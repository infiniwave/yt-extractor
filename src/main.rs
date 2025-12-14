use std::collections::{HashMap, HashSet};

use swc_common::{SourceMap, sync::Lrc};
use swc_ecma_ast::{Callee, Expr, Module, ModuleItem, Stmt};
use swc_ecma_codegen::{Config, Emitter, text_writer::JsWriter};
use swc_ecma_parser::{Lexer, Parser, StringInput, Syntax};
use swc_ecma_visit::{Visit, VisitWith};

// fn match_sig(module: Module)
type Matcher = fn(Box<Expr>) -> Option<Box<Expr>>;
#[derive(Clone, Debug)]
struct Variable {
    assigned_to: Option<Box<Expr>>,
    dependencies: HashSet<String>,
}

struct Analyzer {
    module: Module,
    variables: HashMap<String, Variable>,
    pending_dependents: HashMap<String, HashSet<String>>,
    matchers: Vec<Matcher>,
    matched_vars: Vec<(String, usize, Box<Expr>)>, // (variable name, matcher index, export expression)
}

impl Analyzer {
    fn new(module: Module, matchers: Vec<Matcher>) -> Self {
        Analyzer {
            module,
            variables: Default::default(),
            pending_dependents: Default::default(),
            matchers,
            matched_vars: Vec::new(),
        }
    }

    fn extract_dependencies(&self, expr: &Expr) -> HashSet<String> {
        let mut deps = HashSet::new();
        self.extract_dependencies_recursive(expr, &mut deps);
        deps
    }

    fn extract_dependencies_recursive(&self, expr: &Expr, deps: &mut HashSet<String>) {
        match expr {
            Expr::Ident(ident) => {
                if ident.sym.to_string() == "OoC" {
                    println!("DEBUG: Found dependency on OoC");
                }
                deps.insert(ident.sym.to_string());
            }
            Expr::Member(member) => {
                if let Some(name) = self.member_to_string(&Expr::Member(member.clone())) {
                    deps.insert(name);
                }
                self.extract_dependencies_recursive(&member.obj, deps);
            }
            Expr::Call(call) => {
                if let Callee::Expr(callee) = &call.callee {
                    self.extract_dependencies_recursive(callee, deps);
                }
                for arg in &call.args {
                    self.extract_dependencies_recursive(&arg.expr, deps);
                }
            }
            Expr::New(new_expr) => {
                // Handle new expressions like: new g.WX(...) or new g.bj(...)
                self.extract_dependencies_recursive(&new_expr.callee, deps);
                if let Some(args) = &new_expr.args {
                    for arg in args {
                        self.extract_dependencies_recursive(&arg.expr, deps);
                    }
                }
            }
            Expr::Bin(bin) => {
                self.extract_dependencies_recursive(&bin.left, deps);
                self.extract_dependencies_recursive(&bin.right, deps);
            }
            Expr::Unary(unary) => {
                self.extract_dependencies_recursive(&unary.arg, deps);
            }
            Expr::Cond(cond) => {
                self.extract_dependencies_recursive(&cond.test, deps);
                self.extract_dependencies_recursive(&cond.cons, deps);
                self.extract_dependencies_recursive(&cond.alt, deps);
            }
            Expr::Assign(assign) => {
                self.extract_dependencies_recursive(&assign.right, deps);
            }
            Expr::Seq(seq) => {
                for expr in &seq.exprs {
                    self.extract_dependencies_recursive(expr, deps);
                }
            }
            Expr::Array(array) => {
                for elem in &array.elems {
                    if let Some(elem) = elem {
                        self.extract_dependencies_recursive(&elem.expr, deps);
                    }
                }
            }
            Expr::Object(obj) => {
                for prop in &obj.props {
                    if let swc_ecma_ast::PropOrSpread::Prop(prop) = prop {
                        match &**prop {
                            swc_ecma_ast::Prop::KeyValue(kv) => {
                                self.extract_dependencies_recursive(&kv.value, deps);
                            }
                            swc_ecma_ast::Prop::Method(method) => {
                                if let Some(body) = &method.function.body {
                                    for stmt in &body.stmts {
                                        self.extract_stmt_dependencies(stmt, deps);
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            Expr::Fn(func) => {
                if let Some(body) = &func.function.body {
                    for stmt in &body.stmts {
                        self.extract_stmt_dependencies(stmt, deps);
                    }
                }
            }
            Expr::Arrow(arrow) => match &*arrow.body {
                swc_ecma_ast::BlockStmtOrExpr::BlockStmt(block) => {
                    for stmt in &block.stmts {
                        self.extract_stmt_dependencies(stmt, deps);
                    }
                }
                swc_ecma_ast::BlockStmtOrExpr::Expr(expr) => {
                    self.extract_dependencies_recursive(expr, deps);
                }
            },
            Expr::Paren(paren) => {
                self.extract_dependencies_recursive(&paren.expr, deps);
            }
            _ => {}
        }
    }

    fn extract_stmt_dependencies(&self, stmt: &Stmt, deps: &mut HashSet<String>) {
        match stmt {
            Stmt::Expr(expr_stmt) => {
                self.extract_dependencies_recursive(&expr_stmt.expr, deps);
            }
            Stmt::Return(ret) => {
                if let Some(arg) = &ret.arg {
                    self.extract_dependencies_recursive(arg, deps);
                }
            }
            Stmt::If(if_stmt) => {
                self.extract_dependencies_recursive(&if_stmt.test, deps);
                self.extract_stmt_dependencies(&if_stmt.cons, deps);
                if let Some(alt) = &if_stmt.alt {
                    self.extract_stmt_dependencies(alt, deps);
                }
            }
            Stmt::Block(block) => {
                for stmt in &block.stmts {
                    self.extract_stmt_dependencies(stmt, deps);
                }
            }
            Stmt::Labeled(labeled) => {
                self.extract_stmt_dependencies(&labeled.body, deps);
            }
            Stmt::Decl(decl) => match decl {
                swc_ecma_ast::Decl::Var(var_decl) => {
                    for decl in &var_decl.decls {
                        if let Some(init) = &decl.init {
                            println!(
                                "DEBUG: Extracting dependencies from var decl init: {:?}",
                                init
                            );
                            self.extract_dependencies_recursive(init, deps);
                        }
                    }
                }
                _ => {}
            },
            _ => {
                println!(
                    "DEBUG: Unhandled statement in dependency extraction: {:?}",
                    stmt
                );
            }
        }
    }

    fn member_to_string(&self, expr: &Expr) -> Option<String> {
        match expr {
            Expr::Member(member) => {
                let obj_str = self.member_to_string(&member.obj)?;
                match &member.prop {
                    swc_ecma_ast::MemberProp::Ident(ident) => {
                        Some(format!("{}.{}", obj_str, ident.sym))
                    }
                    swc_ecma_ast::MemberProp::Computed(computed) => {
                        if let Expr::Lit(swc_ecma_ast::Lit::Str(s)) = &*computed.expr {
                            if let Some(prop_name) = s.value.as_str() {
                                Some(format!("{}.{}", obj_str, prop_name))
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
            }
            Expr::Ident(ident) => Some(ident.sym.to_string()),
            Expr::This(_) => Some("this".to_string()),
            _ => None,
        }
    }

    fn member_base_name(&self, expr: &Expr) -> Option<String> {
        match expr {
            Expr::Member(member) => self.member_base_name(&member.obj),
            Expr::Ident(ident) => Some(ident.sym.to_string()),
            Expr::This(_) => Some("this".to_string()),
            _ => None,
        }
    }

    fn matches(&self, var: &Variable) -> Option<(usize, Box<Expr>)> {
        for (idx, matcher) in self.matchers.iter().enumerate() {
            if let Some(export_expr) = matcher(
                var.assigned_to
                    .clone()
                    .expect("should have checked already"),
            ) {
                return Some((idx, export_expr));
            }
        }
        None
    }

    fn assign_target_to_expr(&self, target: &swc_ecma_ast::AssignTarget) -> Option<Expr> {
        match target {
            swc_ecma_ast::AssignTarget::Simple(simple) => match simple {
                swc_ecma_ast::SimpleAssignTarget::Ident(ident) => {
                    Some(Expr::Ident(ident.id.clone()))
                }
                swc_ecma_ast::SimpleAssignTarget::Member(member) => {
                    Some(Expr::Member(member.clone()))
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn collect_all_dependencies(&self, var_name: &str, collected: &mut HashSet<String>) {
        if collected.contains(var_name) {
            return;
        }
        collected.insert(var_name.to_string());

        if let Some(var) = self.variables.get(var_name) {
            for dep in &var.dependencies {
                // Recursively collect all dependencies, including member expressions like g.bj
                // but excluding member expressions if the current var is a member expression
                if !var_name.contains('.') || !dep.contains('.') {
                    self.collect_all_dependencies(dep, collected);
                }
            }
        }
    }

    fn topological_sort(&self, vars: &HashSet<String>) -> Vec<String> {
        let mut sorted = Vec::new();
        let mut visited = HashSet::new();
        let mut visiting = HashSet::new();

        fn visit(
            analyzer: &Analyzer,
            var_name: &str,
            vars: &HashSet<String>,
            visited: &mut HashSet<String>,
            visiting: &mut HashSet<String>,
            sorted: &mut Vec<String>,
        ) {
            if visited.contains(var_name) {
                return;
            }
            if visiting.contains(var_name) {
                // Circular dependency, skip
                return;
            }

            visiting.insert(var_name.to_string());

            // Visit dependencies first
            if let Some(var) = analyzer.variables.get(var_name) {
                for dep in &var.dependencies {
                    if vars.contains(dep) {
                        visit(analyzer, dep, vars, visited, visiting, sorted);
                    }
                }
            }

            visiting.remove(var_name);
            visited.insert(var_name.to_string());
            sorted.push(var_name.to_string());
        }

        // Visit all variables
        for var_name in vars {
            visit(
                self,
                var_name,
                vars,
                &mut visited,
                &mut visiting,
                &mut sorted,
            );
        }

        sorted
    }

    fn render_to_js(&self, cm: &Lrc<SourceMap>) -> Result<String, Box<dyn std::error::Error>> {
        // Collect all variables we need to render
        let mut all_vars = HashSet::new();
        for (matched, matcher_idx, export_expr) in &self.matched_vars {
            // Only collect dependencies if the export expression is not a literal value
            // For literals (like timestamp = 20430), we don't need any dependencies
            let is_literal = matches!(
                **export_expr,
                Expr::Lit(_) | Expr::Ident(_) // Simple identifiers like VyG don't need their variable definition's deps
            );

            if !is_literal || *matcher_idx == 1 {
                // nsigFn needs VyG's dependencies
                self.collect_all_dependencies(matched, &mut all_vars);
            }
        }

        println!("Variables to render: {:?}", all_vars);

        // Sort variables topologically so dependencies come before dependents
        let sorted_vars = self.topological_sort(&all_vars);

        // Map matcher index to function name and export expression
        let function_names = ["sigFn", "nsigFn", "timestamp"];
        let mut matched_exports: HashMap<usize, Box<Expr>> = HashMap::new();

        for (_, matcher_idx, export_expr) in &self.matched_vars {
            matched_exports.insert(*matcher_idx, export_expr.clone());
        }

        // Create a new module with just the variables we need
        let mut stmts = Vec::new();

        for var_name in &sorted_vars {
            if let Some(var) = self.variables.get(var_name) {
                if let Some(expr) = &var.assigned_to {
                    // Check if this is a member expression (like g.bj)
                    if var_name.contains('.') {
                        // For member expressions, create an assignment expression
                        let parts: Vec<&str> = var_name.split('.').collect();
                        if parts.len() >= 2 {
                            // Build the member expression from parts
                            let mut member_expr: Box<Expr> =
                                Box::new(Expr::Ident(swc_ecma_ast::Ident::new(
                                    parts[0].into(),
                                    swc_common::DUMMY_SP,
                                    Default::default(),
                                )));

                            for i in 1..parts.len() {
                                member_expr = Box::new(Expr::Member(swc_ecma_ast::MemberExpr {
                                    span: swc_common::DUMMY_SP,
                                    obj: member_expr,
                                    prop: swc_ecma_ast::MemberProp::Ident(
                                        swc_ecma_ast::IdentName::new(
                                            parts[i].into(),
                                            swc_common::DUMMY_SP,
                                        ),
                                    ),
                                }));
                            }

                            let assign_stmt = swc_ecma_ast::Stmt::Expr(swc_ecma_ast::ExprStmt {
                                span: swc_common::DUMMY_SP,
                                expr: Box::new(Expr::Assign(swc_ecma_ast::AssignExpr {
                                    span: swc_common::DUMMY_SP,
                                    op: swc_ecma_ast::AssignOp::Assign,
                                    left: swc_ecma_ast::AssignTarget::Simple(
                                        swc_ecma_ast::SimpleAssignTarget::Member(
                                            match *member_expr {
                                                Expr::Member(m) => m,
                                                _ => continue,
                                            },
                                        ),
                                    ),
                                    right: expr.clone(),
                                })),
                            });
                            stmts.push(assign_stmt);
                        }
                    } else {
                        // For regular variables, create a variable declaration
                        let var_decl = swc_ecma_ast::Stmt::Decl(swc_ecma_ast::Decl::Var(Box::new(
                            swc_ecma_ast::VarDecl {
                                span: swc_common::DUMMY_SP,
                                kind: swc_ecma_ast::VarDeclKind::Var,
                                declare: false,
                                decls: vec![swc_ecma_ast::VarDeclarator {
                                    span: swc_common::DUMMY_SP,
                                    name: swc_ecma_ast::Pat::Ident(swc_ecma_ast::BindingIdent {
                                        id: swc_ecma_ast::Ident::new(
                                            var_name.clone().into(),
                                            swc_common::DUMMY_SP,
                                            Default::default(),
                                        ),
                                        type_ann: None,
                                    }),
                                    init: Some(expr.clone()),
                                    definite: false,
                                }],
                                ctxt: Default::default(),
                            },
                        )));
                        stmts.push(var_decl);
                    }
                }
            }
        }

        // Add return statement with object containing the three functions
        let mut return_props = Vec::new();
        for (matcher_idx, fn_name) in function_names.iter().enumerate() {
            if let Some(export_expr) = matched_exports.get(&matcher_idx) {
                // Wrap sigFn and nsigFn in arrow functions that take a parameter
                let value = if matcher_idx == 0 || matcher_idx == 1 {
                    // Create arrow function: (param) => exportExpr(param) or (param) => exportExpr
                    let param_name = if matcher_idx == 0 { "O" } else { "m" }; // Use common param names

                    // For sigFn, we need to wrap YU(1, decodeURIComponent(O)) call with param
                    // For nsigFn, we need to call VyG(param)
                    let call_expr = if matcher_idx == 0 {
                        // For sigFn: YU(1, decodeURIComponent(param))
                        if let Expr::Call(call) = &**export_expr {
                            // Replace the second argument with decodeURIComponent(param)
                            let mut new_args = call.args.clone();
                            if new_args.len() >= 2 {
                                new_args[1] = swc_ecma_ast::ExprOrSpread {
                                    spread: None,
                                    expr: Box::new(Expr::Call(swc_ecma_ast::CallExpr {
                                        span: swc_common::DUMMY_SP,
                                        ctxt: Default::default(),
                                        callee: swc_ecma_ast::Callee::Expr(Box::new(Expr::Ident(
                                            swc_ecma_ast::Ident::new(
                                                "decodeURIComponent".into(),
                                                swc_common::DUMMY_SP,
                                                Default::default(),
                                            ),
                                        ))),
                                        args: vec![swc_ecma_ast::ExprOrSpread {
                                            spread: None,
                                            expr: Box::new(Expr::Ident(swc_ecma_ast::Ident::new(
                                                param_name.into(),
                                                swc_common::DUMMY_SP,
                                                Default::default(),
                                            ))),
                                        }],
                                        type_args: None,
                                    })),
                                };
                            }
                            Box::new(Expr::Call(swc_ecma_ast::CallExpr {
                                span: call.span,
                                ctxt: call.ctxt,
                                callee: call.callee.clone(),
                                args: new_args,
                                type_args: call.type_args.clone(),
                            }))
                        } else {
                            export_expr.clone()
                        }
                    } else {
                        // For nsigFn: VyG(param)
                        if let Expr::Ident(ident) = &**export_expr {
                            Box::new(Expr::Call(swc_ecma_ast::CallExpr {
                                span: swc_common::DUMMY_SP,
                                ctxt: Default::default(),
                                callee: swc_ecma_ast::Callee::Expr(Box::new(Expr::Ident(
                                    ident.clone(),
                                ))),
                                args: vec![swc_ecma_ast::ExprOrSpread {
                                    spread: None,
                                    expr: Box::new(Expr::Ident(swc_ecma_ast::Ident::new(
                                        param_name.into(),
                                        swc_common::DUMMY_SP,
                                        Default::default(),
                                    ))),
                                }],
                                type_args: None,
                            }))
                        } else {
                            export_expr.clone()
                        }
                    };

                    Box::new(Expr::Arrow(swc_ecma_ast::ArrowExpr {
                        span: swc_common::DUMMY_SP,
                        ctxt: Default::default(),
                        params: vec![swc_ecma_ast::Pat::Ident(swc_ecma_ast::BindingIdent {
                            id: swc_ecma_ast::Ident::new(
                                param_name.into(),
                                swc_common::DUMMY_SP,
                                Default::default(),
                            ),
                            type_ann: None,
                        })],
                        body: Box::new(swc_ecma_ast::BlockStmtOrExpr::Expr(call_expr)),
                        is_async: false,
                        is_generator: false,
                        type_params: None,
                        return_type: None,
                    }))
                } else {
                    // For timestamp, just use the value directly
                    export_expr.clone()
                };

                let prop = swc_ecma_ast::PropOrSpread::Prop(Box::new(
                    swc_ecma_ast::Prop::KeyValue(swc_ecma_ast::KeyValueProp {
                        key: swc_ecma_ast::PropName::Ident(swc_ecma_ast::IdentName::new(
                            fn_name.to_string().into(),
                            swc_common::DUMMY_SP,
                        )),
                        value,
                    }),
                ));
                return_props.push(prop);
            }
        }

        let return_stmt = swc_ecma_ast::Stmt::Return(swc_ecma_ast::ReturnStmt {
            span: swc_common::DUMMY_SP,
            arg: Some(Box::new(Expr::Object(swc_ecma_ast::ObjectLit {
                span: swc_common::DUMMY_SP,
                props: return_props,
            }))),
        });
        stmts.push(return_stmt);

        // Wrap everything in an IIFE that takes 'g' as a parameter
        let func = swc_ecma_ast::Function {
            params: vec![swc_ecma_ast::Param {
                span: swc_common::DUMMY_SP,
                decorators: vec![],
                pat: swc_ecma_ast::Pat::Ident(swc_ecma_ast::BindingIdent {
                    id: swc_ecma_ast::Ident::new(
                        "g".into(),
                        swc_common::DUMMY_SP,
                        Default::default(),
                    ),
                    type_ann: None,
                }),
            }],
            decorators: vec![],
            span: swc_common::DUMMY_SP,
            ctxt: Default::default(),
            body: Some(swc_ecma_ast::BlockStmt {
                span: swc_common::DUMMY_SP,
                stmts,
                ctxt: Default::default(),
            }),
            is_generator: false,
            is_async: false,
            type_params: None,
            return_type: None,
        };

        let iife_call = swc_ecma_ast::Stmt::Expr(swc_ecma_ast::ExprStmt {
            span: swc_common::DUMMY_SP,
            expr: Box::new(Expr::Call(swc_ecma_ast::CallExpr {
                span: swc_common::DUMMY_SP,
                ctxt: Default::default(),
                callee: swc_ecma_ast::Callee::Expr(Box::new(Expr::Paren(
                    swc_ecma_ast::ParenExpr {
                        span: swc_common::DUMMY_SP,
                        expr: Box::new(Expr::Fn(swc_ecma_ast::FnExpr {
                            ident: None,
                            function: Box::new(func),
                        })),
                    },
                ))),
                args: vec![swc_ecma_ast::ExprOrSpread {
                    spread: None,
                    expr: Box::new(Expr::Object(swc_ecma_ast::ObjectLit {
                        span: swc_common::DUMMY_SP,
                        props: vec![],
                    })),
                }],
                type_args: None,
            })),
        });

        let output_module = Module {
            span: swc_common::DUMMY_SP,
            body: vec![ModuleItem::Stmt(iife_call)],
            shebang: None,
        };

        // Generate JavaScript code
        let mut buf = vec![];
        {
            let mut emitter = Emitter {
                cfg: Config::default(),
                cm: cm.clone(),
                comments: None,
                wr: JsWriter::new(cm.clone(), "\n", &mut buf, None),
            };
            emitter.emit_module(&output_module)?;
        }

        Ok(String::from_utf8(buf)?)
    }

    fn walk_ast(&mut self) {
        // 1. Find the IIFE
        let iife = self.module.body.iter().filter_map(|s| s.clone().stmt())
            .find(|s| matches!(s, swc_ecma_ast::Stmt::Expr(expr) if matches!(&*expr.expr, swc_ecma_ast::Expr::Call(call) if matches!(&call.callee, Callee::Expr(_)))))
            .map(|s| match s {
                swc_ecma_ast::Stmt::Expr(expr) => expr,
                _ => unreachable!(),
            })
            .map(|expr| match &*expr.expr {
                swc_ecma_ast::Expr::Call(call) => call.clone(),
                _ => unreachable!(),
            })
            .map(|expr| match &expr.callee {
                swc_ecma_ast::Callee::Expr(expr) => expr.clone(),
                _ => unreachable!(),
            })
            .map(|expr| match &*expr {
                swc_ecma_ast::Expr::Paren(func) => func.clone(),
                _ => unreachable!()
            })
            .map(|expr| match &*expr.expr {
                swc_ecma_ast::Expr::Fn(func) => func.clone(),
                _ => unreachable!()
            })
            .expect("IIFE not found");
        // println!("Found IIFE: {:?}", iife);

        // 2. Inside the IIFE, keep track of variable assignments
        match iife.function.body {
            Some(ref body) => {
                for stmt in &body.stmts {
                    // Process each statement to track variable assignments
                    match stmt {
                        Stmt::Expr(stmt) => {
                            match stmt.expr.as_ref() {
                                Expr::Assign(assign) => {
                                    // Handle variable assignment
                                    if let Some(name) =
                                        assign.left.as_ident().map(|id| id.sym.to_string())
                                    {
                                        let assigned_expr = assign.right.clone();
                                        if self.variables.contains_key(&name) {
                                            let deps = self.extract_dependencies(&assign.right);

                                            let var = self.variables.get_mut(&name).unwrap();
                                            var.assigned_to = Some(assigned_expr);
                                            var.dependencies.extend(deps);
                                            // println!("Variable assigned: {}", name);
                                            let var = self.variables.get(&name).unwrap();
                                            let matches = self.matches(var);
                                            if let Some((matcher_idx, export_expr)) = matches {
                                                println!("Match found for variable: {}", name);
                                                self.matched_vars.push((
                                                    name.clone(),
                                                    matcher_idx,
                                                    export_expr,
                                                ));
                                                // return;
                                            }
                                        }
                                    }
                                    // Handle member expression assignment
                                    if let Some(left_expr) =
                                        self.assign_target_to_expr(&assign.left)
                                    {
                                        if let Some(name) = self.member_to_string(&left_expr) {
                                            let deps = self.extract_dependencies(&assign.right);
                                            if let Some(var) = self.variables.get_mut(&name) {
                                                var.assigned_to = Some(assign.right.clone());
                                                var.dependencies.extend(deps.clone());
                                            }
                                            // println!("Member assigned: {}", name);
                                            let base = self.member_base_name(&left_expr);
                                            if let Some(base_name) = base {
                                                if base_name != name
                                                    && !base_name.starts_with("this.")
                                                {
                                                    if let Some(var) = self.variables.get_mut(&name)
                                                    {
                                                        var.dependencies.insert(
                                                            base_name.replace(".prototype", ""),
                                                        );
                                                    }
                                                }
                                            }
                                            if self.pending_dependents.contains_key(&name) {
                                                self.pending_dependents.remove(&name);
                                            }
                                            self.variables.insert(
                                                name.clone(),
                                                Variable {
                                                    assigned_to: Some(assign.right.clone()),
                                                    dependencies: deps,
                                                },
                                            );
                                        }
                                    }
                                }
                                _ => {
                                    // Ignore
                                }
                            }
                        }
                        Stmt::Decl(decl) => {
                            match decl {
                                swc_ecma_ast::Decl::Var(var_decl) => {
                                    for decl in &var_decl.decls {
                                        if let Some(name) =
                                            decl.name.as_ident().map(|id| id.sym.to_string())
                                        {
                                            let deps =
                                                decl.init.as_ref().map_or(HashSet::new(), |init| {
                                                    self.extract_dependencies(init)
                                                });
                                            let mut var = Variable {
                                                assigned_to: decl.init.clone(),
                                                dependencies: deps,
                                            };
                                            // Check for pending dependents
                                            if let Some(_dependents) =
                                                self.pending_dependents.remove(&name)
                                            {
                                                var.dependencies.insert(name.clone());
                                            }
                                            self.variables.insert(name.clone(), var.clone());
                                            if var.assigned_to.is_some() {
                                                let matches = self.matches(&var);
                                                if let Some((matcher_idx, export_expr)) = matches {
                                                    println!("Match found in IIFE body: {}", name);
                                                    self.matched_vars.push((
                                                        name.clone(),
                                                        matcher_idx,
                                                        export_expr,
                                                    ));
                                                    // return;
                                                }
                                            }
                                        }
                                    }
                                }
                                _ => {
                                    // Ignore other declarations
                                }
                            }
                        }
                        _ => {
                            // Ignore other statements
                        }
                    }
                }
            }
            None => {
                println!("IIFE has no body");
            }
        }
    }
}

struct TimestampVisitor {
    found: Option<Box<Expr>>,
}
impl Visit for TimestampVisitor {
    fn visit_object_lit(&mut self, node: &swc_ecma_ast::ObjectLit) {
        for prop in &node.props {
            if let swc_ecma_ast::PropOrSpread::Prop(prop) = prop {
                match &**prop {
                    swc_ecma_ast::Prop::KeyValue(kv) => {
                        // println!("Visiting ObjectLit: {:?}", node);
                        if let swc_ecma_ast::PropName::Ident(key) = &kv.key {
                            if key.sym.to_string() == "signatureTimestamp" {
                                println!("Found signatureTimestamp: {:?}", kv.value);
                                self.found = Some(kv.value.clone());
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
}
impl TimestampVisitor {
    fn found(&self) -> Option<Box<Expr>> {
        self.found.clone()
    }
    fn new() -> Self {
        TimestampVisitor { found: None }
    }
}

fn main() {
    // read the file "ab89db3f.js"
    let cm: Lrc<SourceMap> = Default::default();
    let fm = cm
        .load_file(std::path::Path::new("ab89db3f.js"))
        .expect("failed to load file");
    println!("File loaded: {:?}", fm);

    let lexer = Lexer::new(
        Syntax::Es(Default::default()),
        Default::default(),
        StringInput::from(&*fm),
        None,
    );
    let mut parser = Parser::new_from(lexer);
    let module = parser.parse_module().expect("failed to parse module");
    // println!("Parsed module: {:?}", module);
    let mut analyzer = Analyzer::new(
        module,
        vec![
            // matcher for sig function
            |expr| {
                // 1. Check if expr is a var declaration
                if let Expr::Fn(fun) = *expr // var a = function() { ... }
            && fun.function.params.len() == 3
                // var a = function(x, y, z) { ... }
                {
                    // println!("Found function with 3 params");
                    let param3 = &fun.function.params[2];
                    if let swc_ecma_ast::Pat::Ident(ident) = &param3.pat {
                        let _id = ident.id.sym.to_string();
                        // println!("Found function with third param: {}", id);
                        if let Some(body) = &fun.function.body {
                            for stmt in &body.stmts {
                                // println!("Checking statement: {:?}", stmt);
                                if let Stmt::Expr(expr) = stmt
                                    && let Expr::Bin(bin) = &*expr.expr
                                    && bin.op == swc_ecma_ast::BinaryOp::LogicalAnd
                                    && let Expr::Paren(expr) = bin.right.as_ref()
                                    && let Expr::Seq(expr) = &*expr.expr
                                    && let Some(first) = expr.exprs.get(0)
                                    && let Expr::Assign(assign) = first.as_ref()
                                    && let Expr::Call(call) = &*assign.right
                                {
                                    // println!("Found assignment with call expression : {:?}", call);
                                    let arg = call.args.iter().find(|arg| {
                                        if let Expr::Call(call) = &*arg.expr {
                                            if let Callee::Expr(callee_expr) = &call.callee {
                                                if let Expr::Ident(ident) = &**callee_expr {
                                                    return ident.sym.to_string()
                                                        == "decodeURIComponent";
                                                }
                                            }
                                        }
                                        false
                                    });
                                    if arg.is_some() {
                                        println!("Found call to decodeURIComponent");
                                        // Return the call expression (YU(...)) instead of the assignment
                                        if let Callee::Expr(callee) = &call.callee {
                                            if let Expr::Ident(_ident) = &**callee {
                                                return Some(Box::new(Expr::Call(call.clone())));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                None
            },
            // matcher for nsig function
            |expr| {
                if let Expr::Array(array) = *expr
                    && let Some(first) = array.elems.get(0)
                    && let Some(first_expr) = first
                    && let Expr::Ident(ident) = &*first_expr.expr
                {
                    println!("Found nsig first element ident: {}", ident.sym);
                    return Some(first_expr.expr.clone());
                }
                None
            },
            // matcher for timestamp
            |expr| {
                if let Expr::Fn(fun) = *expr {
                    let mut visitor = TimestampVisitor::new();
                    fun.visit_children_with(&mut visitor);
                    // Return the value of signatureTimestamp, not the whole function
                    visitor.found()
                } else {
                    None
                }
            },
        ],
    );
    analyzer.walk_ast();

    // Render the matched functions and their dependencies to JavaScript
    match analyzer.render_to_js(&cm) {
        Ok(js_code) => {
            println!("\n=== Generated JavaScript ===\n");
            println!("{}", js_code);

            // Write to output file
            std::fs::write("output_functions.js", &js_code).expect("Failed to write output file");
            println!("\nOutput written to output_functions.js");
        }
        Err(e) => {
            eprintln!("Error generating JavaScript: {}", e);
        }
    }
}
