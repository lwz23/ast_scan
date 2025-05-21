// src/main.rs
use std::{
    collections::HashSet,
    env,
    fs,
    path::Path,
    process,
};
use syn::{
    visit::{self, Visit},
    File, FnArg, Ident, ImplItemFn, ItemFn, Pat, Visibility, ExprUnsafe, Block, Signature,
    punctuated::Punctuated, token, Expr, ExprCall, ExprPath, UnOp, Member, ItemStruct, Fields, ExprField,
};
use syn::spanned::Spanned;

// --- 结构体定义 ---

#[derive(Debug, Clone, PartialEq, Eq)]
enum ElementType {
    FunctionParameter,
    StructPublicField,
}

#[derive(Debug, Clone)]
struct Finding {
    element_type: ElementType,
    item_name: String,          // 对于参数：函数/方法名；对于字段：结构体名
    element_name: String,       // 参数名 或 字段名
    line: usize,
    unsafe_operation: String,
    context_name: String,       // 使用此元素（参数/字段）的函数或方法名
    context_fn_type: String,    // "Function" or "Method" (context_name 的类型)
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
struct StructFieldInfo {
    struct_name: String,
    field_name: String,
}

// --- 已知的不安全操作列表 ---
const KNOWN_UNSAFE_FUNCS_OR_METHODS: &[&str] = &[
    "from_raw_parts",
    "from_utf8_unchecked",
    "get_unchecked",
    "get_unchecked_mut",
    "read",
    "write",
    "copy",
    "copy_nonoverlapping",
    "set_len",
    "offset",
    // 以下是根据您的截图添加的
    "from_raw", // 例如 Vec::from_raw, Box::from_raw
    "from_ptr", // 例如 NonNull::from_ptr
];

// --- AST 访问和分析逻辑 ---

struct IdentUsageVisitor<'a> {
    target_ident: &'a Ident,
    found: bool,
}

impl<'a, 'ast> Visit<'ast> for IdentUsageVisitor<'a> {
    fn visit_ident(&mut self, i: &'ast Ident) {
        if i == self.target_ident {
            self.found = true;
        }
    }
}

fn expr_uses_ident(expr: &Expr, ident: &Ident) -> bool {
    let mut visitor = IdentUsageVisitor { target_ident: ident, found: false };
    visitor.visit_expr(expr);
    visitor.found
}

fn expr_to_simple_ident(expr: &Expr) -> Option<&Ident> {
    if let Expr::Path(ExprPath { path, .. }) = expr {
        return path.get_ident();
    }
    None
}

fn name_span_line(func_expr: &Expr) -> usize {
    match func_expr {
        Expr::Path(ExprPath { path, .. }) => {
            if let Some(segment) = path.segments.last() {
                return segment.ident.span().start().line;
            }
        }
        Expr::Field(expr_field) => {
            if let Member::Named(ident) = &expr_field.member {
                return ident.span().start().line;
            }
            return (*expr_field.base).span().start().line;
        }
        _ => {}
    }
    func_expr.span().start().line
}

// 修正：移除未使用的生命周期 'a
struct FieldAccessInExprVisitor<'sdata_ref> {
    public_struct_fields: &'sdata_ref HashSet<StructFieldInfo>,
    current_self_type_name: Option<&'sdata_ref str>,
    findings_for_current_expr: Vec<(StructFieldInfo, usize)>,
}

// 修正：在 impl 中声明 'ast 生命周期
impl<'ast, 'sdata_ref> Visit<'ast> for FieldAccessInExprVisitor<'sdata_ref> {
    fn visit_expr_field(&mut self, expr_field_node: &'ast ExprField) {
        if let Member::Named(field_ident) = &expr_field_node.member {
            let field_name_str = field_ident.to_string();
            let base_is_self = if let Expr::Path(p) = &*expr_field_node.base {
                p.path.get_ident().map_or(false, |id| id == "self")
            } else {
                false
            };

            let mut potential_struct_name_for_self: Option<String> = None;
            if base_is_self {
                potential_struct_name_for_self = self.current_self_type_name.map(|s| s.to_string());
            }

            for known_field_info in self.public_struct_fields.iter() {
                if known_field_info.field_name == field_name_str {
                    let struct_matches = potential_struct_name_for_self.as_ref().map_or_else(
                        || !base_is_self,
                        |self_type_name| self_type_name == &known_field_info.struct_name,
                    );

                    if struct_matches {
                        let field_access_line = field_ident.span().start().line;
                        let already_added = self.findings_for_current_expr.iter().any(|(fi, l)| {
                            fi == known_field_info && *l == field_access_line
                        });
                        if !already_added {
                            self.findings_for_current_expr.push((
                                known_field_info.clone(),
                                field_access_line,
                            ));
                        }
                    }
                }
            }
        }
        visit::visit_expr_field(self, expr_field_node);
    }
}


struct UnsafeUsageVisitor<'scanner_data> {
    param_idents: &'scanner_data HashSet<Ident>,
    is_context_fn_safe: bool,
    public_struct_fields: &'scanner_data HashSet<StructFieldInfo>,
    current_self_type_name: Option<&'scanner_data str>,
    findings: &'scanner_data mut Vec<Finding>,
    context_fn_name: String,
    context_fn_type: String,
    in_unsafe_block_depth: usize,
}

impl<'sdata, 'ast> Visit<'ast> for UnsafeUsageVisitor<'sdata> {
    fn visit_expr_unsafe(&mut self, i: &'ast ExprUnsafe) {
        self.in_unsafe_block_depth += 1;
        visit::visit_expr_unsafe(self, i);
        self.in_unsafe_block_depth -= 1;
    }

    fn visit_expr(&mut self, expr_node: &'ast Expr) {
        if self.in_unsafe_block_depth > 0 {
            match expr_node {
                Expr::Call(expr_call) => {
                    self.check_unsafe_operation_in_call(expr_call);
                }
                Expr::Unary(expr_unary) => {
                    if let UnOp::Deref(star_token) = expr_unary.op {
                        self.check_element_in_unsafe_expr(
                            &expr_unary.expr,
                            star_token.span.start().line,
                            "裸指针解引用".to_string(),
                        );
                    }
                }
                _ => {}
            }
        }
        visit::visit_expr(self, expr_node);
    }
}

impl<'sdata> UnsafeUsageVisitor<'sdata> {
    fn add_finding(
        &mut self,
        element_type: ElementType,
        item_name: String,
        element_name: String,
        line: usize,
        operation: String,
    ) {
        let finding_key = (
            element_type.clone(),
            item_name.clone(),
            element_name.clone(),
            operation.clone(),
            self.context_fn_name.clone(),
        );

        let already_found = self.findings.iter().any(|f| {
            f.element_type == finding_key.0 &&
            f.item_name == finding_key.1 &&
            f.element_name == finding_key.2 &&
            f.unsafe_operation == finding_key.3 &&
            f.context_name == finding_key.4
        });

        if !already_found {
            self.findings.push(Finding {
                element_type,
                item_name,
                element_name,
                line,
                unsafe_operation: operation,
                context_name: self.context_fn_name.clone(),
                context_fn_type: self.context_fn_type.clone(),
            });
        }
    }

    fn check_element_in_unsafe_expr(
        &mut self,
        expr: &Expr,
        line_of_unsafe_op: usize,
        operation_desc: String,
    ) {
        if self.is_context_fn_safe {
            for param_ident in self.param_idents.iter() {
                if expr_uses_ident(expr, param_ident) {
                    self.add_finding(
                        ElementType::FunctionParameter,
                        self.context_fn_name.clone(),
                        param_ident.to_string(),
                        line_of_unsafe_op,
                        operation_desc.clone(),
                    );
                }
            }
        }

        let mut field_visitor = FieldAccessInExprVisitor {
            public_struct_fields: self.public_struct_fields,
            current_self_type_name: self.current_self_type_name,
            findings_for_current_expr: Vec::new(),
        };
        field_visitor.visit_expr(expr);

        for (found_field_info, field_access_line) in field_visitor.findings_for_current_expr {
            self.add_finding(
                ElementType::StructPublicField,
                found_field_info.struct_name,
                found_field_info.field_name,
                field_access_line,
                operation_desc.clone(),
            );
        }
    }

    fn check_unsafe_operation_in_call(&mut self, expr_call: &ExprCall) {
        let mut func_name_str_opt: Option<String> = None;
        let mut call_target_expr_for_field_check: Option<&Expr> = None;

        if let Expr::Path(ExprPath { path, .. }) = &*expr_call.func {
            if let Some(segment) = path.segments.last() {
                func_name_str_opt = Some(segment.ident.to_string());
            }
        } else if let Expr::Field(expr_field) = &*expr_call.func {
            if let Member::Named(ident) = &expr_field.member {
                func_name_str_opt = Some(ident.to_string());
                call_target_expr_for_field_check = Some(&expr_field.base);
            }
        }

        if let Some(func_name) = func_name_str_opt {
            if KNOWN_UNSAFE_FUNCS_OR_METHODS.contains(&func_name.as_str()) {
                let operation_desc = format!("调用不安全函数/方法 '{}'", func_name);
                let line = name_span_line(&*expr_call.func);

                if let Some(target_expr) = call_target_expr_for_field_check {
                    self.check_element_in_unsafe_expr(target_expr, line, operation_desc.clone());
                }

                for arg_expr in expr_call.args.iter() {
                    self.check_element_in_unsafe_expr(arg_expr, line, operation_desc.clone());
                }
            }
        }
    }
}

struct UnsafeFnParamScanner {
    findings: Vec<Finding>,
    public_struct_fields: HashSet<StructFieldInfo>,
    current_impl_struct_name: Option<String>,
}

impl UnsafeFnParamScanner {
    fn new() -> Self {
        Self {
            findings: Vec::new(),
            public_struct_fields: HashSet::new(),
            current_impl_struct_name: None,
        }
    }

    fn collect_param_idents<'ast>(inputs: &'ast Punctuated<FnArg, token::Comma>) -> HashSet<Ident> {
        let mut idents = HashSet::new();
        for arg in inputs {
            if let FnArg::Typed(pat_type) = arg {
                Self::extract_idents_from_pat_recursive(&*pat_type.pat, &mut idents);
            }
        }
        idents
    }

    fn extract_idents_from_pat_recursive<'ast>(pat: &'ast Pat, idents: &mut HashSet<Ident>) {
        match pat {
            Pat::Ident(pat_ident) => {
                if pat_ident.ident.to_string() != "_" {
                    idents.insert(pat_ident.ident.clone());
                }
            }
            Pat::Reference(r) => Self::extract_idents_from_pat_recursive(&r.pat, idents),
            Pat::Tuple(t) => t.elems.iter().for_each(|elem| Self::extract_idents_from_pat_recursive(elem, idents)),
            Pat::Struct(s) => s.fields.iter().for_each(|f| Self::extract_idents_from_pat_recursive(&f.pat, idents)),
            Pat::TupleStruct(ts) => ts.elems.iter().for_each(|elem| Self::extract_idents_from_pat_recursive(elem, idents)),
            Pat::Slice(s) => s.elems.iter().for_each(|elem| Self::extract_idents_from_pat_recursive(elem, idents)),
            _ => {}
        }
    }

    fn process_function_common<'ast>(
        &mut self,
        sig: &'ast Signature,
        block: &'ast Block,
        vis: &Visibility,
        func_name_ident: &Ident,
        func_type_str: &str,
        current_self_type_name_opt: Option<String>,
    ) {
        let func_is_safe_for_pattern1 = matches!(vis, Visibility::Public(_)) && sig.unsafety.is_none();
        let param_idents_for_pattern1: HashSet<Ident> = if func_is_safe_for_pattern1 {
            Self::collect_param_idents(&sig.inputs)
        } else {
            HashSet::new()
        };

        if !matches!(vis, Visibility::Public(_)) {
            return;
        }

        let mut usage_visitor = UnsafeUsageVisitor {
            param_idents: &param_idents_for_pattern1,
            is_context_fn_safe: sig.unsafety.is_none(),
            public_struct_fields: &self.public_struct_fields,
            current_self_type_name: current_self_type_name_opt.as_deref(),
            findings: &mut self.findings,
            context_fn_name: func_name_ident.to_string(),
            context_fn_type: func_type_str.to_string(),
            in_unsafe_block_depth: 0,
        };
        usage_visitor.visit_block(block);
    }
}

impl<'ast> Visit<'ast> for UnsafeFnParamScanner {
    fn visit_item_struct(&mut self, i: &'ast ItemStruct) {
        if !matches!(i.vis, Visibility::Public(_)) {
            visit::visit_item_struct(self, i);
            return;
        }
        let struct_name = i.ident.to_string();
        if let Fields::Named(fields_named) = &i.fields {
            for field in &fields_named.named {
                if let Some(field_ident) = &field.ident {
                    if matches!(field.vis, Visibility::Public(_)) {
                        self.public_struct_fields.insert(StructFieldInfo {
                            struct_name: struct_name.clone(),
                            field_name: field_ident.to_string(),
                        });
                    }
                }
            }
        }
        visit::visit_item_struct(self, i);
    }

    fn visit_item_impl(&mut self, i: &'ast syn::ItemImpl) {
        let mut impl_struct_name: Option<String> = None;
        if let syn::Type::Path(type_path) = &*i.self_ty {
            if let Some(last_segment) = type_path.path.segments.last() {
                impl_struct_name = Some(last_segment.ident.to_string());
            }
        }
        let previous_impl_struct_name = self.current_impl_struct_name.take();
        self.current_impl_struct_name = impl_struct_name;

        visit::visit_item_impl(self, i);

        self.current_impl_struct_name = previous_impl_struct_name;
    }

    fn visit_item_fn(&mut self, i: &'ast ItemFn) {
        self.process_function_common(
            &i.sig,
            &i.block,
            &i.vis,
            &i.sig.ident,
            "Function",
            None,
        );
        visit::visit_item_fn(self, i);
    }

    fn visit_impl_item_fn(&mut self, i: &'ast ImplItemFn) {
        self.process_function_common(
            &i.sig,
            &i.block,
            &i.vis,
            &i.sig.ident,
            "Method",
            self.current_impl_struct_name.clone(),
        );
        visit::visit_impl_item_fn(self, i);
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("用法: unsafe_param_scanner <rust_file_path>");
        process::exit(1);
    }

    let file_path_str = &args[1];
    let file_path = Path::new(file_path_str);

    if !file_path.exists() || !file_path.is_file() {
        eprintln!("错误: 文件不存在或不是一个有效文件: {}", file_path_str);
        process::exit(1);
    }

    let content = match fs::read_to_string(file_path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("读取文件 {} 错误: {}", file_path_str, e);
            process::exit(1);
        }
    };

    let ast: File = match syn::parse_file(&content) {
        Ok(tree) => tree,
        Err(e) => {
            eprintln!("从 {} 解析 Rust 代码错误: {}", file_path_str, e);
            process::exit(1);
        }
    };

    let mut scanner = UnsafeFnParamScanner::new();
    scanner.visit_file(&ast);

    if scanner.findings.is_empty() {
        println!("未发现公共项的元素（参数/字段）被用于已知不安全操作的情况。");
    } else {
        println!("发现以下情况:");

        // 分离 Pattern 1 和 Pattern 2 的结果
        let mut pattern1_findings: Vec<&Finding> = Vec::new();
        let mut pattern2_findings: Vec<&Finding> = Vec::new();
        // let mut pattern3_findings: Vec<&Finding> = Vec::new(); // 为 Pattern 3 预留

        for finding in &scanner.findings {
            match finding.element_type {
                ElementType::FunctionParameter => pattern1_findings.push(finding),
                ElementType::StructPublicField => pattern2_findings.push(finding),
                // ElementType::OtherPattern => pattern3_findings.push(finding), // Pattern 3
            }
        }

        // 输出 Pattern 1
        if !pattern1_findings.is_empty() {
            println!("\npattern1:");
            for finding in pattern1_findings {
                // 使用之前的 FunctionParameter 打印格式
                println!(
                    "- 函数/方法 '{}' (类型: {}): 参数 '{}' 在第 {} 行参与了不安全操作 '{}'。",
                    finding.item_name, // 对于参数，item_name 是其所属函数/方法名
                    finding.context_fn_type,
                    finding.element_name, // 参数名
                    finding.line,
                    finding.unsafe_operation
                );
            }
        }

        // 输出 Pattern 2
        if !pattern2_findings.is_empty() {
            println!("\npattern2:");
            for finding in pattern2_findings {
                // 使用之前的 StructPublicField 打印格式
                println!(
                    "- 结构体 '{}' 的公共字段 '{}' (在 {} '{}' 上下文中): 在第 {} 行参与了不安全操作 '{}'。",
                    finding.item_name, // 结构体名
                    finding.element_name, // 字段名
                    finding.context_fn_type, // 上下文函数/方法的类型 ("Method" or "Function")
                    finding.context_name, // 使用字段的函数/方法名
                    finding.line,
                    finding.unsafe_operation
                );
            }
        }

        // 输出 Pattern 3 (如果实现)
        // if !pattern3_findings.is_empty() {
        //     println!("\npattern3:");
        //     for finding in pattern3_findings {
        //         // ... 对应的打印逻辑 ...
        //     }
        // }
    }
}