// src/main.rs
use std::{
    collections::{HashMap, HashSet},
    env,
    fs,
    path::Path, // <--- 修复点 1：添加此 use 声明
    process,
    rc::Rc,
};
use syn::{
    visit::{self, Visit},
    File, FnArg, Ident, ImplItemFn, ItemFn, Pat, Visibility, ExprUnsafe, Block, Signature,
    punctuated::Punctuated, token, Expr, ExprCall, ExprPath, UnOp, Member, ItemStruct, Fields,
    ExprField, Type,
};
use syn::spanned::Spanned;

// --- 结构体定义 ---

#[derive(Debug, Clone, PartialEq, Eq)]
enum ElementType {
    FunctionParameter,
    StructPublicField,
    ChainedUnsafeCall,
}

#[derive(Debug, Clone)]
struct Finding {
    element_type: ElementType,
    item_name: String,
    element_name: String,
    line: usize,
    unsafe_operation: String,
    context_name: String,
    context_fn_type: String,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
struct StructFieldInfo {
    struct_name: String,
    field_name: String,
}

#[derive(Debug, Clone)]
struct FunctionDefInfo {
    id_key: String,
    name: String,
    struct_name_opt: Option<String>,
    visibility_is_pub: bool,
    is_signature_unsafe: bool,
    params: Vec<Ident>, // 参数 Ident 列表
    params_used_in_own_unsafe_ops: HashSet<String>,
    has_unsafe_block: bool,
    definition_span_start_line: usize,
}

// --- 已知的不安全操作列表 ---
const KNOWN_UNSAFE_FUNCS_OR_METHODS: &[&str] = &[
    "from_raw_parts", "from_utf8_unchecked", "get_unchecked", "get_unchecked_mut",
    "read", "write", "copy", "copy_nonoverlapping", "set_len", "offset",
    "from_raw", "from_ptr",
];

// --- AST 访问和分析逻辑 ---

struct IdentUsageVisitor<'a> {
    target_ident: &'a Ident,
    found: bool,
}
impl<'a, 'ast> Visit<'ast> for IdentUsageVisitor<'a> {
    fn visit_ident(&mut self, i: &'ast Ident) {
        if i == self.target_ident { self.found = true; }
    }
}
fn expr_uses_ident(expr: &Expr, ident: &Ident) -> bool {
    let mut visitor = IdentUsageVisitor { target_ident: ident, found: false };
    visitor.visit_expr(expr);
    visitor.found
}
fn expr_to_simple_ident(expr: &Expr) -> Option<&Ident> {
    if let Expr::Path(ExprPath { path, .. }) = expr { return path.get_ident(); } None
}
fn name_span_line(func_expr: &Expr) -> usize {
    match func_expr {
        Expr::Path(ExprPath { path, .. }) => path.segments.last().map_or_else(|| func_expr.span(), |s| s.ident.span()).start().line,
        Expr::Field(ef) => ef.member.span().start().line,
        _ => func_expr.span().start().line,
    }
}

struct FieldAccessInExprVisitor<'sdata_ref> {
    public_struct_fields: &'sdata_ref HashSet<StructFieldInfo>,
    current_self_type_name: Option<&'sdata_ref str>,
    findings_for_current_expr: Vec<(StructFieldInfo, usize)>,
}
impl<'ast, 'sdata_ref> Visit<'ast> for FieldAccessInExprVisitor<'sdata_ref> {
    fn visit_expr_field(&mut self, expr_field_node: &'ast ExprField) {
        if let Member::Named(field_ident) = &expr_field_node.member {
            let field_name_str = field_ident.to_string();
            let base_is_self = matches!(&*expr_field_node.base, Expr::Path(p) if p.path.get_ident().map_or(false, |id| id == "self"));
            let mut struct_name_if_self: Option<String> = None;
            if base_is_self { struct_name_if_self = self.current_self_type_name.map(String::from); }

            for known_sf_info in self.public_struct_fields.iter() {
                if known_sf_info.field_name == field_name_str {
                    let matches_criteria = if base_is_self {
                        struct_name_if_self.as_ref().map_or(false, |s_name| s_name == &known_sf_info.struct_name)
                    } else { true };
                    if matches_criteria {
                        let line = field_ident.span().start().line;
                        if !self.findings_for_current_expr.iter().any(|(sf, l)| sf == known_sf_info && *l == line) {
                            self.findings_for_current_expr.push((known_sf_info.clone(), line));
                        }
                    }
                }
            }
        }
        visit::visit_expr_field(self, expr_field_node);
    }
}

struct FunctionBodyAnalyzer {
    params: Vec<Ident>,
    params_used_in_unsafe_ops: HashSet<String>,
    has_unsafe_block: bool,
    in_unsafe_block_depth: usize,
}
impl FunctionBodyAnalyzer {
    fn new(params: Vec<Ident>) -> Self {
        Self { params, params_used_in_unsafe_ops: HashSet::new(), has_unsafe_block: false, in_unsafe_block_depth: 0 }
    }
}
impl<'ast> Visit<'ast> for FunctionBodyAnalyzer {
    fn visit_expr_unsafe(&mut self, i: &'ast ExprUnsafe) {
        self.has_unsafe_block = true;
        self.in_unsafe_block_depth += 1;
        visit::visit_expr_unsafe(self, i);
        self.in_unsafe_block_depth -= 1;
    }
    fn visit_expr(&mut self, expr_node: &'ast Expr) {
        if self.in_unsafe_block_depth > 0 {
            match expr_node {
                Expr::Call(expr_call) => {
                    let mut func_name_opt: Option<String> = None;
                    if let Expr::Path(ExprPath { path, .. }) = &*expr_call.func {
                        if let Some(seg) = path.segments.last() { func_name_opt = Some(seg.ident.to_string());}
                    } else if let Expr::Field(ef) = &*expr_call.func {
                        if let Member::Named(ident) = &ef.member { func_name_opt = Some(ident.to_string()); }
                    }
                    if let Some(func_name) = func_name_opt {
                        if KNOWN_UNSAFE_FUNCS_OR_METHODS.contains(&func_name.as_str()) {
                            for arg_expr in &expr_call.args {
                                for p in &self.params {
                                    if expr_uses_ident(arg_expr, p) {
                                        self.params_used_in_unsafe_ops.insert(p.to_string());
                                    }
                                }
                            }
                             if let Expr::Field(ef) = &*expr_call.func { // Check if method call base is a param
                                for p in &self.params {
                                     if expr_uses_ident(&ef.base, p) {
                                         self.params_used_in_unsafe_ops.insert(p.to_string());
                                     }
                                 }
                             }
                        }
                    }
                }
                Expr::Unary(expr_unary) => {
                    if matches!(expr_unary.op, UnOp::Deref(_)) {
                        for p in &self.params {
                            if expr_uses_ident(&expr_unary.expr, p) {
                                self.params_used_in_unsafe_ops.insert(p.to_string());
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        visit::visit_expr(self, expr_node);
    }
}

struct UnsafeUsageVisitor<'scanner_data> {
    param_idents: &'scanner_data HashSet<Ident>,
    is_context_fn_safe_for_p1: bool,
    public_struct_fields: &'scanner_data HashSet<StructFieldInfo>,
    current_self_type_name_for_p2: Option<&'scanner_data str>,
    all_function_defs: &'scanner_data HashMap<String, Rc<FunctionDefInfo>>,
    context_fn_def_for_p3: Option<Rc<FunctionDefInfo>>,
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
                    self.analyze_call_for_p1_p2(expr_call);
                }
                Expr::Unary(expr_unary) => {
                    if let UnOp::Deref(star_token) = expr_unary.op {
                        self.check_element_in_unsafe_expr_for_p1_p2(
                            &expr_unary.expr,
                            star_token.span.start().line,
                            "裸指针解引用".to_string(),
                        );
                    }
                }
                _ => {}
            }
        }
        if let Expr::Call(expr_call) = expr_node {
            self.check_call_for_p3_trigger(expr_call);
        }
        visit::visit_expr(self, expr_node);
    }
}

impl<'sdata> UnsafeUsageVisitor<'sdata> {
    fn add_finding(&mut self, element_type: ElementType, item_name: String, element_name: String, line: usize, operation: String) {
        let already_found = self.findings.iter().any(|f| {
            f.element_type == element_type && f.item_name == item_name && f.element_name == element_name &&
            f.unsafe_operation == operation && f.context_name == self.context_fn_name
        });
        if !already_found {
            self.findings.push(Finding {
                element_type, item_name, element_name, line, unsafe_operation: operation,
                context_name: self.context_fn_name.clone(), context_fn_type: self.context_fn_type.clone(),
            });
        }
    }

    fn check_element_in_unsafe_expr_for_p1_p2(&mut self, expr: &Expr, line_of_unsafe_op: usize, operation_desc: String) {
        if self.is_context_fn_safe_for_p1 {
            for param_ident in self.param_idents.iter() {
                if expr_uses_ident(expr, param_ident) {
                    self.add_finding(ElementType::FunctionParameter, self.context_fn_name.clone(), param_ident.to_string(), line_of_unsafe_op, operation_desc.clone());
                }
            }
        }
        let mut field_visitor = FieldAccessInExprVisitor {
            public_struct_fields: self.public_struct_fields,
            current_self_type_name: self.current_self_type_name_for_p2,
            findings_for_current_expr: Vec::new(),
        };
        field_visitor.visit_expr(expr);
        for (found_field_info, field_access_line) in field_visitor.findings_for_current_expr {
            self.add_finding(ElementType::StructPublicField, found_field_info.struct_name, found_field_info.field_name, field_access_line, operation_desc.clone());
        }
    }

    fn analyze_call_for_p1_p2(&mut self, expr_call: &ExprCall) {
        let mut func_name_str_opt: Option<String> = None;
        let mut call_target_expr: Option<&Expr> = None;

        if let Expr::Path(ExprPath { path, .. }) = &*expr_call.func {
            if let Some(segment) = path.segments.last() { func_name_str_opt = Some(segment.ident.to_string()); }
        } else if let Expr::Field(expr_field) = &*expr_call.func {
            if let Member::Named(ident) = &expr_field.member { func_name_str_opt = Some(ident.to_string()); }
            call_target_expr = Some(&expr_field.base);
        }

        if let Some(func_name) = func_name_str_opt {
            if KNOWN_UNSAFE_FUNCS_OR_METHODS.contains(&func_name.as_str()) {
                let op_desc = format!("调用已知不安全函数/方法 '{}'", func_name);
                let line = name_span_line(&*expr_call.func);
                if let Some(target) = call_target_expr { self.check_element_in_unsafe_expr_for_p1_p2(target, line, op_desc.clone()); }
                for arg_expr in expr_call.args.iter() { self.check_element_in_unsafe_expr_for_p1_p2(arg_expr, line, op_desc.clone());}
            }
        }
    }

    fn check_call_for_p3_trigger(&mut self, expr_call: &ExprCall) {
        // 修复点 2：处理借用冲突
        let caller_def_rc = if let Some(cd_rc) = &self.context_fn_def_for_p3 {
            cd_rc.clone() // Clone the Rc to work with its data without holding a borrow on self.context_fn_def_for_p3
        } else {
            return;
        };
        let caller_def = &*caller_def_rc; // Deref Rc to get &FunctionDefInfo

        if !caller_def.visibility_is_pub || caller_def.is_signature_unsafe { return; }

        let mut callee_name_key: Option<String> = None;
        let mut callee_name_display: Option<String> = None;

        if let Expr::Path(ExprPath { path, .. }) = &*expr_call.func {
            if let Some(segment) = path.segments.last() {
                let name = segment.ident.to_string();
                callee_name_key = Some(name.clone());
                callee_name_display = Some(name);
            }
        } else if let Expr::Field(expr_field) = &*expr_call.func {
            if let Member::Named(method_ident) = &expr_field.member {
                 if let Expr::Path(base_path_expr) = &*expr_field.base {
                     if let Some(base_ident) = base_path_expr.path.get_ident() {
                        let base_name = base_ident.to_string();
                        if base_name == "self" {
                            if let Some(self_type) = self.current_self_type_name_for_p2 {
                                let key = format!("{}::{}", self_type, method_ident);
                                callee_name_key = Some(key.clone());
                                callee_name_display = Some(key);
                            }
                        } else {
                            let key = format!("{}::{}", base_name, method_ident);
                            callee_name_key = Some(key.clone());
                            callee_name_display = Some(key);
                        }
                     }
                 } else {
                    let name = method_ident.to_string();
                    callee_name_key = Some(name.clone());
                    callee_name_display = Some(name);
                 }
            }
        }

        let key = if let Some(k) = callee_name_key { k } else { return; };
        let callee_def = if let Some(cd) = self.all_function_defs.get(&key) { cd } else { return; };
        let display_name = if let Some(dn) = callee_name_display { dn } else { return; };

        if callee_def.visibility_is_pub || callee_def.params_used_in_own_unsafe_ops.is_empty() {
            return;
        }

        // 克隆 caller_def.params 以避免在迭代时与 self.add_finding 冲突
        let caller_params_clone = caller_def.params.clone();

        for (arg_idx, arg_expr) in expr_call.args.iter().enumerate() {
            for caller_param_ident_potential in &caller_params_clone { // 使用克隆的参数列表
                if expr_uses_ident(arg_expr, caller_param_ident_potential) {
                    if arg_idx < callee_def.params.len() {
                        let callee_param_ident = &callee_def.params[arg_idx];
                        if callee_def.params_used_in_own_unsafe_ops.contains(&callee_param_ident.to_string()) {
                            let call_path = format!("{} -> {}", caller_def.name, display_name);
                            self.add_finding( // self.add_finding 是 &mut self
                                ElementType::ChainedUnsafeCall,
                                caller_def.name.clone(),
                                call_path,
                                name_span_line(&*expr_call.func),
                                format!("参数 '{}' (从 '{}') 最终进入 '{}' 的不安全操作 (其参数 '{}')",
                                    caller_param_ident_potential, caller_def.name, display_name, callee_param_ident),
                            );
                        }
                    }
                }
            }
        }
    }
}

struct UnsafeFnParamScanner {
    findings: Vec<Finding>,
    public_struct_fields: HashSet<StructFieldInfo>,
    current_impl_struct_name: Option<String>,
    all_function_defs: HashMap<String, Rc<FunctionDefInfo>>,
}

impl UnsafeFnParamScanner {
    fn new() -> Self { Self { findings: Vec::new(), public_struct_fields: HashSet::new(), current_impl_struct_name: None, all_function_defs: HashMap::new() } }
    fn collect_param_idents<'ast>(inputs: &'ast Punctuated<FnArg, token::Comma>) -> HashSet<Ident> {
        let mut idents = HashSet::new();
        for arg in inputs { if let FnArg::Typed(pt) = arg { Self::extract_idents_from_pat_recursive(&*pt.pat, &mut idents); } }
        idents
    }
    fn extract_idents_from_pat_recursive<'ast>(pat: &'ast Pat, idents: &mut HashSet<Ident>) {
        match pat {
            Pat::Ident(pi) => { if pi.ident.to_string() != "_" { idents.insert(pi.ident.clone()); } }
            Pat::Reference(r) => Self::extract_idents_from_pat_recursive(&r.pat, idents),
            Pat::Tuple(t) => t.elems.iter().for_each(|e| Self::extract_idents_from_pat_recursive(e, idents)),
            Pat::Struct(s) => s.fields.iter().for_each(|f| Self::extract_idents_from_pat_recursive(&f.pat, idents)),
            Pat::TupleStruct(ts) => ts.elems.iter().for_each(|e| Self::extract_idents_from_pat_recursive(e, idents)),
            Pat::Slice(sl) => sl.elems.iter().for_each(|e| Self::extract_idents_from_pat_recursive(e, idents)),
            _ => {}
        }
    }

    fn pre_scan_function_defs(&mut self, file_ast: &File) {
        let mut collector = FunctionDefCollector {
            all_function_defs: &mut self.all_function_defs,
            current_struct_for_impl: None,
        };
        collector.visit_file(file_ast);
    }

    fn process_function_common_for_patterns<'ast>(
        &mut self,
        sig: &'ast Signature,
        block: &'ast Block,
        vis: &Visibility,
        func_name_ident: &Ident,
        func_type_str: &str,
        current_self_type_name_opt: Option<String>,
        func_def_key: &str,
    ) {
        let func_is_pub_and_safe_for_p1 = matches!(vis, Visibility::Public(_)) && sig.unsafety.is_none();
        let param_idents_for_p1: HashSet<Ident> = if func_is_pub_and_safe_for_p1 {
            Self::collect_param_idents(&sig.inputs)
        } else { HashSet::new() };

        if !matches!(vis, Visibility::Public(_)) {
            return;
        }

        let context_fn_def_for_p3 = self.all_function_defs.get(func_def_key).cloned();

        let mut usage_visitor = UnsafeUsageVisitor {
            param_idents: &param_idents_for_p1,
            is_context_fn_safe_for_p1: sig.unsafety.is_none(),
            public_struct_fields: &self.public_struct_fields,
            current_self_type_name_for_p2: current_self_type_name_opt.as_deref(),
            all_function_defs: &self.all_function_defs,
            context_fn_def_for_p3,
            findings: &mut self.findings,
            context_fn_name: func_name_ident.to_string(),
            context_fn_type: func_type_str.to_string(),
            in_unsafe_block_depth: 0,
        };
        usage_visitor.visit_block(block);
    }
}

struct FunctionDefCollector<'a> {
    all_function_defs: &'a mut HashMap<String, Rc<FunctionDefInfo>>,
    current_struct_for_impl: Option<String>,
}

impl<'a, 'ast> Visit<'ast> for FunctionDefCollector<'a> {
    fn visit_item_fn(&mut self, i: &'ast ItemFn) {
        self.collect_fn_info(&i.sig, &i.vis, &i.sig.ident, None, &i.block);
        visit::visit_item_fn(self, i);
    }

    fn visit_item_impl(&mut self, i: &'ast syn::ItemImpl) {
        let mut struct_name: Option<String> = None;
        if let Type::Path(tp) = &*i.self_ty {
            if let Some(seg) = tp.path.segments.last() {
                struct_name = Some(seg.ident.to_string());
            }
        }
        let old_struct_name = self.current_struct_for_impl.take(); // take and store
        self.current_struct_for_impl = struct_name; // set for children
        visit::visit_item_impl(self, i);
        self.current_struct_for_impl = old_struct_name; // restore
    }

    fn visit_impl_item_fn(&mut self, i: &'ast ImplItemFn) {
        // 修复点 3：克隆 self.current_struct_for_impl
        let struct_name_opt_clone = self.current_struct_for_impl.clone();
        self.collect_fn_info(&i.sig, &i.vis, &i.sig.ident, struct_name_opt_clone.as_ref(), &i.block);
        visit::visit_impl_item_fn(self, i);
    }
}

impl<'a> FunctionDefCollector<'a> {
    fn collect_fn_info(&mut self, sig: &Signature, vis: &Visibility, ident: &Ident, struct_name_opt: Option<&String>, block: &Block) {
        let fn_name = ident.to_string();
        let id_key = struct_name_opt.map_or_else(
            || fn_name.clone(),
            |s_name| format!("{}::{}", s_name, fn_name)
        );

        let params_vec: Vec<Ident> = sig.inputs.iter().filter_map(|arg| {
            if let FnArg::Typed(pt) = arg {
                if let Pat::Ident(pat_ident) = &*pt.pat {
                    return Some(pat_ident.ident.clone());
                }
            }
            None
        }).collect();

        let mut body_analyzer = FunctionBodyAnalyzer::new(params_vec.clone());
        body_analyzer.visit_block(block);

        let def_info = Rc::new(FunctionDefInfo {
            id_key: id_key.clone(),
            name: fn_name,
            struct_name_opt: struct_name_opt.cloned(),
            visibility_is_pub: matches!(vis, Visibility::Public(_)),
            is_signature_unsafe: sig.unsafety.is_some(),
            params: params_vec,
            params_used_in_own_unsafe_ops: body_analyzer.params_used_in_unsafe_ops,
            has_unsafe_block: body_analyzer.has_unsafe_block,
            definition_span_start_line: ident.span().start().line,
        });
        // 确保不会因为可变借用和不可变借用冲突而报错
        if !self.all_function_defs.contains_key(&id_key) {
             self.all_function_defs.insert(id_key, def_info);
        } else {
            // Potentially handle redefinitions or provide a warning, though syn usually handles unique items.
            // This might occur if we visit an item multiple times through different paths, though less likely with top-level scans.
        }
    }
}

impl<'ast> Visit<'ast> for UnsafeFnParamScanner {
    fn visit_item_struct(&mut self, i: &'ast ItemStruct) {
        if matches!(i.vis, Visibility::Public(_)) {
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
        }
        visit::visit_item_struct(self, i);
    }

    fn visit_item_impl(&mut self, i: &'ast syn::ItemImpl) {
        let mut impl_struct_name: Option<String> = None;
        if let Type::Path(type_path) = &*i.self_ty {
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
        let key = i.sig.ident.to_string();
        self.process_function_common_for_patterns(
            &i.sig, &i.block, &i.vis, &i.sig.ident, "Function", None, &key
        );
    }

    fn visit_impl_item_fn(&mut self, i: &'ast ImplItemFn) {
         let key = self.current_impl_struct_name.as_ref().map_or_else(
            || i.sig.ident.to_string(),
            |s_name| format!("{}::{}", s_name, i.sig.ident.to_string())
        );
        self.process_function_common_for_patterns(
            &i.sig, &i.block, &i.vis, &i.sig.ident, "Method", self.current_impl_struct_name.clone(), &key
        );
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 { eprintln!("用法: unsafe_param_scanner <rust_file_path>"); process::exit(1); }
    let file_path_str = &args[1];
    let file_path_obj = Path::new(file_path_str);

    if !file_path_obj.exists() || !file_path_obj.is_file() {
        eprintln!("错误: 文件不存在或不是一个有效文件: {}", file_path_str);
        process::exit(1);
    }

    let content = fs::read_to_string(file_path_obj).expect("无法读取文件");
    let ast: File = syn::parse_file(&content).expect("无法解析 Rust 代码");

    let mut scanner = UnsafeFnParamScanner::new();
    scanner.pre_scan_function_defs(&ast);
    scanner.visit_file(&ast);

    if scanner.findings.is_empty() { println!("未发现公共项的元素（参数/字段）被用于已知不安全操作的情况。"); }
    else {
        println!("发现以下情况:");
        let mut p1 = Vec::new(); let mut p2 = Vec::new(); let mut p3 = Vec::new();
        for f_ref in &scanner.findings {
            match f_ref.element_type {
                ElementType::FunctionParameter => p1.push(f_ref.clone()),
                ElementType::StructPublicField => p2.push(f_ref.clone()),
                ElementType::ChainedUnsafeCall => p3.push(f_ref.clone()),
            }
        }
        if !p1.is_empty() { println!("\npattern1 (公共安全函数参数进入其内部不安全操作):"); for f in p1 { println!("- 函数/方法 '{}' (类型: {}): 参数 '{}' 在第 {} 行参与了不安全操作 '{}'。", f.item_name, f.context_fn_type, f.element_name, f.line, f.unsafe_operation); } }
        if !p2.is_empty() { println!("\npattern2 (公共结构体字段进入不安全操作):"); for f in p2 { println!("- 结构体 '{}' 的公共字段 '{}' (在 {} '{}' 上下文中): 在第 {} 行参与了不安全操作 '{}'。", f.item_name, f.element_name, f.context_fn_type, f.context_name, f.line, f.unsafe_operation); } }
        if !p3.is_empty() { println!("\npattern3 (公共安全函数参数通过非公共内部不安全函数进入最终不安全操作):"); for f in p3 { println!("- 调用链 '{}' (始于公共函数/方法 '{}'): 参数最终在第 {} 行参与了不安全操作 '{}' (在 {} '{}' 上下文中)。", f.element_name, f.item_name, f.line, f.unsafe_operation, f.context_fn_type, f.context_name); } }
    }
}