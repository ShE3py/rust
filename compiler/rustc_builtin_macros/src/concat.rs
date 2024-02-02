use rustc_ast as ast;
use rustc_ast::tokenstream::TokenStream;
use rustc_expand::base::{self, DummyResult};
use rustc_session::errors::report_lit_error;
use rustc_span::symbol::Symbol;

use crate::errors;

pub fn expand_concat(
    cx: &mut base::ExtCtxt<'_>,
    sp: rustc_span::Span,
    tts: TokenStream,
) -> Box<dyn base::MacResult + 'static> {
    let es = match base::get_exprs_from_tts(cx, tts) {
        Ok(es) => es,
        Err(guar) => return DummyResult::any(sp, guar),
    };
    let mut accumulator = String::new();
    let mut missing_literal = vec![];
    let mut result = Ok(());
    for e in es {
        match e.kind {
            ast::ExprKind::Lit(token_lit) => match ast::LitKind::from_token_lit(token_lit) {
                Ok(ast::LitKind::Str(s, _) | ast::LitKind::Float(s, _)) => {
                    accumulator.push_str(s.as_str());
                }
                Ok(ast::LitKind::Char(c)) => {
                    accumulator.push(c);
                }
                Ok(ast::LitKind::Int(i, _)) => {
                    accumulator.push_str(&i.to_string());
                }
                Ok(ast::LitKind::Bool(b)) => {
                    accumulator.push_str(&b.to_string());
                }
                Ok(ast::LitKind::CStr(..)) => {
                    let guar = cx.dcx().emit_err(errors::ConcatCStrLit { span: e.span });
                    result = Err(guar);
                }
                Ok(ast::LitKind::Byte(..) | ast::LitKind::ByteStr(..)) => {
                    let guar = cx.dcx().emit_err(errors::ConcatBytestr { span: e.span });
                    result = Err(guar);
                }
                Ok(ast::LitKind::Err) => {
                    result = Err(cx.dcx().span_delayed_bug(e.span, "concatenating `LitKind::Err`"));
                }
                Err(err) => {
                    let guar = report_lit_error(&cx.sess.parse_sess, err, token_lit, e.span);
                    result = Err(guar);
                }
            },
            // We also want to allow negative numeric literals.
            ast::ExprKind::Unary(ast::UnOp::Neg, ref expr)
                if let ast::ExprKind::Lit(token_lit) = expr.kind =>
            {
                match ast::LitKind::from_token_lit(token_lit) {
                    Ok(ast::LitKind::Int(i, _)) => accumulator.push_str(&format!("-{i}")),
                    Ok(ast::LitKind::Float(f, _)) => accumulator.push_str(&format!("-{f}")),
                    Err(err) => {
                        let guar = report_lit_error(&cx.sess.parse_sess, err, token_lit, e.span);
                        result = Err(guar);
                    }
                    _ => missing_literal.push(e.span),
                }
            }
            ast::ExprKind::IncludedBytes(..) => {
                cx.dcx().emit_err(errors::ConcatBytestr { span: e.span });
            }
            ast::ExprKind::Err(guar) => {
                result = Err(guar);
            }
            ast::ExprKind::Dummy => cx.dcx().span_bug(e.span, "concatenating `ExprKind::Dummy`"),
            _ => {
                missing_literal.push(e.span);
            }
        }
    }

    if !missing_literal.is_empty() {
        let guar = cx.dcx().emit_err(errors::ConcatMissingLiteral { spans: missing_literal });
        return DummyResult::any(sp, guar);
    } else if let Err(guar) = result {
        return DummyResult::any(sp, guar);
    }
    let sp = cx.with_def_site_ctxt(sp);
    base::MacEager::expr(cx.expr_str(sp, Symbol::intern(&accumulator)))
}
