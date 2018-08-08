#![allow(bad_style, missing_docs, unreachable_pub)]
#![cfg_attr(rustfmt, rustfmt_skip)]
use super::SyntaxInfo;

/// The kind of syntax node, e.g. `IDENT`, `USE_KW`, or `STRUCT_DEF`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SyntaxKind {
    SEMI,
    COMMA,
    L_PAREN,
    R_PAREN,
    L_CURLY,
    R_CURLY,
    L_BRACK,
    R_BRACK,
    L_ANGLE,
    R_ANGLE,
    AT,
    POUND,
    TILDE,
    QUESTION,
    DOLLAR,
    AMP,
    PIPE,
    PLUS,
    STAR,
    SLASH,
    CARET,
    PERCENT,
    DOT,
    DOTDOT,
    DOTDOTDOT,
    DOTDOTEQ,
    COLON,
    COLONCOLON,
    EQ,
    EQEQ,
    FAT_ARROW,
    EXCL,
    NEQ,
    MINUS,
    THIN_ARROW,
    LTEQ,
    GTEQ,
    PLUSEQ,
    MINUSEQ,
    AMPAMP,
    PIPEPIPE,
    SHL,
    SHR,
    SHLEQ,
    SHREQ,
    USE_KW,
    FN_KW,
    STRUCT_KW,
    ENUM_KW,
    TRAIT_KW,
    IMPL_KW,
    TRUE_KW,
    FALSE_KW,
    AS_KW,
    EXTERN_KW,
    CRATE_KW,
    MOD_KW,
    PUB_KW,
    SELF_KW,
    SUPER_KW,
    IN_KW,
    WHERE_KW,
    FOR_KW,
    LOOP_KW,
    WHILE_KW,
    IF_KW,
    ELSE_KW,
    MATCH_KW,
    CONST_KW,
    STATIC_KW,
    MUT_KW,
    UNSAFE_KW,
    TYPE_KW,
    REF_KW,
    LET_KW,
    MOVE_KW,
    RETURN_KW,
    AUTO_KW,
    DEFAULT_KW,
    UNION_KW,
    ERROR,
    IDENT,
    UNDERSCORE,
    WHITESPACE,
    INT_NUMBER,
    FLOAT_NUMBER,
    LIFETIME,
    CHAR,
    BYTE,
    STRING,
    RAW_STRING,
    BYTE_STRING,
    RAW_BYTE_STRING,
    COMMENT,
    DOC_COMMENT,
    SHEBANG,
    FILE,
    STRUCT_ITEM,
    ENUM_ITEM,
    FN_ITEM,
    EXTERN_CRATE_ITEM,
    MOD_ITEM,
    USE_ITEM,
    STATIC_ITEM,
    CONST_ITEM,
    TRAIT_ITEM,
    IMPL_ITEM,
    TYPE_ITEM,
    MACRO_CALL,
    TOKEN_TREE,
    PAREN_TYPE,
    TUPLE_TYPE,
    NEVER_TYPE,
    PATH_TYPE,
    POINTER_TYPE,
    ARRAY_TYPE,
    SLICE_TYPE,
    REFERENCE_TYPE,
    PLACEHOLDER_TYPE,
    FN_POINTER_TYPE,
    FOR_TYPE,
    IMPL_TRAIT_TYPE,
    REF_PAT,
    BIND_PAT,
    PLACEHOLDER_PAT,
    PATH_PAT,
    STRUCT_PAT,
    TUPLE_STRUCT_PAT,
    TUPLE_PAT,
    SLICE_PAT,
    RANGE_PAT,
    TUPLE_EXPR,
    ARRAY_EXPR,
    PAREN_EXPR,
    PATH_EXPR,
    LAMBDA_EXPR,
    IF_EXPR,
    WHILE_EXPR,
    LOOP_EXPR,
    FOR_EXPR,
    BLOCK_EXPR,
    RETURN_EXPR,
    MATCH_EXPR,
    MATCH_ARM,
    MATCH_GUARD,
    STRUCT_LIT,
    STRUCT_LIT_FIELD,
    CALL_EXPR,
    INDEX_EXPR,
    METHOD_CALL_EXPR,
    FIELD_EXPR,
    TRY_EXPR,
    CAST_EXPR,
    REF_EXPR,
    PREFIX_EXPR,
    RANGE_EXPR,
    BIN_EXPR,
    EXTERN_BLOCK_EXPR,
    ENUM_VARIANT,
    NAMED_FIELD,
    POS_FIELD,
    ATTR,
    META_ITEM,
    USE_TREE,
    PATH,
    PATH_SEGMENT,
    LITERAL,
    ALIAS,
    VISIBILITY,
    WHERE_CLAUSE,
    ABI,
    NAME,
    NAME_REF,
    LET_STMT,
    EXPR_STMT,
    TYPE_PARAM_LIST,
    LIFETIME_PARAM,
    TYPE_PARAM,
    TYPE_ARG_LIST,
    LIFETIME_ARG,
    TYPE_ARG,
    ASSOC_TYPE_ARG,
    PARAM_LIST,
    PARAM,
    SELF_PARAM,
    ARG_LIST,
    // Technical SyntaxKinds: they appear temporally during parsing,
    // but never end up in the final tree
    #[doc(hidden)]
    TOMBSTONE,
    #[doc(hidden)]
    EOF,
}
use self::SyntaxKind::*;

impl SyntaxKind {
    pub fn is_keyword(self) -> bool {
        match self {
            | USE_KW
            | FN_KW
            | STRUCT_KW
            | ENUM_KW
            | TRAIT_KW
            | IMPL_KW
            | TRUE_KW
            | FALSE_KW
            | AS_KW
            | EXTERN_KW
            | CRATE_KW
            | MOD_KW
            | PUB_KW
            | SELF_KW
            | SUPER_KW
            | IN_KW
            | WHERE_KW
            | FOR_KW
            | LOOP_KW
            | WHILE_KW
            | IF_KW
            | ELSE_KW
            | MATCH_KW
            | CONST_KW
            | STATIC_KW
            | MUT_KW
            | UNSAFE_KW
            | TYPE_KW
            | REF_KW
            | LET_KW
            | MOVE_KW
            | RETURN_KW
            | AUTO_KW
            | DEFAULT_KW
            | UNION_KW
                => true,
            _ => false
        }
    }

    pub(crate) fn info(self) -> &'static SyntaxInfo {
        match self {
            SEMI => &SyntaxInfo { name: "SEMI" },
            COMMA => &SyntaxInfo { name: "COMMA" },
            L_PAREN => &SyntaxInfo { name: "L_PAREN" },
            R_PAREN => &SyntaxInfo { name: "R_PAREN" },
            L_CURLY => &SyntaxInfo { name: "L_CURLY" },
            R_CURLY => &SyntaxInfo { name: "R_CURLY" },
            L_BRACK => &SyntaxInfo { name: "L_BRACK" },
            R_BRACK => &SyntaxInfo { name: "R_BRACK" },
            L_ANGLE => &SyntaxInfo { name: "L_ANGLE" },
            R_ANGLE => &SyntaxInfo { name: "R_ANGLE" },
            AT => &SyntaxInfo { name: "AT" },
            POUND => &SyntaxInfo { name: "POUND" },
            TILDE => &SyntaxInfo { name: "TILDE" },
            QUESTION => &SyntaxInfo { name: "QUESTION" },
            DOLLAR => &SyntaxInfo { name: "DOLLAR" },
            AMP => &SyntaxInfo { name: "AMP" },
            PIPE => &SyntaxInfo { name: "PIPE" },
            PLUS => &SyntaxInfo { name: "PLUS" },
            STAR => &SyntaxInfo { name: "STAR" },
            SLASH => &SyntaxInfo { name: "SLASH" },
            CARET => &SyntaxInfo { name: "CARET" },
            PERCENT => &SyntaxInfo { name: "PERCENT" },
            DOT => &SyntaxInfo { name: "DOT" },
            DOTDOT => &SyntaxInfo { name: "DOTDOT" },
            DOTDOTDOT => &SyntaxInfo { name: "DOTDOTDOT" },
            DOTDOTEQ => &SyntaxInfo { name: "DOTDOTEQ" },
            COLON => &SyntaxInfo { name: "COLON" },
            COLONCOLON => &SyntaxInfo { name: "COLONCOLON" },
            EQ => &SyntaxInfo { name: "EQ" },
            EQEQ => &SyntaxInfo { name: "EQEQ" },
            FAT_ARROW => &SyntaxInfo { name: "FAT_ARROW" },
            EXCL => &SyntaxInfo { name: "EXCL" },
            NEQ => &SyntaxInfo { name: "NEQ" },
            MINUS => &SyntaxInfo { name: "MINUS" },
            THIN_ARROW => &SyntaxInfo { name: "THIN_ARROW" },
            LTEQ => &SyntaxInfo { name: "LTEQ" },
            GTEQ => &SyntaxInfo { name: "GTEQ" },
            PLUSEQ => &SyntaxInfo { name: "PLUSEQ" },
            MINUSEQ => &SyntaxInfo { name: "MINUSEQ" },
            AMPAMP => &SyntaxInfo { name: "AMPAMP" },
            PIPEPIPE => &SyntaxInfo { name: "PIPEPIPE" },
            SHL => &SyntaxInfo { name: "SHL" },
            SHR => &SyntaxInfo { name: "SHR" },
            SHLEQ => &SyntaxInfo { name: "SHLEQ" },
            SHREQ => &SyntaxInfo { name: "SHREQ" },
            USE_KW => &SyntaxInfo { name: "USE_KW" },
            FN_KW => &SyntaxInfo { name: "FN_KW" },
            STRUCT_KW => &SyntaxInfo { name: "STRUCT_KW" },
            ENUM_KW => &SyntaxInfo { name: "ENUM_KW" },
            TRAIT_KW => &SyntaxInfo { name: "TRAIT_KW" },
            IMPL_KW => &SyntaxInfo { name: "IMPL_KW" },
            TRUE_KW => &SyntaxInfo { name: "TRUE_KW" },
            FALSE_KW => &SyntaxInfo { name: "FALSE_KW" },
            AS_KW => &SyntaxInfo { name: "AS_KW" },
            EXTERN_KW => &SyntaxInfo { name: "EXTERN_KW" },
            CRATE_KW => &SyntaxInfo { name: "CRATE_KW" },
            MOD_KW => &SyntaxInfo { name: "MOD_KW" },
            PUB_KW => &SyntaxInfo { name: "PUB_KW" },
            SELF_KW => &SyntaxInfo { name: "SELF_KW" },
            SUPER_KW => &SyntaxInfo { name: "SUPER_KW" },
            IN_KW => &SyntaxInfo { name: "IN_KW" },
            WHERE_KW => &SyntaxInfo { name: "WHERE_KW" },
            FOR_KW => &SyntaxInfo { name: "FOR_KW" },
            LOOP_KW => &SyntaxInfo { name: "LOOP_KW" },
            WHILE_KW => &SyntaxInfo { name: "WHILE_KW" },
            IF_KW => &SyntaxInfo { name: "IF_KW" },
            ELSE_KW => &SyntaxInfo { name: "ELSE_KW" },
            MATCH_KW => &SyntaxInfo { name: "MATCH_KW" },
            CONST_KW => &SyntaxInfo { name: "CONST_KW" },
            STATIC_KW => &SyntaxInfo { name: "STATIC_KW" },
            MUT_KW => &SyntaxInfo { name: "MUT_KW" },
            UNSAFE_KW => &SyntaxInfo { name: "UNSAFE_KW" },
            TYPE_KW => &SyntaxInfo { name: "TYPE_KW" },
            REF_KW => &SyntaxInfo { name: "REF_KW" },
            LET_KW => &SyntaxInfo { name: "LET_KW" },
            MOVE_KW => &SyntaxInfo { name: "MOVE_KW" },
            RETURN_KW => &SyntaxInfo { name: "RETURN_KW" },
            AUTO_KW => &SyntaxInfo { name: "AUTO_KW" },
            DEFAULT_KW => &SyntaxInfo { name: "DEFAULT_KW" },
            UNION_KW => &SyntaxInfo { name: "UNION_KW" },
            ERROR => &SyntaxInfo { name: "ERROR" },
            IDENT => &SyntaxInfo { name: "IDENT" },
            UNDERSCORE => &SyntaxInfo { name: "UNDERSCORE" },
            WHITESPACE => &SyntaxInfo { name: "WHITESPACE" },
            INT_NUMBER => &SyntaxInfo { name: "INT_NUMBER" },
            FLOAT_NUMBER => &SyntaxInfo { name: "FLOAT_NUMBER" },
            LIFETIME => &SyntaxInfo { name: "LIFETIME" },
            CHAR => &SyntaxInfo { name: "CHAR" },
            BYTE => &SyntaxInfo { name: "BYTE" },
            STRING => &SyntaxInfo { name: "STRING" },
            RAW_STRING => &SyntaxInfo { name: "RAW_STRING" },
            BYTE_STRING => &SyntaxInfo { name: "BYTE_STRING" },
            RAW_BYTE_STRING => &SyntaxInfo { name: "RAW_BYTE_STRING" },
            COMMENT => &SyntaxInfo { name: "COMMENT" },
            DOC_COMMENT => &SyntaxInfo { name: "DOC_COMMENT" },
            SHEBANG => &SyntaxInfo { name: "SHEBANG" },
            FILE => &SyntaxInfo { name: "FILE" },
            STRUCT_ITEM => &SyntaxInfo { name: "STRUCT_ITEM" },
            ENUM_ITEM => &SyntaxInfo { name: "ENUM_ITEM" },
            FN_ITEM => &SyntaxInfo { name: "FN_ITEM" },
            EXTERN_CRATE_ITEM => &SyntaxInfo { name: "EXTERN_CRATE_ITEM" },
            MOD_ITEM => &SyntaxInfo { name: "MOD_ITEM" },
            USE_ITEM => &SyntaxInfo { name: "USE_ITEM" },
            STATIC_ITEM => &SyntaxInfo { name: "STATIC_ITEM" },
            CONST_ITEM => &SyntaxInfo { name: "CONST_ITEM" },
            TRAIT_ITEM => &SyntaxInfo { name: "TRAIT_ITEM" },
            IMPL_ITEM => &SyntaxInfo { name: "IMPL_ITEM" },
            TYPE_ITEM => &SyntaxInfo { name: "TYPE_ITEM" },
            MACRO_CALL => &SyntaxInfo { name: "MACRO_CALL" },
            TOKEN_TREE => &SyntaxInfo { name: "TOKEN_TREE" },
            PAREN_TYPE => &SyntaxInfo { name: "PAREN_TYPE" },
            TUPLE_TYPE => &SyntaxInfo { name: "TUPLE_TYPE" },
            NEVER_TYPE => &SyntaxInfo { name: "NEVER_TYPE" },
            PATH_TYPE => &SyntaxInfo { name: "PATH_TYPE" },
            POINTER_TYPE => &SyntaxInfo { name: "POINTER_TYPE" },
            ARRAY_TYPE => &SyntaxInfo { name: "ARRAY_TYPE" },
            SLICE_TYPE => &SyntaxInfo { name: "SLICE_TYPE" },
            REFERENCE_TYPE => &SyntaxInfo { name: "REFERENCE_TYPE" },
            PLACEHOLDER_TYPE => &SyntaxInfo { name: "PLACEHOLDER_TYPE" },
            FN_POINTER_TYPE => &SyntaxInfo { name: "FN_POINTER_TYPE" },
            FOR_TYPE => &SyntaxInfo { name: "FOR_TYPE" },
            IMPL_TRAIT_TYPE => &SyntaxInfo { name: "IMPL_TRAIT_TYPE" },
            REF_PAT => &SyntaxInfo { name: "REF_PAT" },
            BIND_PAT => &SyntaxInfo { name: "BIND_PAT" },
            PLACEHOLDER_PAT => &SyntaxInfo { name: "PLACEHOLDER_PAT" },
            PATH_PAT => &SyntaxInfo { name: "PATH_PAT" },
            STRUCT_PAT => &SyntaxInfo { name: "STRUCT_PAT" },
            TUPLE_STRUCT_PAT => &SyntaxInfo { name: "TUPLE_STRUCT_PAT" },
            TUPLE_PAT => &SyntaxInfo { name: "TUPLE_PAT" },
            SLICE_PAT => &SyntaxInfo { name: "SLICE_PAT" },
            RANGE_PAT => &SyntaxInfo { name: "RANGE_PAT" },
            TUPLE_EXPR => &SyntaxInfo { name: "TUPLE_EXPR" },
            ARRAY_EXPR => &SyntaxInfo { name: "ARRAY_EXPR" },
            PAREN_EXPR => &SyntaxInfo { name: "PAREN_EXPR" },
            PATH_EXPR => &SyntaxInfo { name: "PATH_EXPR" },
            LAMBDA_EXPR => &SyntaxInfo { name: "LAMBDA_EXPR" },
            IF_EXPR => &SyntaxInfo { name: "IF_EXPR" },
            WHILE_EXPR => &SyntaxInfo { name: "WHILE_EXPR" },
            LOOP_EXPR => &SyntaxInfo { name: "LOOP_EXPR" },
            FOR_EXPR => &SyntaxInfo { name: "FOR_EXPR" },
            BLOCK_EXPR => &SyntaxInfo { name: "BLOCK_EXPR" },
            RETURN_EXPR => &SyntaxInfo { name: "RETURN_EXPR" },
            MATCH_EXPR => &SyntaxInfo { name: "MATCH_EXPR" },
            MATCH_ARM => &SyntaxInfo { name: "MATCH_ARM" },
            MATCH_GUARD => &SyntaxInfo { name: "MATCH_GUARD" },
            STRUCT_LIT => &SyntaxInfo { name: "STRUCT_LIT" },
            STRUCT_LIT_FIELD => &SyntaxInfo { name: "STRUCT_LIT_FIELD" },
            CALL_EXPR => &SyntaxInfo { name: "CALL_EXPR" },
            INDEX_EXPR => &SyntaxInfo { name: "INDEX_EXPR" },
            METHOD_CALL_EXPR => &SyntaxInfo { name: "METHOD_CALL_EXPR" },
            FIELD_EXPR => &SyntaxInfo { name: "FIELD_EXPR" },
            TRY_EXPR => &SyntaxInfo { name: "TRY_EXPR" },
            CAST_EXPR => &SyntaxInfo { name: "CAST_EXPR" },
            REF_EXPR => &SyntaxInfo { name: "REF_EXPR" },
            PREFIX_EXPR => &SyntaxInfo { name: "PREFIX_EXPR" },
            RANGE_EXPR => &SyntaxInfo { name: "RANGE_EXPR" },
            BIN_EXPR => &SyntaxInfo { name: "BIN_EXPR" },
            EXTERN_BLOCK_EXPR => &SyntaxInfo { name: "EXTERN_BLOCK_EXPR" },
            ENUM_VARIANT => &SyntaxInfo { name: "ENUM_VARIANT" },
            NAMED_FIELD => &SyntaxInfo { name: "NAMED_FIELD" },
            POS_FIELD => &SyntaxInfo { name: "POS_FIELD" },
            ATTR => &SyntaxInfo { name: "ATTR" },
            META_ITEM => &SyntaxInfo { name: "META_ITEM" },
            USE_TREE => &SyntaxInfo { name: "USE_TREE" },
            PATH => &SyntaxInfo { name: "PATH" },
            PATH_SEGMENT => &SyntaxInfo { name: "PATH_SEGMENT" },
            LITERAL => &SyntaxInfo { name: "LITERAL" },
            ALIAS => &SyntaxInfo { name: "ALIAS" },
            VISIBILITY => &SyntaxInfo { name: "VISIBILITY" },
            WHERE_CLAUSE => &SyntaxInfo { name: "WHERE_CLAUSE" },
            ABI => &SyntaxInfo { name: "ABI" },
            NAME => &SyntaxInfo { name: "NAME" },
            NAME_REF => &SyntaxInfo { name: "NAME_REF" },
            LET_STMT => &SyntaxInfo { name: "LET_STMT" },
            EXPR_STMT => &SyntaxInfo { name: "EXPR_STMT" },
            TYPE_PARAM_LIST => &SyntaxInfo { name: "TYPE_PARAM_LIST" },
            LIFETIME_PARAM => &SyntaxInfo { name: "LIFETIME_PARAM" },
            TYPE_PARAM => &SyntaxInfo { name: "TYPE_PARAM" },
            TYPE_ARG_LIST => &SyntaxInfo { name: "TYPE_ARG_LIST" },
            LIFETIME_ARG => &SyntaxInfo { name: "LIFETIME_ARG" },
            TYPE_ARG => &SyntaxInfo { name: "TYPE_ARG" },
            ASSOC_TYPE_ARG => &SyntaxInfo { name: "ASSOC_TYPE_ARG" },
            PARAM_LIST => &SyntaxInfo { name: "PARAM_LIST" },
            PARAM => &SyntaxInfo { name: "PARAM" },
            SELF_PARAM => &SyntaxInfo { name: "SELF_PARAM" },
            ARG_LIST => &SyntaxInfo { name: "ARG_LIST" },
            TOMBSTONE => &SyntaxInfo { name: "TOMBSTONE" },
            EOF => &SyntaxInfo { name: "EOF" },
        }
    }
    pub(crate) fn from_keyword(ident: &str) -> Option<SyntaxKind> {
        let kw = match ident {
            "use" => USE_KW,
            "fn" => FN_KW,
            "struct" => STRUCT_KW,
            "enum" => ENUM_KW,
            "trait" => TRAIT_KW,
            "impl" => IMPL_KW,
            "true" => TRUE_KW,
            "false" => FALSE_KW,
            "as" => AS_KW,
            "extern" => EXTERN_KW,
            "crate" => CRATE_KW,
            "mod" => MOD_KW,
            "pub" => PUB_KW,
            "self" => SELF_KW,
            "super" => SUPER_KW,
            "in" => IN_KW,
            "where" => WHERE_KW,
            "for" => FOR_KW,
            "loop" => LOOP_KW,
            "while" => WHILE_KW,
            "if" => IF_KW,
            "else" => ELSE_KW,
            "match" => MATCH_KW,
            "const" => CONST_KW,
            "static" => STATIC_KW,
            "mut" => MUT_KW,
            "unsafe" => UNSAFE_KW,
            "type" => TYPE_KW,
            "ref" => REF_KW,
            "let" => LET_KW,
            "move" => MOVE_KW,
            "return" => RETURN_KW,
            _ => return None,
        };
        Some(kw)
    }

    pub(crate) fn from_char(c: char) -> Option<SyntaxKind> {
        let tok = match c {
            ';' => SEMI,
            ',' => COMMA,
            '(' => L_PAREN,
            ')' => R_PAREN,
            '{' => L_CURLY,
            '}' => R_CURLY,
            '[' => L_BRACK,
            ']' => R_BRACK,
            '<' => L_ANGLE,
            '>' => R_ANGLE,
            '@' => AT,
            '#' => POUND,
            '~' => TILDE,
            '?' => QUESTION,
            '$' => DOLLAR,
            '&' => AMP,
            '|' => PIPE,
            '+' => PLUS,
            '*' => STAR,
            '/' => SLASH,
            '^' => CARET,
            '%' => PERCENT,
            _ => return None,
        };
        Some(tok)
    }

    pub(crate) fn static_text(self) -> Option<&'static str> {
        let tok = match self {
            SEMI => ";",
            COMMA => ",",
            L_PAREN => "(",
            R_PAREN => ")",
            L_CURLY => "{",
            R_CURLY => "}",
            L_BRACK => "[",
            R_BRACK => "]",
            L_ANGLE => "<",
            R_ANGLE => ">",
            AT => "@",
            POUND => "#",
            TILDE => "~",
            QUESTION => "?",
            DOLLAR => "$",
            AMP => "&",
            PIPE => "|",
            PLUS => "+",
            STAR => "*",
            SLASH => "/",
            CARET => "^",
            PERCENT => "%",
            DOT => ".",
            DOTDOT => "..",
            DOTDOTDOT => "...",
            DOTDOTEQ => "..=",
            COLON => ":",
            COLONCOLON => "::",
            EQ => "=",
            EQEQ => "==",
            FAT_ARROW => "=>",
            EXCL => "!",
            NEQ => "!=",
            MINUS => "-",
            THIN_ARROW => "->",
            LTEQ => "<=",
            GTEQ => ">=",
            PLUSEQ => "+=",
            MINUSEQ => "-=",
            AMPAMP => "&&",
            PIPEPIPE => "||",
            SHL => "<<",
            SHR => ">>",
            SHLEQ => "<<=",
            SHREQ => ">>=",

            USE_KW => "use",
            FN_KW => "fn",
            STRUCT_KW => "struct",
            ENUM_KW => "enum",
            TRAIT_KW => "trait",
            IMPL_KW => "impl",
            TRUE_KW => "true",
            FALSE_KW => "false",
            AS_KW => "as",
            EXTERN_KW => "extern",
            CRATE_KW => "crate",
            MOD_KW => "mod",
            PUB_KW => "pub",
            SELF_KW => "self",
            SUPER_KW => "super",
            IN_KW => "in",
            WHERE_KW => "where",
            FOR_KW => "for",
            LOOP_KW => "loop",
            WHILE_KW => "while",
            IF_KW => "if",
            ELSE_KW => "else",
            MATCH_KW => "match",
            CONST_KW => "const",
            STATIC_KW => "static",
            MUT_KW => "mut",
            UNSAFE_KW => "unsafe",
            TYPE_KW => "type",
            REF_KW => "ref",
            LET_KW => "let",
            MOVE_KW => "move",
            RETURN_KW => "return",
            AUTO_KW => "auto",
            DEFAULT_KW => "default",
            UNION_KW => "union",
            _ => return None,
        };
        Some(tok)
    }
}

