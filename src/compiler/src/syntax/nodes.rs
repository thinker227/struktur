//! Structs and enums as a strongly typed layer on top of the untyped syntax tree.
//!
//! This, along with the kinds defined in [SyntaxKind], loosely defines the structure of the AST.
//! It doesn't *statically* define any structure, but more-so lays out the structure for the parser to follow
//! when producing nodes.
//!
//! All structs in this module are newtype wrapper structs around [SyntaxNode].
//! None of the structs store their properties directly, every property is lazily computed.

use super::{NodeId, SyntaxKind, SyntaxNode, Token};
use crate::text::{Spanned, TextLocation, TextSpan};

macro_rules! node {
    ($name:ident, $kind:expr) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        #[repr(transparent)]
        pub struct $name<'map>(SyntaxNode<'map>);

        impl<'map> $name<'map> {
            pub const KIND: SyntaxKind = $kind;

            pub fn new(node: SyntaxNode<'map>) -> Option<Self> {
                if *node.kind() == $kind {
                    Some(Self(node))
                } else {
                    None
                }
            }

            pub fn raw(self) -> SyntaxNode<'map> {
                self.0
            }

            pub fn id(self) -> NodeId {
                self.raw().id()
            }

            pub fn location(self) -> TextLocation {
                self.raw().location()
            }
        }

        impl Spanned for $name<'_> {
            fn span(&self) -> TextSpan {
                self.raw().span()
            }
        }

        impl<'map> From<$name<'map>> for SyntaxNode<'map> {
            fn from(value: $name<'map>) -> Self {
                value.raw()
            }
        }

        impl From<$name<'_>> for NodeId {
            fn from(value: $name<'_>) -> Self {
                value.id()
            }
        }
    };
}

macro_rules! enum_node {
    ($name:ident { $($var_name:ident($ty:ident, $kind:pat)),* }) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum $name<'map> {
            $(
                $var_name($ty<'map>)
            ),*
        }

        impl<'map> $name<'map> {
            pub fn new(node: SyntaxNode<'map>) -> Option<Self> {
                match node.kind() {
                    $(
                        $kind => Some(Self::$var_name(<$ty>::new(node).unwrap())),
                    )*
                    _ => None
                }
            }

            pub fn raw(self) -> SyntaxNode<'map> {
                match self {
                    $(
                        Self::$var_name(x) => x.raw(),
                    )*
                }
            }

            pub fn id(self) -> NodeId {
                self.raw().id()
            }

            pub fn location(self) -> TextLocation {
                self.raw().location()
            }
        }

        impl Spanned for $name<'_> {
            fn span(&self) -> TextSpan {
                self.raw().span()
            }
        }

        impl<'map> From<$name<'map>> for SyntaxNode<'map> {
            fn from(value: $name<'map>) -> Self {
                value.raw()
            }
        }

        impl From<$name<'_>> for NodeId {
            fn from(value: $name<'_>) -> Self {
                value.id()
            }
        }
    };
}

// 'name'
node!(Ident, SyntaxKind::Ident);

impl<'map> Ident<'map> {
    pub fn name(self) -> Token {
        *self.0.token(0).unwrap()
    }
}

// Item* '<eoi>'
node!(Root, SyntaxKind::Root);

impl<'map> Root<'map> {
    pub fn items(self) -> impl Iterator<Item = Item<'map>> + Clone {
        self.0.nodes().map(|x| Item::new(x).unwrap())
    }

    pub fn eoi(self) -> Token {
        *self.0.token(0).unwrap()
    }
}

enum_node!(Item {
    Binding(Binding, SyntaxKind::Binding)
});

// 'let' Ident TyExpr? '=' Expr
node!(Binding, SyntaxKind::Binding);

impl<'map> Binding<'map> {
    pub fn let_tok(self) -> Token {
        *self.0.token(0).unwrap()
    }

    pub fn ident(self) -> Ident<'map> {
        Ident::new(self.0.node(0).unwrap()).unwrap()
    }

    pub fn has_ty_ann(self) -> bool {
        self.0.node_count() > 2
    }

    pub fn ty_ann(self) -> Option<TyAnn<'map>> {
        self.has_ty_ann()
            .then(|| TyAnn::new(self.0.node(1).unwrap()).unwrap())
    }

    pub fn equals_tok(self) -> Token {
        *self.0.token(0).unwrap()
    }

    pub fn expr(self) -> Expr<'map> {
        let index = if self.has_ty_ann() { 2 } else { 1 };
        Expr::new(self.0.node(index).unwrap()).unwrap()
    }
}

enum_node!(Expr {
    Unit(UnitExpr, SyntaxKind::UnitExpr),
    Int(IntExpr, SyntaxKind::IntExpr),
    Bool(BoolExpr, SyntaxKind::BoolExpr),
    String(StringExpr, SyntaxKind::StringExpr),
    Var(VarExpr, SyntaxKind::VarExpr),
    Let(LetExpr, SyntaxKind::LetExpr),
    Lambda(LambdaExpr, SyntaxKind::LambdaExpr),
    Application(ApplicationExpr, SyntaxKind::ApplicationExpr),
    IfElse(IfElseExpr, SyntaxKind::IfElseExpr),
    TyAnn(TyAnnExpr, SyntaxKind::TyAnnExpr),
    Grouping(GroupingExpr, SyntaxKind::GroupingExpr)
});

// '(' ')'
node!(UnitExpr, SyntaxKind::UnitExpr);

impl<'map> UnitExpr<'map> {
    pub fn open_paren(self) -> Token {
        *self.0.token(0).unwrap()
    }

    pub fn close_paren(self) -> Token {
        *self.0.token(1).unwrap()
    }
}

// '0'
node!(IntExpr, SyntaxKind::IntExpr);

impl<'map> IntExpr<'map> {
    pub fn value(self) -> Token {
        *self.0.token(0).unwrap()
    }
}

// 'true'
node!(BoolExpr, SyntaxKind::BoolExpr);

impl<'map> BoolExpr<'map> {
    pub fn value(self) -> Token {
        *self.0.token(0).unwrap()
    }
}

// '"uwu"'
node!(StringExpr, SyntaxKind::StringExpr);

impl<'map> StringExpr<'map> {
    pub fn value(self) -> Token {
        *self.0.token(0).unwrap()
    }
}

// Ident
node!(VarExpr, SyntaxKind::VarExpr);

impl<'map> VarExpr<'map> {
    pub fn ident(self) -> Ident<'map> {
        Ident::new(self.0.node(0).unwrap()).unwrap()
    }
}

// 'let' Pattern '=' Expr 'in' Expr
node!(LetExpr, SyntaxKind::LetExpr);

impl<'map> LetExpr<'map> {
    pub fn let_tok(self) -> Token {
        *self.0.token(0).unwrap()
    }

    pub fn pattern(self) -> Pattern<'map> {
        Pattern::new(self.0.node(0).unwrap()).unwrap()
    }

    pub fn equals_tok(self) -> Token {
        *self.0.token(1).unwrap()
    }

    pub fn value(self) -> Expr<'map> {
        Expr::new(self.0.node(1).unwrap()).unwrap()
    }

    pub fn in_tok(self) -> Token {
        *self.0.token(2).unwrap()
    }

    pub fn subexpr(self) -> Expr<'map> {
        Expr::new(self.0.node(2).unwrap()).unwrap()
    }
}

// 'fun' ('|'? Case) ('|' Case)*
node!(LambdaExpr, SyntaxKind::LambdaExpr);

impl<'map> LambdaExpr<'map> {
    pub fn fun(self) -> Token {
        *self.0.token(0).unwrap()
    }

    pub fn leading_bar(self) -> Option<Token> {
        self.0.node(0).unwrap().token(0).copied()
    }

    pub fn bars(self) -> impl Iterator<Item = Token> + Clone {
        self.0.nodes().filter_map(|x| x.token(0).copied())
    }

    pub fn cases(self) -> impl Iterator<Item = Case<'map>> + Clone {
        self.0
            .nodes()
            .map(|x| Case::new(x.node(0).unwrap()).unwrap())
    }
}

// Expr Expr
node!(ApplicationExpr, SyntaxKind::ApplicationExpr);

impl<'map> ApplicationExpr<'map> {
    pub fn target(self) -> Expr<'map> {
        Expr::new(self.0.node(0).unwrap()).unwrap()
    }

    pub fn arg(self) -> Expr<'map> {
        Expr::new(self.0.node(1).unwrap()).unwrap()
    }
}

// 'if' Expr 'then' Expr 'else' Expr
node!(IfElseExpr, SyntaxKind::IfElseExpr);

impl<'map> IfElseExpr<'map> {
    pub fn if_tok(self) -> Token {
        *self.0.token(0).unwrap()
    }

    pub fn condition(self) -> Expr<'map> {
        Expr::new(self.0.node(0).unwrap()).unwrap()
    }

    pub fn then_tok(self) -> Token {
        *self.0.token(1).unwrap()
    }

    pub fn true_branch(self) -> Expr<'map> {
        Expr::new(self.0.node(1).unwrap()).unwrap()
    }

    pub fn else_tok(self) -> Token {
        *self.0.token(2).unwrap()
    }

    pub fn false_branch(self) -> Expr<'map> {
        Expr::new(self.0.node(2).unwrap()).unwrap()
    }
}

// Expr TyAnn
node!(TyAnnExpr, SyntaxKind::TyAnnExpr);

impl<'map> TyAnnExpr<'map> {
    pub fn expr(self) -> Expr<'map> {
        Expr::new(self.0.node(0).unwrap()).unwrap()
    }

    pub fn ty_ann(self) -> TyAnn<'map> {
        TyAnn::new(self.0.node(1).unwrap()).unwrap()
    }
}

// '(' Expr ')'
node!(GroupingExpr, SyntaxKind::GroupingExpr);

impl<'map> GroupingExpr<'map> {
    pub fn open_paren(self) -> Token {
        *self.0.token(0).unwrap()
    }

    pub fn expr(self) -> Expr<'map> {
        Expr::new(self.0.node(0).unwrap()).unwrap()
    }

    pub fn close_paren(self) -> Token {
        *self.0.token(1).unwrap()
    }
}

// Pattern -> Expr
node!(Case, SyntaxKind::Case);

impl<'map> Case<'map> {
    pub fn pattern(self) -> Pattern<'map> {
        Pattern::new(self.0.node(0).unwrap()).unwrap()
    }

    pub fn arrow(self) -> Token {
        *self.0.token(0).unwrap()
    }

    pub fn body(self) -> Expr<'map> {
        Expr::new(self.0.node(1).unwrap()).unwrap()
    }
}

enum_node!(Pattern {
    Wildcard(WildcardPattern, SyntaxKind::WildcardPattern),
    Var(VarPattern, SyntaxKind::VarPattern),
    Unit(UnitPattern, SyntaxKind::UnitPattern),
    Number(IntPattern, SyntaxKind::IntPattern),
    Bool(BoolPattern, SyntaxKind::BoolPattern),
    TyAnn(TyAnnPattern, SyntaxKind::TyAnnPattern),
    Grouping(GroupingPattern, SyntaxKind::GroupingPattern)
});

// '( ')'
node!(UnitPattern, SyntaxKind::UnitPattern);

impl<'map> UnitPattern<'map> {
    pub fn open_paren(self) -> Token {
        *self.0.token(0).unwrap()
    }

    pub fn close_paren(self) -> Token {
        *self.0.token(1).unwrap()
    }
}

// '_'
node!(WildcardPattern, SyntaxKind::WildcardPattern);

impl<'map> WildcardPattern<'map> {
    pub fn underscore(self) -> Token {
        *self.0.token(0).unwrap()
    }
}

// Ident
node!(VarPattern, SyntaxKind::VarPattern);

impl<'map> VarPattern<'map> {
    pub fn ident(self) -> Ident<'map> {
        Ident::new(self.0.node(0).unwrap()).unwrap()
    }
}

// '0'
node!(IntPattern, SyntaxKind::IntPattern);

impl<'map> IntPattern<'map> {
    pub fn value(self) -> Token {
        *self.0.token(0).unwrap()
    }
}

// 'true'
node!(BoolPattern, SyntaxKind::BoolPattern);

impl<'map> BoolPattern<'map> {
    pub fn value(self) -> Token {
        *self.0.token(0).unwrap()
    }
}

// Pattern TyAnn
node!(TyAnnPattern, SyntaxKind::TyAnnPattern);

impl<'map> TyAnnPattern<'map> {
    pub fn pattern(self) -> Pattern<'map> {
        Pattern::new(self.0.node(0).unwrap()).unwrap()
    }

    pub fn ty_ann(self) -> TyAnn<'map> {
        TyAnn::new(self.0.node(1).unwrap()).unwrap()
    }
}

// '(' Pattern ')'
node!(GroupingPattern, SyntaxKind::GroupingPattern);

impl<'map> GroupingPattern<'map> {
    pub fn open_paren(self) -> Token {
        *self.0.token(0).unwrap()
    }

    pub fn pattern(self) -> Pattern<'map> {
        Pattern::new(self.0.node(0).unwrap()).unwrap()
    }

    pub fn close_paren(self) -> Token {
        *self.0.token(1).unwrap()
    }
}

// ':' TyExpr
node!(TyAnn, SyntaxKind::TyAnn);

impl<'map> TyAnn<'map> {
    pub fn colon(self) -> Token {
        *self.0.token(0).unwrap()
    }

    pub fn ty(self) -> TyExpr<'map> {
        TyExpr::new(self.0.node(0).unwrap()).unwrap()
    }
}

enum_node!(TyExpr {
    Unit(UnitTyExpr, SyntaxKind::UnitTyExpr),
    Int(IntTyExpr, SyntaxKind::IntTyExpr),
    Bool(BoolTyExpr, SyntaxKind::BoolTyExpr),
    String(StringTyExpr, SyntaxKind::StringTyExpr),
    Var(VarTyExpr, SyntaxKind::VarTyExpr),
    Function(FunctionTyExpr, SyntaxKind::FunctionTyExpr),
    Forall(ForallTyExpr, SyntaxKind::ForallTyExpr),
    Grouping(GroupingTyExpr, SyntaxKind::GroupingTyExpr)
});

// '( ')'
node!(UnitTyExpr, SyntaxKind::UnitTyExpr);

impl<'map> UnitTyExpr<'map> {
    pub fn open_paren(self) -> Token {
        *self.0.token(0).unwrap()
    }

    pub fn close_paren(self) -> Token {
        *self.0.token(1).unwrap()
    }
}

// 'Int'
node!(IntTyExpr, SyntaxKind::IntTyExpr);

impl<'map> IntTyExpr<'map> {
    pub fn tok(self) -> Token {
        *self.0.token(0).unwrap()
    }
}

// 'Bool'
node!(BoolTyExpr, SyntaxKind::BoolTyExpr);

impl<'map> BoolTyExpr<'map> {
    pub fn tok(self) -> Token {
        *self.0.token(0).unwrap()
    }
}

// 'String'
node!(StringTyExpr, SyntaxKind::StringTyExpr);

impl<'map> StringTyExpr<'map> {
    pub fn tok(self) -> Token {
        *self.0.token(0).unwrap()
    }
}

// "'a"
node!(VarTyExpr, SyntaxKind::VarTyExpr);

impl<'map> VarTyExpr<'map> {
    pub fn name(self) -> Token {
        *self.0.token(0).unwrap()
    }
}

// Type '->' Type
node!(FunctionTyExpr, SyntaxKind::FunctionTyExpr);

impl<'map> FunctionTyExpr<'map> {
    pub fn param(self) -> TyExpr<'map> {
        TyExpr::new(self.0.node(0).unwrap()).unwrap()
    }

    pub fn arrow(self) -> Token {
        *self.0.token(0).unwrap()
    }

    pub fn ret(self) -> TyExpr<'map> {
        TyExpr::new(self.0.node(1).unwrap()).unwrap()
    }
}

// 'forall' (VarTyExpr*) '.' TyExpr
node!(ForallTyExpr, SyntaxKind::ForallTyExpr);

impl<'map> ForallTyExpr<'map> {
    pub fn forall(self) -> Token {
        *self.0.token(0).unwrap()
    }

    pub fn vars(self) -> impl Iterator<Item = VarTyExpr<'map>> + Clone {
        self.0
            .node(0)
            .unwrap()
            .nodes()
            .map(|x| VarTyExpr::new(x).unwrap())
    }

    pub fn dot(self) -> Token {
        *self.0.token(1).unwrap()
    }

    pub fn subty(self) -> TyExpr<'map> {
        TyExpr::new(self.0.node(1).unwrap()).unwrap()
    }
}

// '(' TyExpr ')'
node!(GroupingTyExpr, SyntaxKind::GroupingTyExpr);

impl<'map> GroupingTyExpr<'map> {
    pub fn open_paren(self) -> Token {
        *self.0.token(0).unwrap()
    }

    pub fn ty(self) -> TyExpr<'map> {
        TyExpr::new(self.0.node(0).unwrap()).unwrap()
    }

    pub fn close_paren(self) -> Token {
        *self.0.token(1).unwrap()
    }
}
