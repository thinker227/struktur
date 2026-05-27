/// CSS-like selector syntax for syntax trees.
/// Returns an iterator of descendant nodes which match the selector.
///
/// The selector is made up of one or more *clauses*:
/// - `> *`: Selects all immediate child nodes.
///   - `> *[n]`: Selects the `n`th immediate child node.
/// - `> (k)`: Selects all immediate child nodes with kind `k`.
///   - `> (k)[n]`: Selects the `n`th child node with kind `k`.
/// - `*`: Selects all descendant nodes.
/// - `(k)`: Selects all descendant nodes with kind `k`.
/// - `as T`: Attempts to cast the items of the iterator into `T` using `T::new` returning `Option<T>`.
///   Must be the final clause of the selector.
///
/// # Examples
/// ```ignore
/// // select all immediate children
/// select_nodes!(node => > *);
///
/// // select all `LitExpr` nodes which are immediate children of an `Expr` node
/// select_nodes!(node => (Kind::Expr) > (Kind::LitExpr))
///
/// // select all children of the first `Stmt` node
/// select_nodes!(node => > (Kind::Stmt)[0] > *)
///
/// // select the first child of every immediate child
/// select_nodes!(node => > *[0])
/// ```
/// Due to the syntax limitations of declarative macros, kind clauses have to be enclosed in parentheses.
#[macro_export]
macro_rules! select_nodes {
    // Entry arm (nicer surface syntax)
    ($tree:expr => $($selector:tt)*) => {
        select_nodes!(
            ::std::iter::once($crate::syntax::tree::SyntaxNode::from($tree));
            $($selector)*
        )
    };

    // Immediate child indexing
    ($tree:expr; > * [$index:expr] $($rest:tt)*) => {
        select_nodes!(
            $tree.filter_map(|x| x.node($index));
            $($rest)*
        )
    };

    // Immediate children
    ($tree:expr; > * $($rest:tt)*) => {
        select_nodes!(
            $tree.flat_map(|x| x.nodes());
            $($rest)*
        )
    };

    // Immediate child indexing with filter
    ($tree:expr; > ($kind:expr) [$index:expr] $($rest:tt)*) => {
        select_nodes!(
            $tree.filter_map(|x| x
                .nodes()
                .filter(|x| x.kind() == &$kind)
                .nth($index)
            );
            $($rest)*
        )
    };

    // Immediate children with filter
    ($tree:expr; > ($kind:expr) $($rest:tt)*) => {
        select_nodes!(
            $tree
                .flat_map(|x| x.nodes())
                .filter(|x| x.kind() == &$kind);
            $($rest)*
        )
    };

    // Descendants
    ($tree:expr; * $($rest:tt)*) => {
        select_nodes!(
            $tree.flat_map(|x| x.all_descendants());
            $($rest)*
        )
    };

    // Descendants with filter
    ($tree:expr; ($kind:expr) $($rest:tt)*) => {
        select_nodes!(
            $tree
                .flat_map(|x| x.all_descendants())
                .filter(|x| x.kind() == &$kind);
            $($rest)*
        )
    };

    // Finish with cast
    ($tree:expr; as $ty:ty) => {
        $tree.filter_map(|x| <$ty>::new(x))
    };

    // Finish
    ($tree:expr;) => {
        $tree
    }
}
