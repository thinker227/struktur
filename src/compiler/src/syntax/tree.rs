//! Core untyped syntax tree structure.
//!
//! At their core, syntax nodes are a [RawNode] identified by a [NodeId] inside of a [NodeMap].
//! [RawNode] is completely opaque—the only way to get at the contents is by wrapping it
//! and the [NodeMap] it is registered in with a [SyntaxNode], which provides an API
//! for querying the children nodes and tokens.
//!
//! Everything in this module is paramerized by two types—a kind and a token.
//! This is in order to not tie the tree structure to the compiler's syntax kind enum or token struct,
//! mainly to aid with testing.
//!
//! The syntax tree is completely untyped besides for each node having a *kind* identifying it,
//! all nodes are otherwise represented uniformly as a set of child nodes and tokens.
//! Therefore, throughout most of the compiler, a set of strongly typed structs and enums
//! is layered on top of the untyped tree in order to provide a more rigid structure.

use crate::text::{Spanned, TextSpan};
use serde::{Serialize, Serializer, ser::SerializeStruct as _};
use slotmap::{SlotMap, new_key_type};
use std::{
    fmt::{Debug, Formatter},
    ptr,
};

/// A mapping between node IDs and syntax nodes.
pub type NodeMap<Kind, Token> = SlotMap<NodeId, RawNode<Kind, Token>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Indexed<T> {
    value: T,
    index: usize,
}

new_key_type! {
    /// A unique identifier for a syntax node.
    pub struct NodeId;
}

/// Opaque raw data for a syntax node.
///
/// [RawNode] has no API—it is completely opaque—the node API is entirely provided by [SyntaxNode].
/// Additionally, [RawNode] has certain invariants which have to be upheld in order to be efficient.
/// Because of this, [RawNode] cannot be constructed directly, and instead has to be constructed using a [NodeBuilder].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RawNode<Kind, Token> {
    kind: Kind,
    nodes: Vec<Indexed<NodeId>>,
    tokens: Vec<Indexed<Token>>,
}

/// Provides the main API for working with nodes.
///
/// [SyntaxNode] is just a wrapper around a [NodeId] and a reference to a [NodeMap]
/// and is as such trivially copyable since it's effectively just a pointer with metadata.
pub struct SyntaxNode<'map, Kind, Token> {
    map: &'map NodeMap<Kind, Token>,
    id: NodeId,
}

impl<'map, Kind, Token> SyntaxNode<'map, Kind, Token> {
    /// Creates a builder for a new node.
    pub fn build(kind: Kind) -> NodeBuilder<Kind, Token> {
        NodeBuilder::new(kind)
    }

    /// Creates a new [SyntaxNode].
    ///
    /// The ID **has** to be present in the map, otherwise most methods on this struct will panic.
    pub fn new(map: &'map NodeMap<Kind, Token>, id: NodeId) -> Self {
        Self { map, id }
    }

    /// Gets the wrapped map.
    pub fn map(self) -> &'map NodeMap<Kind, Token> {
        self.map
    }

    /// Gets the node ID.
    pub fn id(self) -> NodeId {
        self.id
    }

    /// Gets a reference to the inner [RawNode].
    pub fn get(self) -> &'map RawNode<Kind, Token> {
        self.map
            .get(self.id)
            .expect("node ID should be present in the node map")
    }

    /// Gets the kind of the node.
    pub fn kind(self) -> &'map Kind {
        &self.get().kind
    }

    /// Gets the amount of child nodes.
    pub fn node_count(self) -> usize {
        self.get().nodes.len()
    }

    /// Gets the amount of child tokens.
    pub fn token_count(self) -> usize {
        self.get().tokens.len()
    }

    /// Gets a child node at a specified index.
    pub fn node(self, index: usize) -> Option<Self> {
        self.get().nodes.get(index).map(|x| Self {
            map: self.map,
            id: x.value,
        })
    }

    /// Gets a child token at a specified index.
    pub fn token(self, index: usize) -> Option<&'map Token> {
        self.get().tokens.get(index).map(|x| &x.value)
    }

    /// Gets the child nodes of the node.
    pub fn nodes(self) -> impl Iterator<Item = Self> + Clone {
        self.get().nodes.iter().map(move |x| Self {
            map: self.map,
            id: x.value,
        })
    }

    /// Gets the child tokens of the node.
    pub fn tokens(self) -> impl Iterator<Item = &'map Token> + Clone {
        self.get().tokens.iter().map(|x| &x.value)
    }

    fn ended(
        self,
        node: Option<&'map Indexed<NodeId>>,
        token: Option<&'map Indexed<Token>>,
        end: bool,
    ) -> NodeOrToken<'map, Kind, Token> {
        match (node, token) {
            (None, None) => panic!("node has no children"),

            (Some(node), None) => NodeOrToken::Node(Self {
                map: self.map,
                id: node.value,
            }),

            (None, Some(token)) => NodeOrToken::Token(&token.value),

            (Some(node), Some(token)) => {
                if (node.index < token.index) ^ end {
                    NodeOrToken::Node(Self {
                        map: self.map,
                        id: node.value,
                    })
                } else {
                    NodeOrToken::Token(&token.value)
                }
            }
        }
    }

    /// Gets the first child node or token.
    pub fn first(self) -> NodeOrToken<'map, Kind, Token> {
        let raw = self.get();
        self.ended(raw.nodes.first(), raw.tokens.first(), false)
    }

    /// Gets the last child node or token.
    pub fn last(self) -> NodeOrToken<'map, Kind, Token> {
        let raw = self.get();
        self.ended(raw.nodes.last(), raw.tokens.last(), true)
    }

    /// Gets the children nodes and tokens of the node.
    pub fn children(self) -> impl Iterator<Item = NodeOrToken<'map, Kind, Token>> {
        ChildrenIter {
            node: self,
            node_index: 0,
            token_index: 0,
        }
    }
}

impl<Kind, Token: Spanned> Spanned for SyntaxNode<'_, Kind, Token> {
    fn span(&self) -> TextSpan {
        let first = self.first();
        let last = self.last();
        TextSpan::between(first.span(), last.span())
    }
}

impl<Kind: Serialize, Token: Serialize> Serialize for SyntaxNode<'_, Kind, Token> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let kind = &self.get().kind;
        let children = self.children().collect::<Vec<_>>();

        let mut strct = serializer.serialize_struct("SyntaxNode", 2)?;
        strct.serialize_field("kind", kind)?;
        strct.serialize_field("children", &children)?;
        strct.end()
    }
}

impl<Kind, Token> From<SyntaxNode<'_, Kind, Token>> for NodeId {
    fn from(value: SyntaxNode<'_, Kind, Token>) -> Self {
        value.id
    }
}

impl<Kind, Token> Clone for SyntaxNode<'_, Kind, Token> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Kind, Token> Copy for SyntaxNode<'_, Kind, Token> {}

impl<Kind: PartialEq, Token: PartialEq> PartialEq for SyntaxNode<'_, Kind, Token> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self.map, other.map) && self.get() == other.get()
    }
}

impl<Kind: Eq, Token: Eq> Eq for SyntaxNode<'_, Kind, Token> {}

impl<Kind: Debug, Token: Debug> Debug for SyntaxNode<'_, Kind, Token> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        fmt_node(*self, 0, f)
    }
}

fn fmt_node<Kind: Debug, Token: Debug>(
    node: SyntaxNode<Kind, Token>,
    level: usize,
    f: &mut Formatter<'_>,
) -> std::fmt::Result {
    fn write_indent(level: usize, f: &mut Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            for _ in 0..(level) {
                write!(f, "    ")?;
            }
        }
        Ok(())
    }

    write!(f, "SyntaxNode {:?} (", node.id.0)?;
    node.kind().fmt(f)?;
    write!(f, ") [")?;

    let mut any = false;
    for child in node.children() {
        if any {
            write!(f, ",")?;
            if !f.alternate() {
                write!(f, " ")?;
            }
        }

        any = true;

        if f.alternate() {
            writeln!(f)?;
            write_indent(level + 1, f)?;
        }

        match child {
            NodeOrToken::Node(node) => {
                write!(f, "node ")?;
                fmt_node(node, level + 1, f)?;
            }
            NodeOrToken::Token(token) => {
                write!(f, "token ")?;
                token.fmt(f)?;
            }
        }
    }

    if f.alternate() && any {
        writeln!(f)?;
    }

    write_indent(level, f)?;
    write!(f, "]")?;

    Ok(())
}

/// Either a [SyntaxNode] or a token.
#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(untagged)]
pub enum NodeOrToken<'map, Kind, Token> {
    Node(SyntaxNode<'map, Kind, Token>),
    Token(&'map Token),
}

impl<'map, Kind, Token> NodeOrToken<'map, Kind, Token> {
    pub fn into_node(self) -> Option<SyntaxNode<'map, Kind, Token>> {
        match self {
            Self::Node(node) => Some(node),
            Self::Token(_) => None,
        }
    }

    pub fn into_token(self) -> Option<&'map Token> {
        match self {
            Self::Node(_) => None,
            Self::Token(token) => Some(token),
        }
    }
}

impl<Kind, Token: Spanned> Spanned for NodeOrToken<'_, Kind, Token> {
    fn span(&self) -> TextSpan {
        match self {
            Self::Node(node) => node.span(),
            Self::Token(token) => token.span(),
        }
    }
}

impl<Kind, Token> Clone for NodeOrToken<'_, Kind, Token> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Kind, Token> Copy for NodeOrToken<'_, Kind, Token> {}

#[derive(Debug, Clone)]
struct ChildrenIter<'map, Kind, Token> {
    node: SyntaxNode<'map, Kind, Token>,
    node_index: usize,
    token_index: usize,
}

impl<'map, Kind, Token> Iterator for ChildrenIter<'map, Kind, Token> {
    type Item = NodeOrToken<'map, Kind, Token>;

    fn next(&mut self) -> Option<Self::Item> {
        let map = self.node.map;
        let raw = self.node.get();
        let node = raw.nodes.get(self.node_index);
        let token = raw.tokens.get(self.token_index);
        let index = self.node_index + self.token_index;

        if let Some(node) = node
            && node.index == index
        {
            self.node_index += 1;
            return Some(NodeOrToken::Node(SyntaxNode {
                map,
                id: node.value,
            }));
        }

        if let Some(token) = token
            && token.index == index
        {
            self.token_index += 1;
            return Some(NodeOrToken::Token(&token.value));
        }

        None
    }
}

/// Builder for constructing new [RawNode]s.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NodeBuilder<Kind, Token> {
    kind: Kind,
    nodes: Vec<Indexed<NodeId>>,
    tokens: Vec<Indexed<Token>>,
    index: usize,
}

impl<Kind, Token> NodeBuilder<Kind, Token> {
    pub fn new(kind: Kind) -> Self {
        Self {
            kind,
            nodes: Vec::new(),
            tokens: Vec::new(),
            index: 0,
        }
    }

    pub fn add_node(&mut self, node: impl Into<NodeId>) -> &mut Self {
        self.nodes.push(Indexed {
            value: node.into(),
            index: self.index,
        });
        self.index += 1;

        self
    }

    pub fn add_nodes(&mut self, nodes: impl IntoIterator<Item = impl Into<NodeId>>) -> &mut Self {
        for node in nodes {
            self.add_node(node);
        }

        self
    }

    pub fn try_add_node(&mut self, node: Option<impl Into<NodeId>>) -> &mut Self {
        if let Some(node) = node {
            self.add_node(node);
        }

        self
    }

    pub fn add_token(&mut self, token: Token) -> &mut Self {
        self.tokens.push(Indexed {
            value: token,
            index: self.index,
        });
        self.index += 1;

        self
    }

    pub fn add_tokens(&mut self, tokens: impl IntoIterator<Item = Token>) -> &mut Self {
        for token in tokens {
            self.add_token(token);
        }

        self
    }

    pub fn try_add_token(&mut self, token: Option<Token>) -> &mut Self {
        if let Some(token) = token {
            self.add_token(token);
        }

        self
    }

    const EMPTY_MSG: &str = "builder should not be empty when finished";

    /// Finishes the builder and returns a [RawNode].
    pub fn finish_raw_opt(self) -> Option<RawNode<Kind, Token>> {
        if self.nodes.is_empty() && self.tokens.is_empty() {
            None
        } else {
            Some(RawNode {
                kind: self.kind,
                nodes: self.nodes,
                tokens: self.tokens,
            })
        }
    }

    /// Finishes the builder and returns a [RawNode].
    pub fn finish_raw(self) -> RawNode<Kind, Token> {
        self.finish_raw_opt().expect(Self::EMPTY_MSG)
    }

    /// Finishes the builder, inserts the built node into a node map,
    /// then returns a [SyntaxNode] wrapping the map and newly created node ID.
    pub fn finish_opt<'map>(
        self,
        map: &'map mut NodeMap<Kind, Token>,
    ) -> Option<SyntaxNode<'map, Kind, Token>> {
        let raw = self.finish_raw_opt()?;
        let id = map.insert(raw);
        Some(SyntaxNode { id, map })
    }

    /// Finishes the builder, inserts the built node into a node map,
    /// then returns a [SyntaxNode] wrapping the map and newly created node ID.
    pub fn finish<'map>(
        self,
        map: &'map mut NodeMap<Kind, Token>,
    ) -> SyntaxNode<'map, Kind, Token> {
        self.finish_opt(map).expect(Self::EMPTY_MSG)
    }
}

#[macro_export]
macro_rules! node_child {
    ($builder:expr, node $node:expr) => {
        $builder.add_node($node)
    };
    ($builder:expr, token $token:expr) => {
        $builder.add_token($token)
    };
}

#[macro_export]
macro_rules! make_node {
    ($kind:expr; $($child:tt $expr:expr),+) => {
        {
            let mut builder = $crate::syntax::tree::NodeBuilder::new($kind);
            $(
                $crate::node_child!(builder, $child $expr);
            )*
            builder
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn finished_empty_returns_none() {
        let node = NodeBuilder::<(), ()>::new(()).finish_raw_opt();

        assert_eq!(node, None);
    }

    #[test]
    fn children() {
        let mut map = SlotMap::with_key();

        let node = make_node!(
            621;
            token 1,
            token 2,
            node make_node!(3; token 69).finish(&mut map),
            token 4,
            node make_node!(5; token 420).finish(&mut map),
            token 6
        )
        .finish(&mut map);

        let mut children = node.children();

        assert_eq!(*children.next().unwrap().into_token().unwrap(), 1);
        assert_eq!(*children.next().unwrap().into_token().unwrap(), 2);
        assert_eq!(*children.next().unwrap().into_node().unwrap().kind(), 3);
        assert_eq!(*children.next().unwrap().into_token().unwrap(), 4);
        assert_eq!(*children.next().unwrap().into_node().unwrap().kind(), 5);
        assert_eq!(*children.next().unwrap().into_token().unwrap(), 6);
        assert_eq!(children.next(), None);
    }

    #[test]
    fn first_last() {
        let mut map = SlotMap::with_key();

        let node = make_node!(
            0;
            node make_node!(1; token 0).finish(&mut map),
            token 0,
            node make_node!(2; token 0).finish(&mut map)
        )
        .finish(&mut map);

        assert_eq!(node.first().into_node().unwrap().kind(), &1);
        assert_eq!(node.last().into_node().unwrap().kind(), &2);

        let node = make_node!(
            0;
            token 1,
            node make_node!(0; token 0).finish(&mut map),
            token 2
        )
        .finish(&mut map);

        assert_eq!(node.first().into_token().unwrap(), &1);
        assert_eq!(node.last().into_token().unwrap(), &2);
    }
}
