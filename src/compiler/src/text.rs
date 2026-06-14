//! Types for working with text.

use crate::sources::SourceContext;
use std::{
    fmt::Display,
    ops::{Index, Range},
};

use ariadne::Span;
use serde::{Serialize, Serializer};

/// A span in a piece of text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TextSpan {
    start: usize,
    length: usize,
}

impl TextSpan {
    /// Constructs a new [TextSpan] from a start and a length.
    pub fn new(start: usize, length: usize) -> Self {
        Self { start, length }
    }

    /// Constructs a new [TextSpan] from a start and end.
    pub fn from_bounds(start: usize, end: usize) -> Option<Self> {
        (start <= end).then(|| Self::new(start, end - start))
    }

    /// Constructs a new [TextSpan] that spans from the start of one [TextSpan] to the end of another.
    pub fn between(a: impl Into<Self>, b: impl Into<Self>) -> Self {
        let a = a.into();
        let b = b.into();

        let offset = usize::min(a.start, b.start);
        let end = usize::max(a.end(), b.end());

        Self::from_bounds(offset, end).unwrap()
    }

    /// Constructs a new [TextSpan] that has a length of 0.
    pub fn empty(at: usize) -> Self {
        Self::new(at, 0)
    }

    /// The start position of the span.
    pub fn start(self) -> usize {
        self.start
    }

    /// The end position of the span.
    pub fn end(self) -> usize {
        self.start + self.length
    }

    /// The length of the span.
    pub fn len(self) -> usize {
        self.length
    }

    /// Whether the span is empty.
    pub fn is_empty(self) -> bool {
        self.length == 0
    }

    /// Attaches a [SourceContext] as context to the span.
    pub fn with_context(self, context: SourceContext) -> TextLocation {
        TextLocation {
            span: self,
            context,
        }
    }
}

impl From<Range<usize>> for TextSpan {
    fn from(value: Range<usize>) -> Self {
        Self::from_bounds(value.start, value.end).expect("length of range cannot be negative")
    }
}

impl Index<TextSpan> for str {
    type Output = str;

    fn index(&self, index: TextSpan) -> &Self::Output {
        &self[index.start()..index.end()]
    }
}

impl Display for TextSpan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start(), self.end())
    }
}

impl Serialize for TextSpan {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.to_string())
    }
}

/// Trait for types which have a [TextSpan] associated with them.
pub trait Spanned {
    /// Gets the [TextSpan] for the value.
    fn span(&self) -> TextSpan;
}

impl Spanned for TextSpan {
    fn span(&self) -> TextSpan {
        *self
    }
}

/// A [TextSpan] with added [SourceContext] about the origin of the span.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TextLocation {
    pub span: TextSpan,
    pub context: SourceContext,
}

impl Span for TextLocation {
    type SourceId = SourceContext;

    fn source(&self) -> &Self::SourceId {
        &self.context
    }

    fn start(&self) -> usize {
        self.span.start()
    }

    fn end(&self) -> usize {
        self.span.end()
    }
}
