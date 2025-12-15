use std::fmt::Display;

use miette::SourceSpan;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TextSpan {
    offset: usize,
    length: usize,
}

impl TextSpan {
    pub fn new(offset: usize, length: usize) -> Self {
        Self { offset, length }
    }

    pub fn from_offset_end(offset: usize, end: usize) -> Option<Self> {
        (offset <= end).then(|| Self::new(offset, end - offset))
    }

    pub fn between(a: impl Into<TextSpan>, b: impl Into<TextSpan>) -> Self {
        let a = a.into();
        let b = b.into();

        let offset = usize::min(a.offset, b.offset);
        let end = usize::max(a.end(), b.end());

        Self::from_offset_end(offset, end).unwrap()
    }

    pub fn empty(offset: usize) -> Self {
        Self::new(offset, 0)
    }

    pub fn offset(&self) -> usize {
        self.offset
    }

    pub fn len(&self) -> usize {
        self.length
    }

    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    pub fn end(&self) -> usize {
        self.offset + self.length
    }
}

impl From<TextSpan> for SourceSpan {
    fn from(value: TextSpan) -> Self {
        (value.offset, value.length).into()
    }
}

impl From<SourceSpan> for TextSpan {
    fn from(value: SourceSpan) -> Self {
        Self::new(value.offset(), value.len())
    }
}

impl Display for TextSpan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.offset, self.offset + self.length)
    }
}
