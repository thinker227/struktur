//! Text sources and a cache for them.
//!
//! The main purpose of this module is to provide an implementation of [ariadne::Cache] in the form of [SourceProject].
//! [SourceProject] is the principal consumer and distributor of [SourceContext]s, which are used throughout the compiler
//! to identify sources.

use std::{fmt::Display, path::PathBuf};

use ariadne::Cache;
use slotmap::{SlotMap, new_key_type};

use crate::text::{TextLocation, TextSpan};

/// The text of a source.
pub type SourceText = ariadne::Source<String>;

/// The name of a source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceName {
    File(PathBuf),
    InMemory { name: String },
}

impl Display for SourceName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SourceName::File(path) => write!(f, "{}", path.as_os_str().to_string_lossy()),
            SourceName::InMemory { name } => write!(f, "{name}"),
        }
    }
}

/// A piece of text with some origin—its source.
/// Additionally present inside a [SourceProject].
///
/// Sources have a string of text, a name, and a key into the [SourceProject] it is present in.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Source {
    key: SourceContext,
    name: SourceName,
    text: SourceText,
}

impl Source {
    /// Gets the key for the source.
    pub fn key(&self) -> SourceContext {
        self.key
    }

    /// The name of the source.
    pub fn name(&self) -> &SourceName {
        &self.name
    }

    /// The text string of the source.
    pub fn text(&self) -> &SourceText {
        &self.text
    }
}

/// Context about the source of a piece of text,
/// mainly consumed and distributed by a [SourceProject].
///
/// Can be conceptualized as being equivalent to a file handle,
/// although the source doesn't have to be a physical location like a file on disk.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SourceContext(Key);

new_key_type! {
    struct Key;
}

impl SourceContext {
    /// Attaches the context to a [TextSpan].
    pub fn with_span(self, span: TextSpan) -> TextLocation {
        TextLocation {
            span,
            context: self,
        }
    }
}

/// A 'project' containing multiple sources.
///
/// Provides an implementation of [ariadne::Cache].
#[derive(Debug, Clone)]
pub struct SourceProject {
    sources: SlotMap<Key, Source>,
}

impl SourceProject {
    /// Creates a new empty [SourceProject].
    pub fn new() -> Self {
        Self {
            sources: SlotMap::with_key(),
        }
    }

    /// Adds a new source from a name and the source text.
    pub fn add(&mut self, name: SourceName, text: String) -> &Source {
        let key = self.sources.insert_with_key(|key| Source {
            key: SourceContext(key),
            name,
            text: text.into(),
        });

        self.sources.get(key).unwrap()
    }

    /// Gets the [Source] for a key.
    pub fn get(&self, key: SourceContext) -> Option<&Source> {
        self.sources.get(key.0)
    }

    /// Looks up the text at a [TextLocation] in the project.
    ///
    /// Returns [None] if the context of the location is not in the project.
    pub fn lookup(&self, location: TextLocation) -> Option<&str> {
        let source = self.sources.get(location.context.0)?;
        let text = &source.text().text()[location.span];
        Some(text)
    }
}

impl Default for SourceProject {
    fn default() -> Self {
        Self::new()
    }
}

impl Cache<SourceContext> for SourceProject {
    type Storage = String;

    fn fetch(&mut self, id: &SourceContext) -> Result<&SourceText, impl std::fmt::Debug> {
        self.get(*id)
            .map(|source| source.text())
            .ok_or("invalid key for source project")
    }

    fn display<'a>(&self, id: &'a SourceContext) -> Option<impl Display + 'a> {
        let name = self
            .get(*id)
            .expect("key should be valid when display is called")
            .name()
            .to_string();

        Some(name)
    }
}
