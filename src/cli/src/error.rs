use struktur::diagnostic::Diagnostic;

pub enum Error {
    Diagnostic(Diagnostic),
    Other(anyhow::Error),
}

impl Error {
    pub fn from_any<E: std::error::Error + Send + Sync + 'static>(error: E) -> Self {
        Self::Other(anyhow::Error::from_boxed(Box::new(error)))
    }
}

impl From<Diagnostic> for Error {
    fn from(value: Diagnostic) -> Self {
        Self::Diagnostic(value)
    }
}

impl From<anyhow::Error> for Error {
    fn from(value: anyhow::Error) -> Self {
        Self::Other(value)
    }
}

impl From<std::io::Error> for Error {
    fn from(value: std::io::Error) -> Self {
        Self::from_any(value)
    }
}

impl From<serde_yml::Error> for Error {
    fn from(value: serde_yml::Error) -> Self {
        Self::from_any(value)
    }
}
