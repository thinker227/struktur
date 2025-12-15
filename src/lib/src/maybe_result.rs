use std::{convert::Infallible, ops::{ControlFlow, FromResidual, Try}};

/// A three-state [Result], effectively an `Option<Result<T, E>>` or `Result<Option<T>, E>`.
///
/// Can be used with the `?` operator on both `Result<T, E>` and `Option<T>` values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MaybeResult<T, E> {
    Ok(T),
    Err(E),
    None,
}

impl<T, E> MaybeResult<T, E> {
    /// Turns the `MaybeResult<T, E>` into a `Result<Option<T>, E>`.
    pub fn into_result(self) -> Result<Option<T>, E> {
        match self {
            MaybeResult::Ok(x) => Ok(Some(x)),
            MaybeResult::Err(e) => Err(e),
            MaybeResult::None => Ok(None)
        }
    }

    /// Turns the `MaybeResult<T, E>` into a `Option<Result<T, E>>`.
    pub fn into_option(self) -> Option<Result<T, E>> {
        match self {
            MaybeResult::Ok(x) => Some(Ok(x)),
            MaybeResult::Err(e) => Some(Err(e)),
            MaybeResult::None => None
        }
    }

    /// Unwraps the `MaybeResult<T, E>` into a `Result<T, E>`,
    /// using a function to provide the error if the value is `None`.
    pub fn unwrap_or_err(self, f: impl FnOnce() -> E) -> Result<T, E> {
        match self {
            MaybeResult::Ok(x) => Ok(x),
            MaybeResult::Err(e) => Err(e),
            MaybeResult::None => Err(f())
        }
    }

    /// Unwraps the `MaybeResult<T, E>` into an `Option<T>`.
    pub fn unwrap_or_none(self) -> Option<T> {
        match self {
            MaybeResult::Ok(x) => Some(x),
            MaybeResult::Err(_) => None,
            MaybeResult::None => None
        }
    }

    /// Maps the `T` of the `MaybeResult<T, E>` into a `U` if it is present.
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> MaybeResult<U, E> {
        match self {
            MaybeResult::Ok(x) => MaybeResult::Ok(f(x)),
            MaybeResult::Err(e) => MaybeResult::Err(e),
            MaybeResult::None => MaybeResult::None
        }
    }
}

impl<T, E, F: Into<E>> From<Result<T, F>> for MaybeResult<T, E> {
    fn from(value: Result<T, F>) -> Self {
        match value {
            Ok(x) => MaybeResult::Ok(x),
            Err(e) => MaybeResult::Err(e.into())
        }
    }
}

impl<T, E> From<Option<T>> for MaybeResult<T, E> {
    fn from(value: Option<T>) -> Self {
        match value {
            Some(x) => MaybeResult::Ok(x),
            None => MaybeResult::None
        }
    }
}

impl<T, E> FromResidual<Option<Infallible>> for MaybeResult<T, E> {
    fn from_residual(_: Option<Infallible>) -> Self {
        Self::None
    }
}

impl<T, E> FromResidual<Result<Infallible, E>> for MaybeResult<T, E> {
    fn from_residual(residual: Result<Infallible, E>) -> Self {
        let Err(e) = residual;
        Self::Err(e)
    }
}

impl<T, E> FromResidual<MaybeResult<Infallible, E>> for MaybeResult<T, E> {
    fn from_residual(residual: MaybeResult<Infallible, E>) -> Self {
        match residual {
            MaybeResult::Err(e) => Self::Err(e),
            MaybeResult::None => Self::None
        }
    }
}

impl<T, E> Try for MaybeResult<T, E> {
    type Output = T;

    type Residual = MaybeResult<Infallible, E>;

    fn from_output(output: Self::Output) -> Self {
        Self::Ok(output)
    }

    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            MaybeResult::Ok(x) => ControlFlow::Continue(x),
            MaybeResult::Err(e) => ControlFlow::Break(MaybeResult::Err(e)),
            MaybeResult::None => ControlFlow::Break(MaybeResult::None)
        }
    }
}
