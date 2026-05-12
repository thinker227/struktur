//! Type checking and inference.
//!
//! The algorithm used for type inference is [Algorithm-J](https://en.wikipedia.org/wiki/Hindley-Milner_type_system#Algorithm_J)
//! with bidirectionality tacked on, with the implementation heavily referencing
//! [brendanzab's Language Garden project](https://github.com/brendanzab/language-garden/blob/main/scraps/check_poly_algorithm_j.ml)
//! and [an example by jfetcher](https://github.com/jfecher/algorithm-j).
//!
//! Most notably, Algorithm-J uses mutable unification variables instead of a substitution map,
//! so [MetaVar] is implemented using interior mutability.

mod context;
