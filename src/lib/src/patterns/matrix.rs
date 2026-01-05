use std::ops::{Bound, RangeBounds};

use super::{Pat, Occur, Action};

/// An owned matrix mapping a sequence of patterns into a grid
/// with an occurence vector and action vector.
///
/// Indices into the matrix are denoted `n` for the column and `m` for the row.
#[derive(Debug, Clone)]
pub struct Matrix {
    patterns: Vec<Pat>,
    occurs: Vec<Occur>,
    actions: Vec<Action>,
}

impl Matrix {
    pub fn new(patterns: Vec<Pat>, occurs: Vec<Occur>, actions: Vec<Action>) -> Self {
        assert_eq!(patterns.len(), occurs.len() * actions.len());

        Self {
            patterns,
            occurs,
            actions
        }
    }

    /// Borrows the matrix as a [SubMatrix].
    #[inline]
    pub fn borrow(&self) -> SubMatrix<'_> {
        SubMatrix {
            patterns: &self.patterns,
            occurs: &self.occurs,
            actions: &self.actions
        }
    }

    /// Specializes every pattern in a column by replacing it
    /// with a set of new patterns returned by a function invoked with the pattern.
    /// Additionally takes a vector of occurences for each of the newly added columns.
    ///
    /// Every set of new patterns returned by the function has to be the same length
    /// as the vector of new occurences.
    ///
    /// Returns a new owned matrix.
    pub fn specialize(&mut self, n: usize, occurs: Vec<Occur>, f: impl Fn(&Pat) -> Option<Vec<Pat>>) {
        let len = occurs.len();
        let width = self.width();

        self.occurs.splice(n..n+1, occurs);

        let mut i = 0;
        while i < self.height() {
            let pat = &self.patterns[(width + len) * i + n];
            if let Some(spec) = f(pat) {
                if spec.len() != len {
                    panic!("inconsistent length of specialized patterns, expected all patterns to be of length {len}")
                }

                let index = (width + spec.len()) * i + n;
                self.patterns.splice(index..index+1, spec);

                i += 1;
            } else {
                let index = (width + len) * i + n;
                self.patterns.drain(index..index+width);
                self.actions.remove(i);
            }
        }
    }

    /// Swaps two columns in the matrix.
    ///
    /// Returns a new owned matrix.
    pub fn swap(&mut self, n_a: usize, n_b: usize) {
        self.occurs.swap(n_a, n_b);

        for i in 0..self.height() {
            let base = self.width() * i;
            self.patterns.swap(base + n_a, base + n_b);
        }
    }

    #[inline]
    pub fn width(&self) -> usize {
        self.borrow().width()
    }

    #[inline]
    pub fn height(&self) -> usize {
        self.borrow().height()
    }
}

/// A borrowed [Matrix].
///
/// Since a [SubMatrix] borrows its data, it can more easily be sliced
/// without having to mutate the original matrix. It also provides views over the
/// data using [column](Self::column) and [row](Self::row).
#[derive(Debug, Clone, Copy)]
pub struct SubMatrix<'mat> {
    patterns: &'mat [Pat],
    occurs: &'mat [Occur],
    actions: &'mat [Action],
}

impl SubMatrix<'_> {
    pub fn to_matrix(&self) -> Matrix {
        Matrix {
            patterns: self.patterns.to_owned(),
            occurs: self.occurs.to_owned(),
            actions: self.actions.to_owned()
        }
    }

    /// Slices the rows of the matrix.
    pub fn slice<R: RangeBounds<usize>>(&self, range: R) -> Self {
        let start = match range.start_bound() {
            Bound::Included(n) => *n,
            Bound::Excluded(n) => *n + 1,
            Bound::Unbounded => 0
        };
        let end = match range.end_bound() {
            Bound::Included(n) => *n + 1,
            Bound::Excluded(n) => *n,
            Bound::Unbounded => self.height()
        };

        let from = self.width() * start;
        let to = self.width() * end;

        Self {
            patterns: &self.patterns[from..to],
            occurs: &self.occurs,
            actions: &self.actions[start..end]
        }
    }

    #[inline]
    pub fn width(&self) -> usize {
        self.occurs.len()
    }

    #[inline]
    pub fn height(&self) -> usize {
        self.actions.len()
    }

    pub fn pattern(&self, n: usize, m: usize) -> &Pat {
        let index = self.width() * m + n;
        &self.patterns[index]
    }

    /// Gets a column of the matrix.
    pub fn column(&self, n: usize) -> Column<'_> {
        Column { mat: *self, n }
    }

    /// Gets a row of the matrix.
    pub fn row(&self, m: usize) -> Row<'_> {
        Row { mat: *self, m }
    }
}

/// A column of a pattern matrix.
#[derive(Debug, Clone, Copy)]
pub struct Column<'mat> {
    mat: SubMatrix<'mat>,
    n: usize,
}

impl<'mat> Column<'mat> {
    pub fn occur(&self) -> &'mat Occur {
        &self.mat.occurs[self.n]
    }

    pub fn pattern(&self, m: usize) -> &'mat Pat {
        let index = self.mat.width() * m + self.n;
        &self.mat.patterns[index]
    }

    pub fn len(&self) -> usize {
        self.mat.height()
    }
}

impl<'mat> IntoIterator for Column<'mat> {
    type Item = &'mat Pat;

    type IntoIter = Iter<'mat>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            mat: self.mat,
            start: self.n,
            step: self.mat.width(),
            len: self.len(),
            i: 0
        }
    }
}

/// A row of a pattern matrix.
#[derive(Debug, Clone, Copy)]
pub struct Row<'mat> {
    mat: SubMatrix<'mat>,
    m: usize,
}

impl<'mat> Row<'mat> {
    pub fn action(&self) -> &'mat Action {
        &self.mat.actions[self.m]
    }

    pub fn pattern(&self, n: usize) -> &'mat Pat {
        let index = self.mat.height() * self.m + n;
        &self.mat.patterns[index]
    }

    pub fn len(&self) -> usize {
        self.mat.width()
    }
}

impl<'mat> IntoIterator for Row<'mat> {
    type Item = &'mat Pat;

    type IntoIter = Iter<'mat>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            mat: self.mat,
            start: self.m * self.mat.width(),
            step: 1,
            len: self.len(),
            i: 0
        }
    }
}

/// An iterator over either the columns or rows of a pattern matrix.
#[derive(Debug, Clone)]
pub struct Iter<'mat> {
    mat: SubMatrix<'mat>,
    start: usize,
    step: usize,
    len: usize,
    i: usize,
}

impl<'mat> Iterator for Iter<'mat> {
    type Item = &'mat Pat;

    fn next(&mut self) -> Option<Self::Item> {
        if self.i < self.len {
            let index = self.start + self.step * self.i;
            self.i += 1;
            Some(&self.mat.patterns[index])
        } else {
            None
        }
    }
}
