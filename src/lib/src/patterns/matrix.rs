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
    /// Constructs a new matrix with no rows from an occurence vector.
    pub fn new(occurs: Vec<Occur>) -> Self {
        Self {
            patterns: Vec::new(),
            occurs,
            actions: Vec::new()
        }
    }

    /// Borrows the matrix as a [SubMatrix].
    #[inline]
    pub fn borrow(&self) -> SubMatrix<'_> {
        SubMatrix {
            patterns: &self.patterns,
            occurs: &self.occurs,
            actions: &self.actions,
            col_from_start: 0,
            col_from_end: 0
        }
    }

    /// Adds a row to the matrix. The amount of patterns in the row
    /// has to be the same as the length of the occurence vector.
    pub fn push_row(&mut self, action: Action, patterns: Vec<Pat>) {
        assert_eq!(patterns.len(), self.occurs.len());

        self.actions.push(action);
        self.patterns.extend_from_slice(&patterns);
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
        if n_a == n_b {
            return;
        }

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
    col_from_start: usize,
    col_from_end: usize,
}

impl SubMatrix<'_> {
    pub fn to_owned(self) -> Matrix {
        Matrix {
            patterns: self.patterns.to_owned(),
            occurs: self.occurs.to_owned(),
            actions: self.actions.to_owned()
        }
    }

    /// Slices the rows of the matrix.
    pub fn slice_rows<R: RangeBounds<usize>>(&self, range: R) -> Self {
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

        let height = self.height();
        assert!(start < height);
        assert!(end < height);
        assert!(end >= start);

        let from = self.real_width() * start;
        let to = self.real_width() * end;

        Self {
            patterns: &self.patterns[from..to],
            occurs: self.occurs,
            actions: &self.actions[start..end],
            col_from_start: self.col_from_start,
            col_from_end: self.col_from_end
        }
    }

    /// Slices the columns of the matrix.
    pub fn slice_columns<R: RangeBounds<usize>>(&self, range: R) -> Self {
        let start = match range.start_bound() {
            Bound::Included(n) => *n,
            Bound::Excluded(n) => *n + 1,
            Bound::Unbounded => 0
        };
        let end = match range.end_bound() {
            Bound::Included(n) => *n + 1,
            Bound::Excluded(n) => *n,
            Bound::Unbounded => self.width()
        };

        let width = self.width();
        assert!(start < width);
        assert!(end < width);
        assert!(end >= start);

        Self {
            occurs: self.occurs,
            actions: self.actions,
            patterns: self.patterns,
            col_from_start: self.col_from_start + start,
            col_from_end: self.col_from_end + (width - end)
        }
    }

    fn real_width(&self) -> usize {
        self.occurs.len()
    }

    #[inline]
    pub fn width(&self) -> usize {
        self.real_width() - self.col_from_start - self.col_from_end
    }

    #[inline]
    pub fn height(&self) -> usize {
        self.actions.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.width() == 0
    }

    pub fn pattern(&self, n: usize, m: usize) -> &Pat {
        let index = self.width() * m + n + self.col_from_start;
        &self.patterns[index]
    }

    /// Gets a column of the matrix.
    pub fn column(&self, n: usize) -> Column<'_> {
        Column {
            mat: *self,
            n: n + self.col_from_start
        }
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
        let index = self.mat.real_width() * m + self.n;
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
            step: self.mat.real_width(),
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
        assert!(n < self.mat.width());

        let index = self.mat.height() * self.m + n + self.mat.col_from_start;
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
            start: self.m * self.mat.real_width() + self.mat.col_from_start,
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

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper macro to assert the items yielded by an iterator.
    macro_rules! assert_iter {
        ($iter:expr; $($value:expr),*) => {
            {
                let mut iter = IntoIterator::into_iter($iter);
                $(
                    assert_eq!(iter.next(), Some($value));
                )*
                assert_eq!(iter.next(), None);
            }
        };
    }

    #[test]
    fn swap() {
        let mut matrix = Matrix::new(vec![Occur::Identity; 2]);
        matrix.push_row(
            Action { case_index: 0 },
            vec![Pat::Number(0), Pat::Number(1)]
        );
        matrix.push_row(
            Action { case_index: 1 },
            vec![Pat::Number(2), Pat::Number(3)]
        );

        matrix.swap(0, 1);

        let matrix = matrix.borrow();

        assert_iter![
            matrix.row(0);
            &Pat::Number(1),
            &Pat::Number(0)
        ];
        assert_iter![
            matrix.row(1);
            &Pat::Number(3),
            &Pat::Number(2)
        ];
    }

    #[test]
    fn slice_rows() {
        let mut matrix = Matrix::new(vec![Occur::Identity; 2]);
        matrix.push_row(
            Action { case_index: 0 },
            vec![Pat::Number(0), Pat::Number(1)]
        );
        matrix.push_row(
            Action { case_index: 1 },
            vec![Pat::Number(2), Pat::Number(3)]
        );
        matrix.push_row(
            Action { case_index: 2 },
            vec![Pat::Number(4), Pat::Number(5)]
        );
        matrix.push_row(
            Action { case_index: 3 },
            vec![Pat::Number(6), Pat::Number(7)]
        );
        matrix.push_row(
            Action { case_index: 4 },
            vec![Pat::Number(8), Pat::Number(9)]
        );

        let matrix = matrix.borrow().slice_rows(1..=3);

        assert_iter![
            matrix.row(0);
            &Pat::Number(2),
            &Pat::Number(3)
        ];
        assert_iter![
            matrix.row(1);
            &Pat::Number(4),
            &Pat::Number(5)
        ];
        assert_iter![
            matrix.row(2);
            &Pat::Number(6),
            &Pat::Number(7)
        ];

        assert_iter![
            matrix.column(0);
            &Pat::Number(2),
            &Pat::Number(4),
            &Pat::Number(6)
        ];
        assert_iter![
            matrix.column(1);
            &Pat::Number(3),
            &Pat::Number(5),
            &Pat::Number(7)
        ];

        let matrix = matrix.slice_rows(1..=1);

        assert_iter![
            matrix.row(0);
            &Pat::Number(4),
            &Pat::Number(5)
        ];

        assert_iter![
            matrix.column(0);
            &Pat::Number(4)
        ];
        assert_iter![
            matrix.column(1);
            &Pat::Number(5)
        ];
    }

    #[test]
    fn slice_cols() {
        let mut matrix = Matrix::new(vec![Occur::Identity; 5]);
        matrix.push_row(
            Action { case_index: 0 },
            vec![Pat::Number(1), Pat::Number(2), Pat::Number(3), Pat::Number(4), Pat::Number(5)]
        );
        matrix.push_row(
            Action { case_index: 1 },
            vec![Pat::Number(6), Pat::Number(7), Pat::Number(8), Pat::Number(9), Pat::Number(10)]
        );

        let matrix = matrix.borrow().slice_columns(1..=3);

        assert_iter![
            matrix.row(0);
            &Pat::Number(2),
            &Pat::Number(3),
            &Pat::Number(4)
        ];
        assert_iter![
            matrix.row(1);
            &Pat::Number(7),
            &Pat::Number(8),
            &Pat::Number(9)
        ];

        assert_iter![
            matrix.column(0);
            &Pat::Number(2),
            &Pat::Number(7)
        ];
        assert_iter![
            matrix.column(1);
            &Pat::Number(3),
            &Pat::Number(8)
        ];
        assert_iter![
            matrix.column(2);
            &Pat::Number(4),
            &Pat::Number(9)
        ];

        let matrix = matrix.slice_columns(1..=1);

        assert_iter!(
            matrix.row(0);
            &Pat::Number(3)
        );
        assert_iter!(
            matrix.row(1);
            &Pat::Number(8)
        );

        assert_iter!(
            matrix.column(0);
            &Pat::Number(3),
            &Pat::Number(8)
        );
    }
}
