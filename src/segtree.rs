//! SegTree: Segment Tree

// TODO: Use internal ceil_pow2: how to depend on and expand it?
fn ceil_pow2(_: usize) -> usize {
    todo!()
}

trait Monoid {
    type ValueType;
    fn op(lhs: Self::ValueType, rhs: Self::ValueType) -> Self::ValueType;
    fn e() -> Self::ValueType;
}

struct SegTree<M: Monoid> {
    // `_n` in the original
    data_len: usize,

    // `log` in the original
    log_data_size: usize,

    // `size` in the original
    // WARNING: the actual size of tree (len of data) is 2 * tree_size.
    tree_size: usize,

    // `d` in the original
    data: Vec<M::ValueType>,
}

macro_rules! assert_index_bounds {
    ($index:expr, $len:expr) => {
        assert!(
            $index < $len,
            "index out of bounds: the len is {} but the index is {}",
            $len,
            $index
        );
    };
}

impl<M: Monoid> SegTree<M>
where
    M::ValueType: Clone,
{
    pub fn new() -> Self {
        Self::with_len(0)
    }

    pub fn with_len(len: usize) -> Self {
        Self::from_slice(&*vec![M::e(); len])
    }

    pub fn from_slice(slice: &[M::ValueType]) -> Self {
        let data_len = slice.len();
        let log_data_size = ceil_pow2(data_len);
        let tree_size = 1 << log_data_size;
        let mut data = vec![M::e(); 2 * tree_size];

        for i in 0..data_len {
            // SAFETY: `data_len < tree_size` so `tree_size + i < 2 * tree_size`
            unsafe {
                *data.get_unchecked_mut(tree_size + i) = slice.get_unchecked(i).clone();
            }
        }

        let mut res = Self {
            data_len,
            log_data_size,
            tree_size,
            data,
        };

        for i in (1..data_len).rev() {
            res.update(i)
        }

        res
    }

    pub fn set(&mut self, mut index: usize, value: M::ValueType) {
        assert_index_bounds!(index, self.data_len);

        index += self.data_len;

        // SAFETY: index is already checked.
        unsafe {
            *self.data.get_unchecked_mut(index) = value;
        }

        for i in 1..=self.log_data_size {
            self.update(index >> i);
        }
    }

    pub fn get(&self, mut index: usize) -> M::ValueType {
        assert_index_bounds!(index, self.data_len);

        index += self.data_len;

        // SAFETY: index is already checked.
        unsafe { self.data.get_unchecked(index).clone() }
    }

    pub fn prod(&self, left: usize, right: usize) -> M::ValueType {
        assert_index_bounds!(left, self.data_len);
        assert_index_bounds!(right, self.data_len);
        assert!(
            left <= right,
            "left index {} is greater than right index {}",
            left,
            right
        );

        // to improve readability I use `left` and `right` in the arguments but
        // `l` and `r` is more easy to read in the body of the algorithm...
        let mut l = left;
        let mut r = right;
        let mut sml = M::e();
        let mut smr = M::e();

        while l < r {
            if l & 1 != 0 {
                // SAFETY: the binary tree structure of self.data
                debug_assert!(l < self.data.len());
                sml = M::op(sml, unsafe { self.data.get_unchecked(l).clone() });
                l += 1;
            }

            if r & 1 != 0 {
                r -= 1;
                // SAFETY: the binary tree structure of self.data
                debug_assert!(r < self.data.len());
                smr = M::op(smr, unsafe { self.data.get_unchecked(r).clone() })
            }

            l >>= 1;
            r >>= 1;
        }

        M::op(sml, smr)
    }

    pub fn all_prod(&self) -> M::ValueType {
        // SAFETY: we have at least two elements in the data even if we
        // initialized the tree of size 0.
        debug_assert!(self.data.len() >= 2);
        unsafe { self.data.get_unchecked(1).clone() }
    }

    pub fn max_right<F>(&self, left: usize, mut pred: F) -> usize
    where
        F: FnMut(M::ValueType) -> bool,
    {
        // SAFETY for all unsafes: binary tree structure of self.data

        assert_index_bounds!(left, self.data_len);
        assert!(
            pred(M::e()),
            "the predicate must return `true` for the identity",
        );

        if left == self.data_len {
            return self.data_len;
        }

        let mut l = left;
        l += self.data_len;
        let mut sm = M::e();

        loop {
            while l % 2 == 0 {
                l >>= 1;
            }

            debug_assert!(l < self.data.len());
            if !pred(M::op(sm.clone(), unsafe {
                self.data.get_unchecked(l).clone()
            })) {
                while l < self.tree_size {
                    // this verbosity is intentional: for correspondence with
                    // the `min_left()`.
                    l = 2 * l;
                    debug_assert!(l < self.data.len());
                    if pred(M::op(sm.clone(), unsafe {
                        self.data.get_unchecked(l).clone()
                    })) {
                        debug_assert!(l < self.data.len());
                        sm = M::op(sm, unsafe { self.data.get_unchecked(l).clone() });
                        l += 1;
                    }
                }

                return l - self.tree_size;
            }
            debug_assert!(l < self.data.len());
            sm = M::op(sm, unsafe { self.data.get_unchecked(l).clone() });
            l += 1;

            // SAFETY: the max length of the Vec is (currently) isize::MAX so
            // valid index must be less than isize::MAX.
            let l = l as isize;
            if l & -l == 1 {
                break;
            }
        }

        self.data_len
    }

    pub fn min_left<F>(&self, right: usize, mut pred: F) -> usize
    where
        F: FnMut(M::ValueType) -> bool,
    {
        assert_index_bounds!(right, self.data_len);
        assert!(
            pred(M::e()),
            "the predicate must return `true` for the identity",
        );

        if right == 0 {
            return 0;
        }

        let mut r = right;
        r += self.tree_size;
        let mut sm = M::e();

        loop {
            r -= 1;
            while r > 1 && r % 2 == 1 {
                r >>= 1;
            }
            debug_assert!(r < self.data.len());
            if !pred(M::op(
                unsafe { self.data.get_unchecked(r) }.clone(),
                sm.clone(),
            )) {
                while r < self.tree_size {
                    r = 2 * r + 1;
                    debug_assert!(r < self.data.len());
                    if pred(M::op(
                        unsafe { self.data.get_unchecked(r) }.clone(),
                        sm.clone(),
                    )) {
                        debug_assert!(r < self.data.len());
                        sm = M::op(unsafe { self.data.get_unchecked(r) }.clone(), sm);
                        r -= 1;
                    }
                }
                return r + 1 - self.tree_size;
            }
            sm = M::op(
                unsafe {
                    debug_assert!(r < self.data.len());
                    self.data.get_unchecked(r)
                }
                .clone(),
                sm,
            );

            // SAFETY: the max length of the Vec is (currently) isize::MAX so
            // valid index must be less than isize::MAX.
            let r = r as isize;
            if r & -r != r {
                break;
            }
        }

        0
    }

    fn update(&mut self, index: usize) {
        // SAFETY: the binary tree structure of self.data
        unsafe {
            *self.data.get_unchecked_mut(index) = M::op(
                self.data.get_unchecked(2 * index).clone(),
                self.data.get_unchecked(2 * index + 1).clone(),
            );
        }
    }
}
