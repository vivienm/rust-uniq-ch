//! A Rust library for counting distinct elements in a stream,
//! using [ClickHouse uniq][ClickHouseRefUniq] data structure.
//!
//! This uses [BJKST][BarYossef+02], a probabilistic algorithm that relies on
//! adaptive sampling and provides fast, accurate and deterministic results.
//! Two BJKSTs can be merged, making the data structure well suited for
//! map-reduce settings.
//!
//! [Repository]
//!
//! [ClickHouseRefUniq]: https://clickhouse.com/docs/en/sql-reference/aggregate-functions/reference/uniq/
//! [BarYossef+02]: https://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.12.6276
//! [Repository]: https://github.com/vivienm/rust-uniq-ch
//!
//! # Examples
//!
//! ```
//! use uniq_ch::Bjkst;
//!
//! let mut bjkst = Bjkst::new();
//!
//! // Add some elements, with duplicates.
//! bjkst.extend(0..75_000);
//! bjkst.extend(25_000..100_000);
//!
//! // Count the distinct elements.
//! assert!((99_000..101_000).contains(&bjkst.len()));
//! ```

use std::{
    collections::hash_map::DefaultHasher,
    hash::{BuildHasher, BuildHasherDefault, Hash, Hasher},
    marker::PhantomData,
    num::NonZeroU64,
    ops::{BitOr, BitOrAssign},
};

pub use crate::precision::Precision;

pub mod precision;

/// A [BJKST][BarYossef+02] data structure to estimate the number of distinct
/// elements in a data stream.
///
/// [BarYossef+02]: https://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.12.6276
///
/// # Examples
///
/// ```
/// use uniq_ch::Bjkst;
///
/// let mut bjkst = Bjkst::new();
///
/// // Add some elements, with duplicates.
/// bjkst.extend(0..75_000);
/// bjkst.extend(25_000..100_000);
///
/// // Count the distinct elements.
/// assert!((99_000..101_000).contains(&bjkst.len()));
/// ```

#[derive(Debug)]
pub struct Bjkst<T, S = BuildHasherDefault<DefaultHasher>> {
    /// For typechecking.
    phantom: PhantomData<T>,
    /// Computes hashes of inserted elements.
    build_hasher: S,
    /// The number of elements in the table.
    count: usize,
    /// The current size of the table, as a power of `2`.
    size_degree: u8,
    /// Skip elements not divisible by `2 ** skip_degree`.
    skip_degree: u8,
    /// The maximum number of elements in the table, as a power of `2`.
    /// The table is twice bigger than this value.
    precision: Precision,
    /// An element with a hash value of `0` has been inserted.
    has_zero: bool,
    /// The table of hash values.
    hashes: Vec<Option<NonZeroU64>>,
}

impl<T> Bjkst<T, BuildHasherDefault<DefaultHasher>> {
    /// Creates an empty `Bjkst`.
    ///
    /// # Examples
    ///
    /// ```
    /// use uniq_ch::Bjkst;
    ///
    /// let bjkst = Bjkst::<usize>::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }
}

impl<T, S> Bjkst<T, S>
where
    S: Default,
{
    /// Creates an empty `Bjkst` with the specified precision.
    ///
    /// # Examples
    ///
    /// ```
    /// use uniq_ch::{Bjkst, Precision};
    ///
    /// let bjkst = Bjkst::<usize>::with_precision(Precision::P10);
    /// assert_eq!(bjkst.precision(), Precision::P10);
    /// ```
    #[inline]
    pub fn with_precision(precision: Precision) -> Self {
        Self::with_precision_and_hasher(precision, S::default())
    }
}

impl<T, S> Bjkst<T, S> {
    /// Creates an empty `Bjkst` with the specified precision, using `hasher` to
    /// hash values.
    ///
    /// Warning: `hasher` is normally randomly generated, and is designed to
    /// allow `Bjkst`s to be resistant to attacks that cause many collisions
    /// and very poor performance. Setting it manually using this function
    /// can expose a DoS attack vector.
    ///
    /// The `hasher` passed should implement the [`BuildHasher`] trait for the
    /// BJKST to be useful, see its documentation for details.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::hash_map::RandomState;
    ///
    /// use uniq_ch::{Bjkst, Precision};
    ///
    /// let hasher = RandomState::new();
    /// let mut bjkst = Bjkst::with_precision_and_hasher(Precision::P10, hasher);
    /// bjkst.insert(&2);
    /// ```
    pub fn with_precision_and_hasher(precision: Precision, hasher: S) -> Self {
        let size_degree = precision.initial_size_degree();
        Self {
            phantom: PhantomData,
            build_hasher: hasher,
            count: 0,
            size_degree,
            precision,
            skip_degree: 0,
            has_zero: false,
            // Precision range guarantees to avoid overflows.
            hashes: vec![None; 1usize << size_degree],
        }
    }

    /// Creates a new empty `Bjkst` which will use the given hasher to hash
    /// values.
    ///
    /// Warning: `hasher` is normally randomly generated, and is designed to
    /// allow `Bjkst`s to be resistant to attacks that cause many collisions
    /// and very poor performance. Setting it manually using this function
    /// can expose a DoS attack vector.
    ///
    /// The `hasher` passed should implement the [`BuildHasher`] trait for the
    /// BJKST to be useful, see its documentation for details.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::hash_map::RandomState;
    ///
    /// use uniq_ch::Bjkst;
    ///
    /// let hasher = RandomState::new();
    /// let mut bjkst = Bjkst::with_hasher(hasher);
    /// bjkst.insert(&2);
    /// ```
    #[inline]
    pub fn with_hasher(hasher: S) -> Self {
        Self::with_precision_and_hasher(Precision::default(), hasher)
    }

    /// Returns the precision of the `Bjkst`.
    ///
    /// # Examples
    ///
    /// ```
    /// use uniq_ch::{Bjkst, Precision};
    ///
    /// let bjkst = Bjkst::<usize>::with_precision(Precision::P10);
    /// assert_eq!(bjkst.precision(), Precision::P10);
    /// ```
    #[inline]
    pub const fn precision(&self) -> Precision {
        self.precision
    }

    /// Returns a reference to the BJKST data structure's [`BuildHasher`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::hash_map::RandomState;
    ///
    /// use uniq_ch::Bjkst;
    ///
    /// let hasher = RandomState::new();
    /// let bjkst = Bjkst::<usize, _>::with_hasher(hasher);
    /// let hasher: &RandomState = bjkst.hasher();
    /// ```
    #[inline]
    pub fn hasher(&self) -> &S {
        &self.build_hasher
    }

    /// Clears the BJKST data structure, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use uniq_ch::Bjkst;
    ///
    /// let mut bjkst = Bjkst::new();
    /// bjkst.insert(&1);
    /// bjkst.clear();
    /// assert!(bjkst.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.count = 0;
        self.size_degree = self.precision.initial_size_degree();
        self.skip_degree = 0;
        self.has_zero = false;
        self.hashes.truncate(1 << self.size_degree);
        self.hashes.fill(None);
    }

    /// Returns `true` if the BJKST data structure contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use uniq_ch::Bjkst;
    ///
    /// let mut bjkst = Bjkst::new();
    /// assert!(bjkst.is_empty());
    /// bjkst.insert(&1);
    /// assert!(!bjkst.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Adds a hash value to the BJKST data structure.
    ///
    /// Returns whether the value was newly inserted. That is:
    ///
    /// - If the value is not skipped, and the BJKST data structure did not
    ///   previously contain this value, `true` is returned.
    /// - If the value is skipped or the BJKST data structure already contained
    ///   this value, `false` is returned.
    ///
    /// This may be handy when the hash is previously computed, to avoid
    /// computing twice. Hash values need to be uniformly distributed over
    /// [u64] for an accurate total count.
    ///
    /// In all other cases, use [`insert`][Bjkst::insert] instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use uniq_ch::Bjkst;
    ///
    /// let mut bjkst = Bjkst::<usize>::new();
    ///
    /// assert_eq!(bjkst.insert_hash(0x12345678), true);
    /// assert_eq!(bjkst.insert_hash(0x12345678), false);
    /// assert_eq!(bjkst.len(), 1);
    /// ```
    pub fn insert_hash(&mut self, hash: u64) -> bool {
        if self.should_keep(hash) {
            let count = self.count;
            self.do_insert(hash);
            let inserted = count != self.count;
            self.adjust_to_fit();
            inserted
        } else {
            false
        }
    }

    /// Determines if an element should be kept, that is, its value is divisible
    /// by `2 ** skip_degree`.
    #[inline]
    fn should_keep(&self, hash: u64) -> bool {
        hash == (hash >> self.skip_degree) << self.skip_degree
    }

    /// Unconditionally inserts a value into the BJKST data structure.
    fn do_insert(&mut self, hash: u64) {
        let hash = match NonZeroU64::new(hash) {
            None if self.has_zero => return,
            None => {
                self.count += 1;
                self.has_zero = true;
                return;
            }
            Some(hash) => hash,
        };

        let mut i = self.expected_index(hash);
        while let Some(hash_i) = self.hashes[i] {
            if hash_i == hash {
                break;
            }
            i += 1;
            i %= self.hashes.len();
        }
        if self.hashes[i].is_none() {
            self.hashes[i] = Some(hash);
            self.count += 1;
        }
    }

    /// Resize the BJKST data structure if the buffer is full enough.
    /// If there are too many items, then throw half of them and repeat until
    /// their count is below the threshold.
    fn adjust_to_fit(&mut self) {
        if self.count > self.fill_threshold() {
            let purge_threshold = self.purge_threshold();
            if self.count > purge_threshold {
                while self.count > purge_threshold {
                    self.skip_degree += 1;
                    self.purge();
                }
            } else {
                self.grow();
            }
        }
    }

    #[inline]
    fn expected_index(&self, hash: NonZeroU64) -> usize {
        (hash.get() as usize >> self.precision.bits_to_skip()) % self.hashes.len()
    }

    #[inline]
    const fn fill_threshold(&self) -> usize {
        1 << (self.size_degree - 1)
    }

    #[inline]
    const fn purge_threshold(&self) -> usize {
        1 << self.precision.get()
    }

    /// Purge the BJKST data structure, deleting all values not divisible by `2
    /// ** skip_degree`. This must be called after increasing the skip
    /// degree.
    fn purge(&mut self) {
        for i in 0..self.hashes.len() {
            let hash = self.hashes[i];
            if let Some(hash) = hash {
                if !self.should_keep(hash.get()) {
                    self.hashes[i] = None;
                    self.count -= 1;
                } else if i != self.expected_index(hash) {
                    // After removing the elements, there may have been room for items,
                    // which were placed further than necessary, due to a collision.
                    // You need to move them.
                    self.hashes[i] = None;
                    self.reinsert(hash);
                }
            }
        }

        // We must process first collision resolution chain once again.
        // Look at the comment in function `grow_to`.
        for i in 0..self.hashes.len() {
            let hash = self.hashes[i];
            if let Some(hash) = hash {
                self.hashes[i] = None;
                self.reinsert(hash);
            } else {
                break;
            }
        }
    }

    /// Doubles the size of the buffer.
    #[inline]
    fn grow(&mut self) {
        self.grow_to(self.size_degree + 1)
    }

    /// Increases the size of the buffer up to `2 ** size_degree`.
    fn grow_to(&mut self, size_degree: u8) {
        let old_size = self.hashes.len();

        // Expand the space.
        self.hashes.resize(1 << size_degree, None);
        self.size_degree = size_degree;

        // Now some items may need to be moved to a new location.
        // Each element can stay in place, or move to a new location "on the right",
        // or move to the left of the collision resolution chain, because the elements
        // to the left of it have been moved to the new "right" location.
        //
        // There is also a special case:
        // If the element was to be at the end of the old buffer (`x`)
        // [        x] but is at the beginning because of the collision
        // resolution chain (`o`)       [o       x] then after resizing, it will
        // first be out of place again.                     [        xo        ]
        // Transferring it to the right location requires,
        // after transferring all elements from the old half of the buffer,
        // [         o   x    ] to process the tail of the collision resolution
        // chain that follows.           [        o    x    ] This is why we
        // don't necessarily stop when `i >= old_size`,
        for i in 0.. {
            let hash_i = self.hashes[i];
            let hash_i = match hash_i {
                None if i >= old_size => break,
                None => continue,
                Some(hash) => hash,
            };

            let mut j = self.expected_index(hash_i);

            // The element is in its place.
            if j == i {
                continue;
            }

            let mut hash_h = self.hashes[j];
            while let Some(hash_j) = hash_h {
                if hash_j == hash_i {
                    break;
                }
                j += 1;
                j %= self.hashes.len();
                hash_h = self.hashes[j];
            }

            // The element remained in its place.
            if let Some(hash_j) = hash_h {
                if hash_j == hash_i {
                    continue;
                }
            }

            self.hashes[j] = Some(hash_i);
            self.hashes[i] = None;
        }
    }

    /// Reinserts a value into the BJKST data structure.
    /// Used when increasing the size of the buffer, as well as when reading
    /// from a file.
    fn reinsert(&mut self, hash: NonZeroU64) {
        let mut i = self.expected_index(hash);
        while self.hashes[i].is_some() {
            i += 1;
            i %= self.hashes.len();
        }
        self.hashes[i] = Some(hash);
    }
}

impl<T, S> Bjkst<T, S>
where
    T: Hash,
    S: BuildHasher,
{
    /// Adds a value to the BJKST data structure.
    ///
    /// Returns whether the value was newly inserted. That is:
    ///
    /// - If the value is not skipped, and the BJKST data structure did not
    ///   previously contain this value, `true` is returned.
    /// - If the value is skipped or the BJKST data structure already contained
    ///   this value, `false` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use uniq_ch::Bjkst;
    ///
    /// let mut bjkst = Bjkst::new();
    ///
    /// assert_eq!(bjkst.insert(&2), true);
    /// assert_eq!(bjkst.insert(&2), false);
    /// assert_eq!(bjkst.len(), 1);
    /// ```
    pub fn insert(&mut self, value: &T) -> bool {
        self.insert_hash(self.hash(value))
    }

    fn hash<Q>(&self, value: &Q) -> u64
    where
        Q: Hash + ?Sized,
    {
        self.build_hasher.hash_one(value)
    }

    /// Calculates the approximate number of different elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use uniq_ch::Bjkst;
    ///
    /// let mut bjkst = Bjkst::new();
    /// for i in 0..100_000 {
    ///     bjkst.insert(&i);
    /// }
    /// assert!((99_000..=101_000).contains(&bjkst.len()));
    /// ```
    pub fn len(&self) -> usize {
        if 0 == self.skip_degree {
            return self.count;
        }

        let mut res = self.count as u64 * (1 << self.skip_degree);

        // Pseudo-random remainder - in order to hide that the number is divisible by a
        // power of two.
        res += self.hash(&self.count) & ((1 << self.skip_degree) - 1);

        // Correction of a systematic error due to collisions during hashing.
        // Seems broken due to rounding errors, and not needed with 64-bit hashes.
        // let p64 = 2.0f64.powi(64);
        // f64::round(p64 * (f64::ln(p64) - f64::ln(p64 - res as f64))) as usize
        res as usize
    }
}

impl<T, H> BitOr<&Bjkst<T, BuildHasherDefault<H>>> for &Bjkst<T, BuildHasherDefault<H>>
where
    T: Hash,
    H: Default + Hasher,
{
    type Output = Bjkst<T, BuildHasherDefault<H>>;

    /// Returns the union of `self` and `rhs` as a new `Bjkst<S, T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use uniq_ch::Bjkst;
    ///
    /// let lhs = Bjkst::<i32>::from_iter(0..75_000);
    /// let rhs = Bjkst::<i32>::from_iter(25_000..100_000);
    /// let bjkst = &lhs | &rhs;
    /// assert!((99_000..=101_000).contains(&bjkst.len()));
    /// ```
    fn bitor(self, rhs: &Bjkst<T, BuildHasherDefault<H>>) -> Self::Output {
        let mut bjkst = Bjkst {
            skip_degree: self.skip_degree.max(rhs.skip_degree),
            ..Default::default()
        };

        if self.has_zero || rhs.has_zero {
            bjkst.has_zero = true;
            bjkst.count = 1;
        }

        for hash in self.hashes.iter().chain(rhs.hashes.iter()).flatten() {
            bjkst.insert_hash(hash.get());
        }
        bjkst
    }
}

impl<T, H> BitOrAssign<&Bjkst<T, BuildHasherDefault<H>>> for Bjkst<T, BuildHasherDefault<H>>
where
    T: Hash,
    H: Default + Hasher,
{
    /// Merges `self` and `rhs` into `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use uniq_ch::Bjkst;
    ///
    /// let mut lhs = Bjkst::<i32>::from_iter(1..75_000);
    /// let rhs = Bjkst::<i32>::from_iter(25_000..100_000);
    /// lhs |= &rhs;
    /// assert!((99_000..=101_000).contains(&lhs.len()));
    /// ```
    fn bitor_assign(&mut self, rhs: &Bjkst<T, BuildHasherDefault<H>>) {
        if rhs.skip_degree > self.skip_degree {
            self.skip_degree = rhs.skip_degree;
            self.purge();
        }

        if !self.has_zero && rhs.has_zero {
            self.has_zero = true;
            self.count += 1;
            self.adjust_to_fit();
        }

        for hash in rhs.hashes.iter().flatten() {
            self.insert_hash(hash.get());
        }
    }
}

impl<T, S> Clone for Bjkst<T, S>
where
    S: Clone,
{
    fn clone(&self) -> Self {
        Self {
            phantom: self.phantom,
            build_hasher: self.build_hasher.clone(),
            count: self.count,
            size_degree: self.size_degree,
            precision: self.precision,
            skip_degree: self.skip_degree,
            has_zero: self.has_zero,
            hashes: self.hashes.clone(),
        }
    }
}

impl<T, S> Default for Bjkst<T, S>
where
    S: Default,
{
    #[inline]
    fn default() -> Self {
        Self::with_hasher(S::default())
    }
}

impl<'a, T, S> Extend<&'a T> for Bjkst<T, S>
where
    T: Hash + 'a,
    S: BuildHasher,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'a T>,
    {
        for value in iter {
            self.insert(value);
        }
    }
}

impl<T, S> Extend<T> for Bjkst<T, S>
where
    T: Hash,
    S: BuildHasher,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        for value in iter {
            self.insert(&value);
        }
    }
}

impl<'a, T, S, const N: usize> From<[&'a T; N]> for Bjkst<T, S>
where
    T: Hash,
    S: BuildHasher + Default,
{
    #[inline]
    fn from(values: [&'a T; N]) -> Self {
        Self::from_iter(values)
    }
}

impl<T, S, const N: usize> From<[T; N]> for Bjkst<T, S>
where
    T: Hash,
    S: BuildHasher + Default,
{
    /// Creates a new `Bjkst<T, S>` from an array of `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use uniq_ch::Bjkst;
    ///
    /// let bjkst1 = Bjkst::<i32>::from([1, 2, 3, 4, 5]);
    /// let bjkst2: Bjkst<i32> = [1, 2, 3, 4, 5].into();
    /// assert_eq!(bjkst1.len(), bjkst2.len());
    /// ```
    #[inline]
    fn from(values: [T; N]) -> Self {
        Self::from_iter(values)
    }
}

impl<'a, T, S> FromIterator<&'a T> for Bjkst<T, S>
where
    T: Hash + 'a,
    S: BuildHasher + Default,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = &'a T>,
    {
        let mut bjkst = Bjkst::default();
        bjkst.extend(iter);
        bjkst
    }
}

impl<T, S> FromIterator<T> for Bjkst<T, S>
where
    T: Hash,
    S: BuildHasher + Default,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut bjkst = Bjkst::default();
        bjkst.extend(iter);
        bjkst
    }
}

#[cfg(feature = "serde")]
impl<T, S> serde::Serialize for Bjkst<T, S>
where
    S: Default,
{
    fn serialize<R>(&self, serializer: R) -> Result<R::Ok, R::Error>
    where
        R: serde::Serializer,
    {
        (
            self.count,
            self.size_degree,
            self.precision,
            self.skip_degree,
            self.has_zero,
            &self.hashes,
        )
            .serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, T, S> serde::Deserialize<'de> for Bjkst<T, S>
where
    S: Default,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let (count, size_degree, precision, skip_degree, has_zero, hashes) =
            serde::Deserialize::deserialize(deserializer)?;
        Ok(Self {
            count,
            size_degree,
            precision,
            skip_degree,
            has_zero,
            hashes,
            ..Self::default()
        })
    }
}
