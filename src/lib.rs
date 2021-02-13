//! Provide suffix sorting function that runs in O(N+|Σ|) time with O(|Σ|) additional workspace.
//!
//! The implementation is based on the algorithm proposed in the paper [*Practical Linear-Time O(1)-Workspace Sufﬁx Sorting for Constant Alphabets*](https://storage.googleapis.com/google-code-archive-downloads/v2/code.google.com/ge-nong/saca-k-tois.pdf).
//!
//! # Example
//! ```ignore
//! use sacak::construct;
//! use std::fs;
//! use std::io;
//!
//! fn main() -> io::Result<()> {
//!     let mut buf = fs::read("./english.100MB")?;
//!     buf.push(0); // sentinel
//!     let mut sa = vec![0u32; buf.len()];
//!     construct(&buf, &mut sa);
//!
//!     Ok(())
//! }
//! ```
use contracts::*;
use std::cmp::Ordering::*;

mod private {
    use num::{
        traits::{WrappingAdd, WrappingSub},
        PrimInt,
    };
    use std::fmt::Debug;
    use std::ops::{AddAssign, BitAnd, BitOr, BitXor, SubAssign};

    pub trait Char:
        PrimInt
        + AddAssign
        + SubAssign
        + BitAnd
        + BitOr
        + BitXor
        + Copy
        + Debug
        + WrappingAdd
        + WrappingSub
    {
        fn of_u(v: usize) -> Self;
        fn to_u(&self) -> usize;
        fn hb_mask() -> Self;
    }

    macro_rules! impl_char {
        ($uint:ty) => {
            impl Char for $uint {
                #[inline]
                fn of_u(v: usize) -> Self {
                    v as $uint
                }
                #[inline]
                fn to_u(&self) -> usize {
                    *self as usize
                }
                #[inline]
                fn hb_mask() -> Self {
                    (1 as $uint).reverse_bits()
                }
            }
        };
    }

    impl_char!(u8);

    impl_char!(u16);

    #[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
    impl_char!(u32);

    #[cfg(target_pointer_width = "64")]
    impl_char!(u64);

    impl_char!(usize);
}

/// A trait that represents both character and index: primitive unsigned integer type that fit into `usize`.
///
/// This is a [sealed trait](https://rust-lang.github.io/api-guidelines/future-proofing.html).
pub trait Char: private::Char {}

macro_rules! impl_char {
    ($uint:ty) => {
        impl Char for $uint {}
    };
}

impl_char!(u8);

impl_char!(u16);

#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
impl_char!(u32);

#[cfg(target_pointer_width = "64")]
impl_char!(u64);

impl_char!(usize);

/// split slice into two parts; fst[..mid], ..., snd[slice.len()-mid..]
/// See https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html
fn split_at_same_len_mut<T>(slice: &mut [T], mid: usize) -> (&mut [T], &mut [T]) {
    use std::slice;

    let len = slice.len();
    let ptr = slice.as_mut_ptr();

    assert!(mid * 2 <= len);

    unsafe {
        (
            slice::from_raw_parts_mut(ptr, mid),
            slice::from_raw_parts_mut(ptr.offset((slice.len() - mid) as isize), mid),
        )
    }
}

/// v==0b100..000
#[inline]
fn is_empty<C: Char>(v: C) -> bool {
    v == empty()
}

#[inline]
fn empty<C: Char>() -> C {
    C::hb_mask()
}

/// v==0b1**...*** and !is_empty(v)
#[inline]
fn is_counter<C: Char>(v: C) -> bool {
    ((v & C::hb_mask()) != C::zero()) && !is_empty(v)
}

#[inline]
fn increment_counter<C: Char>(v: &mut C) {
    let c = !C::hb_mask() & *v;
    *v = C::hb_mask() | (c + C::one());
}

#[inline]
fn get_count<C: Char>(v: C) -> usize {
    (!C::hb_mask() & v).to_u()
}

/// v==0b0**...***
#[inline]
fn is_index<C: Char>(v: C) -> bool {
    (v & C::hb_mask()) == C::zero()
}

#[inline]
fn clear<I: Char>(l: &mut [I]) {
    l.iter_mut().for_each(|e| *e = I::zero());
}

fn fill_bucket<C: Char, I: Char>(s: &[C], bucket: &mut [I], head: bool) {
    clear(bucket);

    s.iter().for_each(|c| bucket[c.to_u()] += I::one());

    (0..bucket.len()).fold(0, |s, i| {
        let s = s + bucket[i].to_u();
        bucket[i] = I::of_u(if head {
            s - bucket[i].to_u()
        } else {
            s.wrapping_sub(1)
        });
        s
    });
}

fn fill_lms_index<C: Char, I: Char>(s: &[C], sa: &mut [I]) {
    let lms_count = sa.len();

    let mut j = lms_count - 1;
    let mut is_s = true; // s[n-1] is S-type

    for i in (1..s.len()).rev() {
        let prev_is_s = s[i - 1] < s[i] || (s[i - 1] == s[i] && is_s);
        // s[i] is LMS
        if !prev_is_s && is_s {
            sa[j] = I::of_u(i);
            j = j.wrapping_sub(1);
        }

        is_s = prev_is_s;
    }
}

fn put_lms_char<C: Char, I: Char>(s: &[C], bucket: &mut [I], sa: &mut [I]) -> usize {
    clear(sa);

    fill_bucket(s, bucket, false);

    let mut lms_count = 1;

    let mut is_s = false; // s[n-2] is L-type
    (1..s.len() - 1).rev().for_each(|i| {
        let prev_is_s = match s[i - 1].cmp(&s[i]) {
            Greater => false,
            Equal => is_s,
            Less => true,
        };

        // s[i] is LMS?
        if is_s && !prev_is_s {
            let j = bucket[s[i].to_u()].to_u();
            sa[j] = I::of_u(i);
            bucket[s[i].to_u()] = bucket[s[i].to_u()].wrapping_sub(&I::one());
            lms_count += 1;
        }

        is_s = prev_is_s;
    });

    sa[0] = I::of_u(s.len() - 1);

    lms_count
}

/// Pre-condition: sa[0..lms_count] == sa1[0..lms_count]
fn put_lms_suffix<C: Char, I: Char>(s: &[C], lms_count: usize, bucket: &mut [I], sa: &mut [I]) {
    debug_assert!(s.len() == sa.len());

    {
        let (sa1, lms_index) = split_at_same_len_mut(sa, lms_count);

        fill_lms_index(s, lms_index);

        sa1.iter_mut().for_each(|e| *e = lms_index[e.to_u()]);
    }
    // -> sa[..lms_count] contains sorted LMS suffixes

    clear(&mut sa[lms_count..]);

    fill_bucket(s, bucket, false);

    for i in (0..lms_count).rev() {
        let j = sa[i];
        let b = &mut bucket[s[j.to_u()].to_u()];
        sa[i] = I::zero();
        sa[b.to_u()] = j;
        *b = b.wrapping_sub(&I::one());
    }
}

fn sort_l<C: Char, I: Char>(s: &[C], bucket: &mut [I], sa: &mut [I], suf: bool) {
    debug_assert_eq!(s.len(), sa.len());

    fill_bucket(s, bucket, true);

    for i in 0..s.len() {
        let j = sa[i].to_u();
        // s[j-1] is L-type?
        if j > 0 && s[j - 1] >= s[j] {
            let b = &mut bucket[s[j - 1].to_u()];
            sa[b.to_u()] = I::of_u(j - 1);
            *b = b.wrapping_add(&I::one());

            // only left-most L-type remain
            if i > 0 && !suf {
                sa[i] = I::zero();
            }
        }
    }
}

fn sort_s<C: Char, I: Char>(s: &[C], bucket: &mut [I], sa: &mut [I], suf: bool) {
    fill_bucket(s, bucket, false);

    for i in (0..sa.len()).rev() {
        let j = sa[i].to_u();
        if j > 0 {
            let b = &mut bucket[s[j - 1].to_u()];
            // s[j-1] is S-type?
            if s[j - 1] < s[j] || (s[j - 1] == s[j] && b.to_u() < i) {
                sa[b.to_u()] = I::of_u(j - 1);
                *b = b.wrapping_sub(&I::one());

                // only LMS remain
                if !suf {
                    sa[i] = I::zero();
                }
            }
        }
    }
}

#[inline]
fn fill_empty<I: Char>(sa: &mut [I]) {
    sa.iter_mut().for_each(|e| *e = empty());
}

fn put_head<C: Char, I: Char>(idx: I, s: &[C], sa: &mut [I]) -> Option<C> {
    let c = s[idx.to_u()].to_u();

    let mut shifted_bucket = None;

    // sa[c] is borrowed by left-neighboring bucket
    if is_index(sa[c]) {
        // find the counter of left-neighboring bucket
        for j in (0..c).rev() {
            if is_counter(sa[j]) {
                // shift left one step
                (j..c).for_each(|k| sa[k] = sa[k + 1]);
                shifted_bucket = Some(C::of_u(j));
                break;
            }
        }

        sa[c] = empty();
    }

    debug_assert!(!is_index(sa[c]));

    if is_empty(sa[c]) {
        if c < sa.len() - 1 && is_empty(sa[c + 1]) {
            sa[c] = I::hb_mask(); // use as counter
            sa[c + 1] = idx;
            increment_counter(&mut sa[c]);
        } else {
            sa[c] = idx;
        }
    } else {
        debug_assert!(is_counter(sa[c]));

        let d = get_count(sa[c]);

        let pos = c + d + 1;

        if pos < sa.len() && is_empty(sa[pos]) {
            sa[pos] = idx;
            increment_counter(&mut sa[c]);
        } else {
            // shift this bucket left one step
            (c..pos - 1).for_each(|k| {
                sa[k] = sa[k + 1];
            });

            sa[pos - 1] = idx;

            shifted_bucket = Some(C::of_u(c));
        }
    }

    shifted_bucket
}

fn put_tail<C: Char, I: Char>(idx: I, s: &[C], sa: &mut [I]) -> Option<C> {
    let i = s[idx.to_u()].to_u();

    let mut shifted_bucket = None;

    // sa[i] is borrowed by right-neighboring bucket
    if is_index(sa[i]) {
        // find the counter of the right-neighboring bucket
        for j in i + 1..sa.len() {
            if is_counter(sa[j]) {
                // shift right one step
                (i..j).rev().for_each(|k| sa[k + 1] = sa[k]);
                shifted_bucket = Some(C::of_u(j));
                break;
            }
        }

        sa[i] = empty();
    }

    debug_assert!(!is_index(sa[i]));

    if is_empty(sa[i]) {
        if i > 0 && is_empty(sa[i - 1]) {
            sa[i] = I::hb_mask(); // use as counter
            sa[i - 1] = idx;
            increment_counter(&mut sa[i]);
        } else {
            sa[i] = idx;
        }
    } else {
        debug_assert!(is_counter(sa[i]));

        let d = get_count(sa[i]);

        let pos = i - d - 1;

        if is_empty(sa[pos]) {
            sa[pos] = idx;
            increment_counter(&mut sa[i]);
        } else {
            debug_assert!(shifted_bucket.is_none());

            // shift this bucket to left one step
            (pos..i).rev().for_each(|k| {
                sa[k + 1] = sa[k];
            });

            sa[pos + 1] = idx;

            shifted_bucket = Some(C::of_u(i));
        }
    }

    shifted_bucket
}

fn clear_head_counter<I: Char>(sa: &mut [I]) {
    let mut i = 0;
    while i < sa.len() {
        if is_counter(sa[i]) {
            let d = get_count(sa[i]);
            (i..i + d).for_each(|j| sa[j] = sa[j + 1]);
            sa[i + d] = empty();
            i += d;
        } else {
            i += 1;
        }
    }
}

fn clear_tail_counter<I: Char>(sa: &mut [I]) {
    let mut i = sa.len() - 1;
    while i >= 1 {
        if is_counter(sa[i]) {
            let d = get_count(sa[i]);
            (i - d + 1..=i).rev().for_each(|j| sa[j] = sa[j - 1]);
            sa[i - d] = empty();
            i -= d;
        } else {
            i -= 1;
        }
    }
}

fn put_lms_char_rec<C: Char, I: Char>(s: &[C], sa: &mut [I]) -> usize {
    fill_empty(sa);

    let mut lms_count = 0;

    let mut is_s = true;
    (1..s.len()).rev().for_each(|i| {
        // s[i] is LMS
        if is_s && s[i] < s[i - 1] {
            put_tail(I::of_u(i), s, sa);
            lms_count += 1;
        }

        is_s = match s[i - 1].cmp(&s[i]) {
            Greater => false,
            Equal => is_s,
            Less => true,
        };
    });

    sa[0] = I::of_u(s.len() - 1);

    clear_tail_counter(sa);

    lms_count
}

fn sort_l_rec<C: Char, I: Char>(s: &[C], sa: &mut [I], suf: bool) {
    let mut i = 0;
    while i < s.len() {
        if !is_index(sa[i]) {
            i += 1;
            continue;
        }

        let j = sa[i].to_u();

        // s[j-1] is L-type
        if j > 0 && s[j - 1] >= s[j] {
            let shifted = put_head(I::of_u(j - 1), s, sa);

            // s[j] is L-type?
            let is_l =
                j < s.len() - 1 && (s[j] > s[j + 1] || (s[j] == s[j + 1] && s[j].to_u() < i));

            // clear if !suf or s[j] is LMS

            // current bucket was shifted left
            if shifted == Some(s[j]) {
                if i - 1 > 0 && (!suf || !is_l) {
                    sa[i - 1] = empty();
                }
            } else {
                if i > 0 && (!suf || !is_l) {
                    sa[i] = empty();
                }
                i += 1;
            }
        } else {
            i += 1;
        }
    }

    clear_head_counter(sa);
}

fn sort_s_rec<C: Char, I: Char>(s: &[C], sa: &mut [I], suf: bool) {
    let mut i = s.len() - 1;
    while i > 0 {
        if !is_index(sa[i]) {
            i -= 1;
            continue;
        }

        let j = sa[i].to_u();
        // s[j-1] is S-type
        if j > 0 && (s[j - 1] < s[j] || (s[j - 1] == s[j] && s[j].to_u() > i)) {
            let shifted = put_tail(I::of_u(j - 1), s, sa);

            // only left most S-type (including 0) remain if !suf

            // current bucket was shifted right
            if shifted == Some(s[j]) {
                if i + 1 < sa.len() && !suf {
                    sa[i + 1] = empty();
                }
            } else {
                if i > 0 && !suf {
                    sa[i] = empty();
                }
                i -= 1;
            }
        } else {
            i -= 1;
        }
    }

    clear_tail_counter(sa);

    sa.iter_mut()
        .filter(|e| is_empty(**e))
        .for_each(|e| *e = I::zero());
}

fn put_lms_suffix_rec<C: Char, I: Char>(s: &[C], lms_count: usize, sa: &mut [I]) {
    debug_assert!(s.len() == sa.len());

    let n = sa.len();

    fill_empty(&mut sa[lms_count..n - lms_count]);

    {
        let (sa1, lms_index) = split_at_same_len_mut(sa, lms_count);

        fill_lms_index(s, lms_index);

        sa1.iter_mut().for_each(|e| *e = lms_index[e.to_u()]);
    }
    // -> sa[..lms_count] contains sorted LMS suffixes

    fill_empty(&mut sa[n - lms_count..]);

    let mut prev_char = None;
    let mut index = 0;
    for i in (0..lms_count).rev() {
        let j = sa[i].to_u();

        if prev_char != Some(s[j]) {
            index = s[j].to_u(); // s[j] points to the tail of its bucket
            prev_char = Some(s[j]);
        }

        let temp = sa[i];
        sa[i] = empty();
        sa[index] = temp;
        index = index.wrapping_sub(1);
    }
}

fn lms_substr_end<C: Char>(s: &[C], i: usize) -> usize {
    let mut l_found = false;
    let mut may_end = s.len() - 1;

    for j in i + 1..s.len() {
        if s[j] < s[j - 1] {
            l_found = true;
            may_end = j;
        }

        if l_found && s[j] > s[j - 1] {
            break;
        }
    }

    may_end + 1
}

fn eq_lms_substr<C: Char>(s: &[C], i: usize, j: usize) -> bool {
    let ri = lms_substr_end(s, i);
    let rj = lms_substr_end(s, j);
    s[i..ri] == s[j..rj]
}

/// Pre-condition: sa contains sorted LMS-substrings
fn reduce<C: Char, I: Char>(s: &[C], lms_count: usize, sa: &mut [I]) -> usize {
    debug_assert!(!s.is_empty());
    debug_assert_eq!(s.len(), sa.len());
    debug_assert!(lms_count * 2 <= s.len());

    {
        let mut i = 0;
        for j in 0..sa.len() {
            if sa[j] > I::zero() {
                let temp = sa[j];
                sa[j] = I::zero();
                sa[i] = temp;
                i += 1;
            }
        }
    }

    let mut cur = I::zero();

    let n = sa.len();

    let m = n / 2;

    // # of occurrence of LMS ch is stored in sa[m + ch / 2]
    // we can do this because no two LMS are adjacent
    sa[m + sa[0].to_u() / 2] = cur;

    let mut name_counter = 1;

    for i in 1..lms_count {
        if !eq_lms_substr(s, sa[i - 1].to_u(), sa[i].to_u()) {
            cur = I::of_u(i);
            name_counter += 1;
        }

        sa[m + sa[i].to_u() / 2] = cur;
    }

    // replace LMS indexes with corresponding characters
    sa[n - 1] = I::zero();
    {
        let mut i = n - 2;
        for j in (m..n - 1).rev() {
            if sa[j] > I::zero() {
                sa[i] = sa[j];
                i = i.wrapping_sub(1);
            }
        }
    }

    // calculate prefix sum
    sa[0..lms_count].iter_mut().for_each(|e| *e = I::zero());

    for i in n - lms_count..sa.len() {
        let c = sa[i].to_u();
        sa[c] += I::one();
    }
    for i in 1..lms_count {
        sa[i] += sa[i - 1];
    }

    // replace S-type character with its bucket tail index
    let mut is_s = true; // sa[n-1] is S-type
    for i in (n - lms_count..n).rev() {
        if is_s {
            sa[i] = sa[sa[i].to_u()] - I::one();
        }

        debug_assert!(i > 0);

        is_s = match sa[i - 1].cmp(&sa[i]) {
            Less => true,
            Equal => is_s,
            Greater => false,
        };
    }

    clear(&mut sa[..n - lms_count]);

    name_counter
}

fn sacak<C: Char, I: Char>(s: &[C], sa: &mut [I]) {
    if s.len() == 1 {
        sa[0] = I::zero();
        return;
    }

    let upper = s.iter().max().unwrap().to_u();

    let mut bucket = vec![I::zero(); upper + 1];

    let lms_count = put_lms_char(s, &mut bucket, sa);

    debug_assert!(lms_count <= s.len() / 2);

    sort_l(s, &mut bucket, sa, false);

    sort_s(s, &mut bucket, sa, false);

    let name_count = reduce(s, lms_count, sa);

    if lms_count == name_count {
        let m = s.len() - lms_count;
        for i in m..s.len() {
            let c = sa[i];
            sa[c.to_u()] = I::of_u(i - m);
        }
    } else {
        let (sa1, s1) = split_at_same_len_mut(sa, lms_count);
        sacak_rec(s1, 1, sa1);
    }

    let mut bucket = vec![I::zero(); upper + 1];

    put_lms_suffix(s, lms_count, &mut bucket, sa);

    sort_l(s, &mut bucket, sa, true);

    sort_s(s, &mut bucket, sa, true);
}

fn sacak_rec<C: Char, I: Char>(s: &[C], depth: usize, sa: &mut [I]) {
    if s.len() == 1 {
        sa[0] = I::zero();
        return;
    }

    let lms_count = put_lms_char_rec(s, sa);

    debug_assert!(lms_count <= s.len() / 2);

    sort_l_rec(s, sa, false);

    sort_s_rec(s, sa, false);

    let name_count = reduce(s, lms_count, sa);

    if lms_count == name_count {
        let m = s.len() - lms_count;
        for i in m..s.len() {
            let c = sa[i];
            sa[c.to_u()] = I::of_u(i - m);
        }
    } else {
        let (sa1, s1) = split_at_same_len_mut(sa, lms_count);
        sacak_rec(s1, depth + 1, sa1);
    }

    put_lms_suffix_rec(s, lms_count, sa);

    sort_l_rec(s, sa, true);

    sort_s_rec(s, sa, true);
}

/// Construct suffix array.
///
/// Runs in O(N+|Σ|) time with O(|Σ|) additional workspace.
/// # Arguments
/// - `s`: Input string
/// - `sa`: Output suffix array
/// # Example
/// ```
/// use sacak;
///
/// let s = b"abracadabra$";
///
/// let mut sa = vec![0u8; s.len()];
///
/// sacak::construct(s, &mut sa);
///
/// assert_eq!(sa, vec![11, 10, 7, 0, 3, 5, 8, 1, 4, 6, 9, 2]);
/// ```
#[requires(s.len() >= 2, "`s` have 2 or more characters (including sentinel)")]
#[requires(s.len() == sa.len(), "`s` and `sa` have same length")]
#[requires(I::max_value().to_usize().unwrap() >= s.len() - 1, "indexes of `s` fit into `I`")]
#[requires(s.iter().min() == s.last(), "last character is minimum")]
#[requires(s.iter().filter(|c| *c == s.last().unwrap()).count() == 1, "last character is unique")]
pub fn construct<C: Char, I: Char>(s: &[C], sa: &mut [I]) {
    sacak(s, sa);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn is_suffix_array_of<C: Char, I: Char>(sa: &[I], s: &[C]) -> bool {
        s.len() == sa.len()
            && (0..sa.len() - 1).all(|i| {
                sa[i].to_u() < sa.len()
                    && sa[i + 1].to_u() < sa.len()
                    && s[sa[i].to_u()..] < s[sa[i + 1].to_u()..]
            })
    }

    #[test]
    fn bucket_head_works() {
        let s = "abbaebabdab"
            .chars()
            .map(|c| c as u8 - b'a')
            .collect::<Vec<_>>();

        let mut bucket = vec![0u32; 5];

        fill_bucket(&s, &mut bucket, true);

        assert_eq!(bucket, vec![0, 4, 9, 9, 10]);
    }

    #[test]
    fn bucket_tail_works() {
        let s = "abbaebabdab"
            .chars()
            .map(|c| c as u8 - b'a')
            .collect::<Vec<_>>();

        let mut bucket = vec![0u32; 5];

        fill_bucket(&s, &mut bucket, false);

        assert_eq!(bucket, vec![3, 8, 8, 9, 10]);
    }

    #[test]
    fn step_by_step() {
        // 012345678901
        // abracadabra$
        // SSLSLSLSSLLS
        // SA = [11, 10, 7, 0, 3, 5, 8, 1, 4, 6, 9, 2]

        let s = b"abracadabra$";

        let upper: u8 = *s.iter().max().unwrap();

        let mut bucket = vec![0u32; upper as usize + 1];
        let mut sa = vec![0u32; s.len()];

        let lms_count = put_lms_char(s, &mut bucket, &mut sa);
        assert_eq!(lms_count, 4);
        assert_eq!(sa, vec![11, 0, 0, 3, 5, 7, 0, 0, 0, 0, 0, 0]);

        sort_l(s, &mut bucket, &mut sa, false);
        assert_eq!(sa, vec![11, 0, 0, 0, 0, 0, 0, 0, 4, 6, 9, 2]);

        sort_s(s, &mut bucket, &mut sa, false);
        assert_eq!(sa, vec![11, 0, 7, 0, 3, 5, 0, 0, 0, 0, 0, 0]);

        let name_count = reduce(s, lms_count, &mut sa);
        assert_eq!(sa, vec![0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 1, 0]);
        assert_eq!(name_count, 4);

        let mut sa = vec![3, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0];
        put_lms_suffix(s, lms_count, &mut bucket, &mut sa);
        assert_eq!(sa, vec![11, 0, 0, 7, 3, 5, 0, 0, 0, 0, 0, 0]);

        sort_l(s, &mut bucket, &mut sa, true);
        assert_eq!(sa, vec![11, 10, 0, 7, 3, 5, 0, 0, 4, 6, 9, 2]);

        sort_s(s, &mut bucket, &mut sa, true);
        assert_eq!(sa, vec![11, 10, 7, 0, 3, 5, 8, 1, 4, 6, 9, 2]);
    }

    #[test]
    fn step_by_step_rec() {
        //          [original] [bucket]   [final]
        // [index]  012345678  012345678  012345678
        // [type]   SLLLSLLLS  |||||||||  SLLLSLLLS
        // [string] 132213210  011122233  374437410
        let s: Vec<u8> = vec![3, 7, 4, 4, 3, 7, 4, 1, 0];

        let mut sa = vec![0u8; s.len()];

        let lms_count = put_lms_char_rec(&s, &mut sa);
        assert_eq!(lms_count, 2);
        assert_eq!(sa, vec![8, 128, 128, 4, 128, 128, 128, 128, 128]);

        sort_l_rec(&s, &mut sa, false);
        assert_eq!(sa, vec![8, 128, 128, 128, 128, 128, 128, 5, 1]);

        sort_s_rec(&s, &mut sa, false);
        assert_eq!(sa, vec![8, 0, 4, 0, 0, 0, 0, 0, 0]);

        let name_count = reduce(&s, lms_count, &mut sa);
        assert_eq!(sa, vec![0, 0, 0, 0, 0, 0, 0, 1, 0]);
        assert_eq!(name_count, 2);

        let mut sa: Vec<u8> = vec![1, 0, 0, 0, 0, 0, 0, 0, 0];
        put_lms_suffix_rec(&s, lms_count, &mut sa);
        assert_eq!(sa, vec![8, 128, 128, 4, 128, 128, 128, 128, 128]);

        sort_l_rec(&s, &mut sa, true);
        assert_eq!(sa, vec![8, 7, 128, 128, 6, 3, 2, 5, 1]);

        sort_s_rec(&s, &mut sa, true);
        assert_eq!(sa, vec![8, 7, 4, 0, 6, 3, 2, 5, 1]);
    }

    #[test]
    fn suffix_array_abracadabra() {
        let s = b"abracadabra$";
        let mut sa = vec![0u8; s.len()];
        construct(s, &mut sa);
        assert_eq!(sa, vec![11, 10, 7, 0, 3, 5, 8, 1, 4, 6, 9, 2]);
    }

    #[test]
    fn suffix_array_mmiissiippii() {
        let s = b"mmiissiissiippii$";
        let mut sa = vec![0u8; s.len()];
        construct(s, &mut sa);
        assert_eq!(
            sa,
            vec![16, 15, 14, 10, 6, 2, 11, 7, 3, 1, 0, 13, 12, 9, 5, 8, 4]
        );
    }

    use proptest::collection::*;
    use proptest::num::*;
    use proptest::prelude::*;

    const UNARY: std::ops::Range<u8> = 1..2;
    const BINARY: std::ops::Range<u8> = 1..3;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1000))]
        #[test]
        fn suffix_array_unary(mut s in vec(UNARY, 1..(u8::MAX as usize))) {
            s.push(0u8);
            let mut sa = vec![0u8; s.len()];
            construct(&s, &mut sa);
            prop_assert!(is_suffix_array_of(&sa, &s));
        }

        #[test]
        fn suffix_array_binary(mut s in vec(BINARY, 1..(u8::MAX as usize))) {
            s.push(0u8);
            let mut sa = vec![0u8; s.len()];
            construct(&s, &mut sa);
            prop_assert!(is_suffix_array_of(&sa, &s));
        }

        #[test]
        fn suffix_array_u8u8(mut s in vec(1u8..=u8::MAX, 1..(u8::MAX as usize))) {
            s.push(0u8);
            let mut sa = vec![0u8; s.len()];
            construct(&s, &mut sa);
            prop_assert!(is_suffix_array_of(&sa, &s));
        }

        #[test]
        fn suffix_array_short(mut s in vec(1u8..=u8::MAX, 1..=1)) {
            s.push(0u8);
            let mut sa = vec![0u8; s.len()];
            construct(&s, &mut sa);
            prop_assert_eq!(sa, vec![1, 0]);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(50))]
        #[test]
        fn suffix_array_u8u16(mut s in vec(1u8..=u8::MAX, 1..(u16::MAX as usize))) {
            s.push(0u8);
            let mut sa = vec![0u16; s.len()];
            construct(&s, &mut sa);
            prop_assert!(is_suffix_array_of(&sa, &s));
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(50))]
        #[test]
        fn suffix_array_1000000u8(mut s in vec(1u32..=1_000_000u32, 1..(u8::MAX as usize))) {
            s.push(0u32);
            let mut sa = vec![0u8; s.len()];
            construct(&s, &mut sa);
            prop_assert!(is_suffix_array_of(&sa, &s));
        }
    }

    #[test]
    fn regression1() {
        // 012345678901
        // LSLSSLSSLSLS
        // 212112112120
        //             L    S    S   L S
        // LMSSubstr=121,1121,1121,120,0
        let s: Vec<u8> = vec![2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 0];
        let mut sa = vec![0u8; s.len()];
        construct(&s, &mut sa);
        assert!(is_suffix_array_of(&sa, &s));
    }

    #[test]
    fn regression2() {
        let s = vec![1, 0];
        let mut sa = vec![0u8; s.len()];
        construct(&s, &mut sa);
        assert!(is_suffix_array_of::<u8, u8>(&sa, &s));
    }

    #[test]
    fn regression3() {
        // 01234567890123
        // LSLSSLSLSSLSLS
        // 21211212112120
        //             L    S   L    S   L S
        // LMSSubstr=121,1121,121,1121,120,0
        let s = vec![2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 0];
        let mut sa = vec![0u8; s.len()];
        construct(&s, &mut sa);
        assert!(is_suffix_array_of::<u8, u8>(&sa, &s));
    }

    #[test]
    fn regression4() {
        let s = vec![
            2, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 0,
        ];
        let mut sa = vec![0u8; s.len()];
        construct(&s, &mut sa);
        assert!(is_suffix_array_of::<u8, u8>(&sa, &s));
    }

    #[test]
    fn regression5() {
        let s = vec![2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 0];
        let mut sa = vec![0u8; s.len()];
        construct(&s, &mut sa);
        assert!(is_suffix_array_of::<u8, u8>(&sa, &s));
    }

    #[test]
    #[should_panic]
    fn no_sentinel() {
        let s = vec![2u8, 1, 2, 2];
        let mut sa = vec![0u8; s.len()];
        construct(&s, &mut sa);
    }

    #[test]
    #[should_panic]
    fn empty_string() {
        let s = vec![0u8];
        let mut sa = vec![0u8; s.len()];
        construct(&s, &mut sa);
    }
}
