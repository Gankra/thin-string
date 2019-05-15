// #![feature(const_slice_len)]
#[feature(try_reserve)]

use std::string::FromUtf16Error;
#[cfg(feature = "nightly_try_reserve")]
use std::collections::CollectionAllocErr;
use core::ptr;
use core::fmt;
use core::hash;
use core::str;
use core::iter::FromIterator;
use core::ops::{self, Add, AddAssign, Index, IndexMut};
use core::str::Utf8Error;

use thin_vec::ThinVec;

pub struct ThinString {
    vec: ThinVec<u8>,
}

#[derive(Debug)]
pub struct FromUtf8Error {
    bytes: ThinVec<u8>,
    error: Utf8Error,
}

impl ThinString {
    pub fn new() -> Self {
        Self { vec: ThinVec::new() }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self { vec: ThinVec::with_capacity(capacity) }
    }

    pub fn from_utf8(vec: ThinVec<u8>) -> Result<ThinString, FromUtf8Error> {
        match str::from_utf8(&vec) {
            Ok(..) => Ok(ThinString { vec }),
            Err(e) => {
                Err(FromUtf8Error {
                    bytes: vec,
                    error: e,
                })
            }
        }
    }
/*
    pub fn from_utf8_lossy<'a>(v: &'a [u8]) -> Cow<'a, str> { unimplemented!() }
*/
    pub fn from_utf16(v: &[u16]) -> Result<Self, FromUtf16Error> { unimplemented!() }
    pub fn from_utf16_lossy(v: &[u16]) -> Self { unimplemented!() }
    pub fn from_raw_parts(buf: *const u8) -> Self { unimplemented!() }
    pub unsafe fn from_utf8_unchecked(bytes: ThinVec<u8>) -> Self {
        ThinString { vec: bytes }
    }
    pub fn into_bytes(self) -> ThinVec<u8> {
        self.vec
    }
    pub fn as_str(&self) -> &str {
        self
    }
    pub fn as_mut_str(&mut self) -> &mut str {
        unimplemented!()
    }

    pub fn push_str(&mut self, other: &str) {
        self.vec.extend_from_slice(other.as_bytes())
    }

    pub fn reserve(&mut self, additional: usize) {
        self.vec.reserve(additional)
    }

    pub fn reserve_exact(&mut self, additional: usize) {
        self.vec.reserve_exact(additional)
    }

    #[cfg(feature = "nightly_try_reserve")]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), CollectionAllocErr> {
        self.vec.try_reserve(additional)
    }

    #[cfg(feature = "nightly_try_reserve")]
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), CollectionAllocErr>  {
        self.vec.try_reserve_exact(additional)
    }

    pub fn shrink_to_fit(&mut self) {
        self.vec.shrink_to_fit()
    }

    pub fn push(&mut self, ch: char) {
        match ch.len_utf8() {
            1 => self.vec.push(ch as u8),
            _ => self.vec.extend_from_slice(ch.encode_utf8(&mut [0; 4]).as_bytes()),
        }
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.vec
    }

    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            assert!(self.is_char_boundary(new_len));
            self.vec.truncate(new_len)
        }
    }

    pub fn pop(&mut self) -> Option<char> {
        let ch = self.chars().rev().next()?;
        let newlen = self.len() - ch.len_utf8();
        unsafe {
            self.vec.set_len(newlen);
        }
        Some(ch)
    }

    pub fn remove(&mut self, idx: usize) -> char {
        let ch = match self[idx..].chars().next() {
            Some(ch) => ch,
            None => panic!("cannot remove a char from the end of a string"),
        };

        let next = idx + ch.len_utf8();
        let len = self.len();
        unsafe {
            ptr::copy(self.vec.as_ptr().add(next),
                      self.vec.as_mut_ptr().add(idx),
                      len - next);
            self.vec.set_len(len - (next - idx));
        }
        ch
    }

    pub fn retain<F>(&mut self, mut f: F)
        where F: FnMut(char) -> bool
    {
        let len = self.len();
        let mut del_bytes = 0;
        let mut idx = 0;

        while idx < len {
            let ch = unsafe {
                self.get_unchecked(idx..len).chars().next().unwrap()
            };
            let ch_len = ch.len_utf8();

            if !f(ch) {
                del_bytes += ch_len;
            } else if del_bytes > 0 {
                unsafe {
                    ptr::copy(self.vec.as_ptr().add(idx),
                              self.vec.as_mut_ptr().add(idx - del_bytes),
                              ch_len);
                }
            }

            // Point idx to the next char
            idx += ch_len;
        }

        if del_bytes > 0 {
            unsafe { self.vec.set_len(len - del_bytes); }
        }
    }

    pub fn insert(&mut self, idx: usize, ch: char) {
        assert!(self.is_char_boundary(idx));
        let mut bits = [0; 4];
        let bits = ch.encode_utf8(&mut bits).as_bytes();

        unsafe {
            self.insert_bytes(idx, bits);
        }
    }

    unsafe fn insert_bytes(&mut self, idx: usize, bytes: &[u8]) {
        let len = self.len();
        let amt = bytes.len();
        self.vec.reserve(amt);

        ptr::copy(self.vec.as_ptr().add(idx),
                  self.vec.as_mut_ptr().add(idx + amt),
                  len - idx);
        ptr::copy(bytes.as_ptr(),
                  self.vec.as_mut_ptr().add(idx),
                  amt);
        self.vec.set_len(len + amt);
    }

    pub fn insert_str(&mut self, idx: usize, string: &str) {
        assert!(self.is_char_boundary(idx));

        unsafe {
            self.insert_bytes(idx, string.as_bytes());
        }
    }

    pub unsafe fn as_mut_vec(&mut self) -> &mut ThinVec<u8> {
        &mut self.vec
    }

    pub fn len(&self) -> usize {
        self.vec.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn split_off(&mut self, at: usize) -> ThinString {
        assert!(self.is_char_boundary(at));
        let other = self.vec.split_off(at);
        unsafe { ThinString::from_utf8_unchecked(other) }
    }

    pub fn clear(&mut self) {
        self.vec.clear()
    }
}

impl Clone for ThinString {
    fn clone(&self) -> Self {
        ThinString { vec: self.vec.clone() }
    }

    fn clone_from(&mut self, source: &Self) {
        self.vec.clone_from(&source.vec);
    }
}


impl FromIterator<char> for ThinString {
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> Self {
        let mut buf = Self::new();
        buf.extend(iter);
        buf
    }
}


impl<'a> FromIterator<&'a char> for ThinString {
    fn from_iter<I: IntoIterator<Item = &'a char>>(iter: I) -> Self {
        let mut buf = Self::new();
        buf.extend(iter);
        buf
    }
}


impl<'a> FromIterator<&'a str> for ThinString {
    fn from_iter<I: IntoIterator<Item = &'a str>>(iter: I) -> Self {
        let mut buf = Self::new();
        buf.extend(iter);
        buf
    }
}


impl FromIterator<ThinString> for ThinString {
    fn from_iter<I: IntoIterator<Item = ThinString>>(iter: I) -> Self {
        let mut iterator = iter.into_iter();

        // Because we're iterating over `String`s, we can avoid at least
        // one allocation by getting the first string from the iterator
        // and appending to it all the subsequent strings.
        match iterator.next() {
            None => Self::new(),
            Some(mut buf) => {
                buf.extend(iterator);
                buf
            }
        }
    }
}

impl Extend<char> for ThinString {
    fn extend<I: IntoIterator<Item = char>>(&mut self, iter: I) {
        let iterator = iter.into_iter();
        let (lower_bound, _) = iterator.size_hint();
        self.reserve(lower_bound);
        iterator.for_each(move |c| self.push(c));
    }
}


impl<'a> Extend<&'a char> for ThinString {
    fn extend<I: IntoIterator<Item = &'a char>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }
}


impl<'a> Extend<&'a str> for ThinString {
    fn extend<I: IntoIterator<Item = &'a str>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(s));
    }
}


impl Extend<ThinString> for ThinString {
    fn extend<I: IntoIterator<Item = ThinString>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(&s));
    }
}

impl PartialEq for ThinString {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        PartialEq::eq(&self[..], &other[..])
    }
    #[inline]
    fn ne(&self, other: &Self) -> bool {
        PartialEq::ne(&self[..], &other[..])
    }
}

macro_rules! impl_eq {
    ($lhs:ty, $rhs: ty) => {

        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool { PartialEq::eq(&self[..], &other[..]) }
            #[inline]
            fn ne(&self, other: &$rhs) -> bool { PartialEq::ne(&self[..], &other[..]) }
        }


        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool { PartialEq::eq(&self[..], &other[..]) }
            #[inline]
            fn ne(&self, other: &$lhs) -> bool { PartialEq::ne(&self[..], &other[..]) }
        }

    }
}

impl_eq! { ThinString, str }
impl_eq! { ThinString, &'a str }

impl Default for ThinString {
    /// Creates an empty `String`.
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}


impl fmt::Display for ThinString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}


impl fmt::Debug for ThinString {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}


impl hash::Hash for ThinString {
    #[inline]
    fn hash<H: hash::Hasher>(&self, hasher: &mut H) {
        (**self).hash(hasher)
    }
}

/// Implements the `+` operator for concatenating two strings.
///
/// This consumes the `ThinString` on the left-hand side and re-uses its buffer (growing it if
/// necessary). This is done to avoid allocating a new `ThinString` and copying the entire contents on
/// every operation, which would lead to `O(n^2)` running time when building an `n`-byte string by
/// repeated concatenation.

impl Add<&str> for ThinString {
    type Output = ThinString;

    #[inline]
    fn add(mut self, other: &str) -> Self {
        self.push_str(other);
        self
    }
}

/// Implements the `+=` operator for appending to a `String`.
///
/// This has the same behavior as the [`push_str`][String::push_str] method.

impl AddAssign<&str> for ThinString {
    #[inline]
    fn add_assign(&mut self, other: &str) {
        self.push_str(other);
    }
}


impl ops::Index<ops::Range<usize>> for ThinString {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::Range<usize>) -> &str {
        &self[..][index]
    }
}

impl ops::Index<ops::RangeTo<usize>> for ThinString {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::RangeTo<usize>) -> &str {
        &self[..][index]
    }
}

impl ops::Index<ops::RangeFrom<usize>> for ThinString {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::RangeFrom<usize>) -> &str {
        &self[..][index]
    }
}

impl ops::Index<ops::RangeFull> for ThinString {
    type Output = str;

    #[inline]
    fn index(&self, _index: ops::RangeFull) -> &str {
        unsafe { str::from_utf8_unchecked(&self.vec) }
    }
}

impl ops::Index<ops::RangeInclusive<usize>> for ThinString {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::RangeInclusive<usize>) -> &str {
        Index::index(&**self, index)
    }
}

impl ops::Index<ops::RangeToInclusive<usize>> for ThinString {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::RangeToInclusive<usize>) -> &str {
        Index::index(&**self, index)
    }
}


impl ops::IndexMut<ops::Range<usize>> for ThinString {
    #[inline]
    fn index_mut(&mut self, index: ops::Range<usize>) -> &mut str {
        &mut self[..][index]
    }
}

impl ops::IndexMut<ops::RangeTo<usize>> for ThinString {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeTo<usize>) -> &mut str {
        &mut self[..][index]
    }
}

impl ops::IndexMut<ops::RangeFrom<usize>> for ThinString {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeFrom<usize>) -> &mut str {
        &mut self[..][index]
    }
}

impl ops::IndexMut<ops::RangeFull> for ThinString {
    #[inline]
    fn index_mut(&mut self, _index: ops::RangeFull) -> &mut str {
        unsafe { str::from_utf8_unchecked_mut(&mut *self.vec) }
    }
}

impl ops::IndexMut<ops::RangeInclusive<usize>> for ThinString {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeInclusive<usize>) -> &mut str {
        IndexMut::index_mut(&mut **self, index)
    }
}

impl ops::IndexMut<ops::RangeToInclusive<usize>> for ThinString {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeToInclusive<usize>) -> &mut str {
        IndexMut::index_mut(&mut **self, index)
    }
}


impl ops::Deref for ThinString {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        unsafe { str::from_utf8_unchecked(&self.vec) }
    }
}


impl ops::DerefMut for ThinString {
    #[inline]
    fn deref_mut(&mut self) -> &mut str {
        unsafe { str::from_utf8_unchecked_mut(&mut *self.vec) }
    }
}

impl AsRef<str> for ThinString {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

impl AsRef<[u8]> for ThinString {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl From<&str> for ThinString {
    #[inline]
    fn from(s: &str) -> Self {
        let mut buf = Self::new();
        buf.push_str(s);
        buf
    }
}

impl From<ThinString> for ThinVec<u8> {
    fn from(s: ThinString) -> Self {
        s.into_bytes()
    }
}

impl fmt::Write for ThinString {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.push_str(s);
        Ok(())
    }

    #[inline]
    fn write_char(&mut self, c: char) -> fmt::Result {
        self.push(c);
        Ok(())
    }
}



impl FromUtf8Error {
    /// Returns a slice of [`u8`]s bytes that were attempted to convert to a `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // some invalid bytes, in a vector
    /// let bytes = vec![0, 159];
    ///
    /// let value = String::from_utf8(bytes);
    ///
    /// assert_eq!(&[0, 159], value.unwrap_err().as_bytes());
    /// ```
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..]
    }

    /// Returns the bytes that were attempted to convert to a `String`.
    ///
    /// This method is carefully constructed to avoid allocation. It will
    /// consume the error, moving out the bytes, so that a copy of the bytes
    /// does not need to be made.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // some invalid bytes, in a vector
    /// let bytes = vec![0, 159];
    ///
    /// let value = String::from_utf8(bytes);
    ///
    /// assert_eq!(vec![0, 159], value.unwrap_err().into_bytes());
    /// ```

    pub fn into_bytes(self) -> ThinVec<u8> {
        self.bytes
    }

    /// Fetch a `Utf8Error` to get more details about the conversion failure.
    ///
    /// The [`Utf8Error`] type provided by [`std::str`] represents an error that may
    /// occur when converting a slice of [`u8`]s to a [`&str`]. In this sense, it's
    /// an analogue to `FromUtf8Error`. See its documentation for more details
    /// on using it.
    ///
    /// [`Utf8Error`]: ../../std/str/struct.Utf8Error.html
    /// [`std::str`]: ../../std/str/index.html
    /// [`u8`]: ../../std/primitive.u8.html
    /// [`&str`]: ../../std/primitive.str.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // some invalid bytes, in a vector
    /// let bytes = vec![0, 159];
    ///
    /// let error = String::from_utf8(bytes).unwrap_err().utf8_error();
    ///
    /// // the first byte is invalid here
    /// assert_eq!(1, error.valid_up_to());
    /// ```

    pub fn utf8_error(&self) -> Utf8Error {
        self.error
    }
}

impl fmt::Display for FromUtf8Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

/*
macro_rules! lit {
    ($literal: expr) => { {
        // TODO: grab some of this stuff from thin_vec?

        #[repr(C)]
        struct Literal<T> {
            header: Header,
            data: T,
        }

        #[repr(C)]
        struct Header {
            len: usize,
            cap: usize,
        }

        static LIT: Literal<[u8; $literal.len()]> = Literal {
            header: Header {
                len: $literal.len(),
                cap: 0,
            },
            data: *$literal,
        };

        $crate::ThinString { buf: from_raw_header(&LIT.header }
    } }
}

#[cfg(test)]
mod test {
    fn test_basic() {

        let string = lit!(b"hello!");

        println!("{}", &*string);
    }
}
*/
