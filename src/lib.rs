//! Library of [null-terminated slices](struct.Nul.html) and
//! [UTF-8-encoded strings](struct.NulStr.html), references to which are thin pointers for
//! efficiency and ease of use with FFI
//!
//! The likely primary use cases are C FFI and OS ABI (for example: on Unix, many system calls
//! take, and the initial environment involves, null-terminated arguments).
//!
//! As the representation is a bare pointer to the element type, one can declare foreign
//! functions which merely take arguments or return values of type `Nul<_>`, for example:
//! ```no_run
//! # extern crate null_terminated; use null_terminated::Nul; type c_int = i32;
//! extern "C" {
//!     fn strlen(_: &Nul<u8>) -> usize;
//!     fn strchr(_: &Nul<u8>, _: c_int) -> &Nul<u8>;
//! }
//! ```
//!
//! For further examples, see the docs of [`Nul`](struct.Nul.html).

#![no_std]

#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

#![feature(cfg_doctest)]
#![feature(const_fn)]
#![feature(const_raw_ptr_deref)]
#![feature(extern_types)]

extern crate fallible;
extern crate unreachable;

#[cfg(feature = "utf")]
extern crate utf;

#[cfg(test)] extern crate quickcheck;

#[cfg(test)] #[macro_use] extern crate quickcheck_macros;
#[cfg(test)] extern crate std;

use core::{cmp::*, fmt::{self, Debug, Display}, hash::{Hash, Hasher}, marker::PhantomData, mem,
           ops::*, slice};
use fallible::*;

extern { type Opaque; }
unsafe impl Send for Opaque {}
unsafe impl Sync for Opaque {}

/// Generic unsized null-terminated array
///
/// `&Nul<A>` is a thin pointer, so it can be readily used with FFI.
///
/// # Examples
///
/// One can safely take views of null-terminated slices with [`TryFrom::try_from`](../fallible/trait.TryFrom.html#tymethod.try_from):
/// ```
/// # extern crate fallible; extern crate null_terminated; use null_terminated::Nul;
/// extern "C" {
///     fn c_f(path: *const u8) -> i32;
/// }
///
/// fn f(path: &[u8]) -> Result<i32, ()> {
///     <&Nul<u8> as ::fallible::TryFrom<_>>::try_from(path)
///         .map(|path| unsafe { c_f(path.as_ptr()) })
/// }
/// ```
#[repr(C)]
pub struct Nul<A>([A; 0], Opaque);

impl<A> Nul<A> {
    /// Return a pointer to the start of the array.
    #[inline]
    pub const fn as_ptr(&self) -> *const A { self as *const Self as *const A }

    /// Return a mutable pointer to the start of the array.
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut A { self as *mut Self as *mut A }

    /// Iterate over array elements.
    #[inline]
    pub const fn iter(&self) -> Iter<A> { Iter(self.as_ptr(), PhantomData) }

    /// Iterate over array elements, mutably.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<A> { IterMut(self.as_mut_ptr(), PhantomData) }

    /// Create a reference to a null-terminated array, given a pointer to its start.
    ///
    /// The caller must make sure the argument does, in fact, point to a null-terminated array,
    /// and the returned reference not live longer than the array it refers to. These
    /// requirements are not checked.
    #[inline]
    pub const unsafe fn new_unchecked(p: *const A) -> &'static Self { &*(p as *const Nul<A>) }

    /// Create a mutable reference to a null-terminated array, given a pointer to its start.
    ///
    /// The caller must make sure the argument does, in fact, point to a null-terminated array,
    /// and the returned reference not live longer than the array it refers to. These
    /// requirements are not checked.
    #[inline]
    pub unsafe fn new_unchecked_mut(p: *mut A) -> &'static mut Self { &mut *(p as *mut Nul<A>) }

    /// Return array length. `O(n)`
    #[inline]
    pub fn len(&self) -> usize { unsafe {
        if 0 == mem::size_of::<A>() { return 0; }
        let mut p = self.as_ptr();
        while !is_null(&*p) { p = p.offset(1); }
        ptr_diff(p, self.as_ptr())
    } }

    /// Get element at given position. `O(n)` to check bounds
    #[inline]
    pub fn get(&self, i: usize) -> Option<&A> { self[..].get(i) }

    /// Get element at given position, mutably. `O(n)` to check bounds
    #[inline]
    pub fn get_mut(&mut self, i: usize) -> Option<&mut A> { self[..].get_mut(i) }

    /// Split array at given position.
    ///
    /// # Panics
    ///
    /// Panics if index out of bounds.
    #[inline]
    pub fn split_at(&self, i: usize) -> (&[A], &Self) {
        self.try_split_at(i).expect("index out of bounds")
    }

    /// Split array at given position, mutably.
    ///
    /// # Panics
    ///
    /// Panics if index out of bounds.
    #[inline]
    pub fn split_at_mut(&mut self, i: usize) -> (&mut [A], &mut Self) {
        self.try_split_at_mut(i).expect("index out of bounds")
    }

    /// Split array at given position; return `None` if index out of bounds.
    #[inline]
    pub fn try_split_at(&self, i: usize) -> Option<(&[A], &Self)> {
        let mut it = self.iter();
        for _ in 0..i { if let None = it.next() { return None; } }
        Some(unsafe { (slice::from_raw_parts(self.as_ptr(), i), <&Self>::from(it)) })
    }

    /// Split array at given position, mutably; return `None` if index out of bounds.
    #[inline]
    pub fn try_split_at_mut(&mut self, i: usize) -> Option<(&mut [A], &mut Self)> {
        let p = self.as_mut_ptr();
        let mut it = self.iter_mut();
        for _ in 0..i { if let None = it.next() { return None; } }
        Some(unsafe { (slice::from_raw_parts_mut(p, i), <&mut Self>::from(it)) })
    }
}

/// Cast.
pub const unsafe fn cast<A, B>(a: &Nul<A>) -> &Nul<B> { &*(a as *const Nul<A> as *const Nul<B>) }

impl<A, I> Index<I> for Nul<A> where [A]: Index<I> {
    type Output = <[A] as Index<I>>::Output;
    #[inline]
    fn index(&self, i: I) -> &Self::Output {
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len()).index(i) }
    }
}

impl<A, I> IndexMut<I> for Nul<A> where [A]: IndexMut<I> {
    #[inline]
    fn index_mut(&mut self, i: I) -> &mut Self::Output {
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()).index_mut(i) }
    }
}

impl<A: Debug> Debug for Nul<A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self[..].fmt(f) }
}

impl<A: PartialEq> PartialEq for Nul<A> {
    #[inline]
    fn eq(&self, other: &Self) -> bool { self[..] == other[..] }
}

impl<A: Eq> Eq for Nul<A> {}

impl<A: PartialOrd> PartialOrd for Nul<A> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        <[A]>::partial_cmp(&self[..], &other[..])
    }
}

impl<A: Ord> Ord for Nul<A> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering { <[A]>::cmp(&self[..], &other[..]) }
}

impl<A: Hash> Hash for Nul<A> {
    #[inline]
    fn hash<H: Hasher>(&self, h: &mut H) { self.iter().for_each(|a| a.hash(h)) }
}

impl<'a, A> TryFrom<&'a [A]> for &'a Nul<A> {
    type Error = ();
    #[inline]
    fn try_from(xs: &'a [A]) -> Result<Self, ()> {
        if xs.last().map_or(false, is_null) { Ok(unsafe { &*(xs.as_ptr() as *const Nul<A>) }) }
        else { Err(()) }
    }
}

impl<'a, A> TryFrom<&'a mut [A]> for &'a mut Nul<A> {
    type Error = ();
    #[inline]
    fn try_from(xs: &'a mut [A]) -> Result<Self, ()> {
        if xs.last().map_or(false, is_null) { Ok(unsafe { &mut *(xs.as_mut_ptr() as *mut Nul<A>) }) }
        else { Err(()) }
    }
}

impl<'a, A> IntoIterator for &'a Nul<A> {
    type Item = &'a A;
    type IntoIter = Iter<'a, A>;
    #[inline]
    fn into_iter(self) -> Iter<'a, A> { self.iter() }
}

impl<'a, A> IntoIterator for &'a mut Nul<A> {
    type Item = &'a mut A;
    type IntoIter = IterMut<'a, A>;
    #[inline]
    fn into_iter(self) -> IterMut<'a, A> { self.iter_mut() }
}

impl<'a, A> From<Iter<'a, A>> for &'a Nul<A> {
    #[inline]
    fn from(it: Iter<'a, A>) -> Self { unsafe { &*(it.0 as *const Nul<A>) } }
}

impl<'a, A> From<IterMut<'a, A>> for &'a mut Nul<A> {
    #[inline]
    fn from(it: IterMut<'a, A>) -> Self { unsafe { &mut *(it.0 as *mut Nul<A>) } }
}

/// Iterator over the elements of a null-terminated array
#[derive(Debug, Clone, Copy)]
pub struct Iter<'a, A: 'a>(*const A, PhantomData<&'a A>);

unsafe impl<'a, T: Sync> Send for Iter<'a, T> {}
unsafe impl<'a, T: Sync> Sync for Iter<'a, T> {}

impl<'a, A: 'a> Iterator for Iter<'a, A> {
    type Item = &'a A;
    #[inline]
    fn next(&mut self) -> Option<&'a A> { unsafe {
        if is_null(&*self.0) { None } else {
            let ptr = self.0;
            self.0 = ptr.offset(1);
            Some(&*ptr)
        }
    } }
}

/// Iterator over the elements of a mutable null-terminated array
#[derive(Debug)]
pub struct IterMut<'a, A: 'a>(*mut A, PhantomData<&'a mut A>);

unsafe impl<'a, T: Send> Send for IterMut<'a, T> {}
unsafe impl<'a, T: Sync> Sync for IterMut<'a, T> {}

impl<'a, A: 'a> Iterator for IterMut<'a, A> {
    type Item = &'a mut A;
    #[inline]
    fn next(&mut self) -> Option<&'a mut A> { unsafe {
        if is_null(&*self.0) { None } else {
            let ptr = self.0;
            self.0 = ptr.offset(1);
            Some(&mut *ptr)
        }
    } }
}

impl Display for Nul<char> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use fmt::Write;
        for &x in self { f.write_char(x)?; }
        Ok(())
    }
}

impl<A> AsRef<Nul<A>> for Nul<A> { #[inline] fn as_ref(&self) -> &Self { self } }

/// Null-terminated UTF-8 encoded string
///
/// `&NulStr` is a thin pointer, so it can be readily used with FFI.
///
/// One can convert from `&Nul<u8>` to `&NulStr` with `try_from`, which checks whether its
/// argument is valid UTF-8.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct NulStr(Nul<u8>);

impl Debug for NulStr {
    #[inline]
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result { write!(fmt, "{:?}", &self[..]) }
}

#[cfg(feature = "utf")]
impl fmt::Display for NulStr {
    #[inline]
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result { fmt.write_str(&self[..]) }
}

impl Index<RangeFull> for NulStr {
    type Output = str;

    #[inline]
    fn index(&self, _: RangeFull) -> &str { unsafe {
        ::core::str::from_utf8_unchecked(&self.0[..])
    } }
}

impl IndexMut<RangeFull> for NulStr {
    #[inline]
    fn index_mut(&mut self, _: RangeFull) -> &mut str { unsafe {
        ::core::str::from_utf8_unchecked_mut(&mut self.0[..])
    } }
}

impl NulStr {
    /// Create a reference to a null-terminated string, given a pointer to its start.
    ///
    /// The caller must make sure the argument does, in fact, point to a null-terminated string;
    /// the string is valid UTF-8; and the returned reference not live longer than the array it
    /// refers to. These requirements are not checked.
    #[inline]
    pub const unsafe fn new_unchecked(p: *const u8) -> &'static Self { &*(p as *mut Self) }

    /// Create a mutable reference to a null-terminated string, given a pointer to its start.
    ///
    /// The caller must make sure the argument does, in fact, point to a null-terminated string;
    /// the string is valid UTF-8; and the returned reference not live longer than the array it
    /// refers to. These requirements are not checked.
    #[inline]
    pub unsafe fn new_unchecked_mut(p: *mut u8) -> &'static mut Self { &mut *(p as *mut Self) }

    /// Return a slice of the UTF-8 code bytes of the string.
    #[inline]
    pub fn as_bytes(&self) -> &Nul<u8> { &self.0 }

    /// Return a mutable slice of the UTF-8 code bytes of the string.
    #[inline]
    pub fn as_bytes_mut(&mut self) -> &mut Nul<u8> { &mut self.0 }

    /// Return a pointer to the start of the string.
    #[inline]
    pub fn as_ptr(&self) -> *const u8 { self.0.as_ptr() }

    /// Return a mutable pointer to the start of the string.
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *const u8 { self.0.as_mut_ptr() }

    /// Iterate over the characters of the string.
    #[cfg(feature = "utf")]
    #[inline]
    pub fn chars(&self) -> Chars { Chars(::utf::decode_utf8(self.0.iter().cloned())) }

    /// Iterate over the characters of the string and their byte positions.
    #[cfg(feature = "utf")]
    #[inline]
    pub fn char_indices(&self) -> CharIndices { CharIndices(self.chars(), 0) }

    /// Return whether the given byte position is a character boundary.
    #[inline]
    pub fn is_char_boundary(&self, k: usize) -> bool { self[..].is_char_boundary(k) }
}

/// Iterator over the characters of a null-terminated string
#[cfg(feature = "utf")]
#[derive(Debug, Clone)]
pub struct Chars<'a>(::utf::DecodeUtf8<::core::iter::Cloned<Iter<'a, u8>>>);

#[cfg(feature = "utf")]
impl<'a> Iterator for Chars<'a> {
    type Item = char;
    #[inline]
    fn next(&mut self) -> Option<char> {
        use unreachable::UncheckedResultExt;
        self.0.next().map(|r| unsafe { r.unchecked_unwrap_ok() })
    }
}

/// Iterator over the characters of a null-terminated string and their byte positions
#[cfg(feature = "utf")]
#[derive(Debug, Clone)]
pub struct CharIndices<'a>(Chars<'a>, usize);

#[cfg(feature = "utf")]
impl<'a> Iterator for CharIndices<'a> {
    type Item = (usize, char);
    #[inline]
    fn next(&mut self) -> Option<(usize, char)> {
        let x = self.0.next()?;
        let k = self.1;
        self.1 += x.len_utf8();
        Some((k, x))
    }
}

impl<'a> TryFrom<&'a Nul<u8>> for &'a NulStr {
    type Error = ::core::str::Utf8Error;

    #[inline]
    fn try_from(s: &'a Nul<u8>) -> Result<Self, Self::Error> {
        ::core::str::from_utf8(&s[..])?;
        Ok(unsafe { NulStr::new_unchecked(s.as_ptr()) })
    }
}

impl<'a> TryFrom<&'a mut Nul<u8>> for &'a mut NulStr {
    type Error = ::core::str::Utf8Error;

    #[inline]
    fn try_from(s: &'a mut Nul<u8>) -> Result<Self, Self::Error> {
        ::core::str::from_utf8_mut(&mut s[..])?;
        Ok(unsafe { NulStr::new_unchecked_mut(s.as_mut_ptr()) })
    }
}

#[inline]
fn is_null<A>(a: &A) -> bool { unsafe {
    let l = mem::size_of_val(a);
    let p = a as *const A as *const u8;
    slice::from_raw_parts(p, l).iter().all(|&b| 0 == b)
} }

#[inline]
fn ptr_diff<A>(p: *const A, q: *const A) -> usize {
    use ::core::num::Wrapping as w;
    (w(p as usize) - w(q as usize)).0/mem::size_of::<A>()
}

/// Make a static `Nul<u8>`.
///
/// # Examples
///
/// ```
/// # extern crate null_terminated; use null_terminated::{Nul, str0}; fn main() {
/// static s: &'static Nul<u8> = str0!("Hello, world!");
/// # }
/// ```
#[macro_export]
macro_rules! str0 {
    ($s:expr) => (unsafe {
        $crate::Nul::<u8>::new_unchecked(concat!($s, "\0").as_ptr() as *mut _)
    })
}

/// Make a static `NulStr`.
///
/// # Examples
///
/// ```
/// # extern crate null_terminated; use null_terminated::{NulStr, str0_utf8}; fn main() {
/// static s: &'static NulStr = str0_utf8!("Hello, world!");
/// # }
/// ```
#[macro_export]
macro_rules! str0_utf8 {
    ($s:expr) => (unsafe {
        $crate::NulStr::new_unchecked(concat!($s, "\0").as_ptr() as *mut _)
    })
}


/// Constructs a `&Nul<&T>`.
///
/// # Examples
///
/// ```
/// # extern crate null_terminated;
/// # use null_terminated::{Nul,NulStr,nul_of_ref,str0_utf8};
///
/// static INTS: &Nul<&u32> = nul_of_ref![&0, &1, &2, &3];
/// static STRS: &Nul<&NulStr> =
///     nul_of_ref![str0_utf8!("foo"), str0_utf8!("bar"), str0_utf8!("baz")];
///
/// # fn main() {
/// assert_eq!( INTS[..], [&0, &1, &2, &3] );
/// assert_eq!( STRS[..], [str0_utf8!("foo"), str0_utf8!("bar"), str0_utf8!("baz")] );
/// # }
/// ```
///
#[macro_export]
macro_rules! nul_of_ref {
    ($($reference:expr),* $(,)?) => (unsafe {
        enum Opt<T> { Nil, Just(T) }
        #[inline(always)]
        const unsafe fn cast_helper<'a, 'b, A: ?Sized>(a: &'b Nul<Opt<&'a A>>) -> &'b Nul<&'a A> { $crate::cast(a) }
        cast_helper($crate::Nul::new_unchecked([$(Opt::Just($reference),)* Opt::Nil].as_ptr()))
    })
}

/// ```compile_fail
/// # extern crate null_terminated;
/// # use null_terminated::{Nul,nul_of_ref};
/// static VOIDS: &Nul<&std::convert::Infallible> = nul_of_ref![&()];
/// ```
/// ```compile_fail
/// # extern crate null_terminated;
/// # use null_terminated::{Nul,nul_of_ref};
/// static VOIDS: &Nul<&std::convert::Infallible> = nul_of_ref![&0usize];
/// ```
/// ```compile_fail
/// # extern crate null_terminated;
/// # use null_terminated::{Nul,nul_of_ref};
/// static BOOLS: &Nul<&bool> = nul_of_ref![&()];
/// ```
#[cfg(doctest)]
pub struct NoNulOfRefInvalid;

#[cfg(test)]
mod tests {
    use super::*;

    #[quickcheck]
    fn test(mut xs: ::std::vec::Vec<usize>) -> bool {
        xs.push(0);
        let l = xs.iter().take_while(|&&x| 0usize != x).count();
        xs[0..l] == <&Nul<_>>::try_from(&xs[..]).unwrap()[..]
    }

    #[quickcheck]
    fn iter(mut xs: ::std::vec::Vec<usize>) -> bool {
        xs.push(0);
        let l = xs.iter().take_while(|&&x| 0usize != x).count();
        Iterator::eq(xs.iter().take(l), <&Nul<_>>::try_from(&xs[..]).unwrap().iter())
    }
}
