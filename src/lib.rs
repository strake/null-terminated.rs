//! See [`Nul`](struct.Nul.html).

#![no_std]

#![feature(const_fn)]
#![feature(extern_types)]
#![feature(untagged_unions)]

#![cfg_attr(test, feature(custom_attribute))]
#![cfg_attr(test, feature(plugin))]

#![cfg_attr(test, plugin(quickcheck_macros))]

extern crate fallible;

#[cfg(test)] extern crate quickcheck;
#[cfg(test)] #[macro_use]
             extern crate std;

use core::cmp::*;
use core::fmt::{self, Debug, Display};
use core::marker::PhantomData;
use core::mem;
use core::ops::*;
use core::slice;
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
    #[inline]
    pub const fn as_ptr(&self) -> *const A { self as *const Self as *const A }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut A { self as *mut Self as *mut A }

    /// Iterate over array elements.
    #[inline]
    pub const fn iter(&self) -> Iter<A> { Iter(self.as_ptr(), PhantomData) }

    /// Iterate over array elements, mutably.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<A> { IterMut(self.as_mut_ptr(), PhantomData) }

    #[inline]
    pub const unsafe fn new_unchecked(p: *const A) -> &'static Nul<A> {
        union U<A: 'static> { p: *const A, q: &'static Nul<A> }
        U { p }.q
    }

    #[inline]
    pub unsafe fn new_unchecked_mut(p: *mut A) -> &'static mut Nul<A> {
        &mut *(p as *mut Nul<A>)
    }

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

impl<'a, A> TryFrom<&'a [A]> for &'a Nul<A> {
    type Error = ();
    #[inline]
    fn try_from(xs: &'a [A]) -> Result<Self, ()> {
        if xs.last().map_or(false, is_null) { Ok(unsafe { mem::transmute(&xs[0]) }) }
        else { Err(()) }
    }
}

impl<'a, A> TryFrom<&'a mut [A]> for &'a mut Nul<A> {
    type Error = ();
    #[inline]
    fn try_from(xs: &'a mut [A]) -> Result<Self, ()> {
        if xs.last().map_or(false, is_null) { Ok(unsafe { mem::transmute(&mut xs[0]) }) }
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

#[derive(Clone, Copy)]
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
        for &x in self { try!(f.write_char(x)); }
        Ok(())
    }
}

impl<A> AsRef<Nul<A>> for Nul<A> { #[inline] fn as_ref(&self) -> &Self { self } }

#[derive(PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct NulStr(Nul<u8>);

impl Debug for NulStr {
    #[inline]
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result { write!(fmt, "{:?}", &self[..]) }
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
    #[inline]
    pub const unsafe fn new_unchecked(p: *const u8) -> &'static Self {
        union U<A: 'static> { p: *const A, q: &'static NulStr }
        U { p }.q
    }

    #[inline]
    pub unsafe fn new_unchecked_mut(p: *mut u8) -> &'static mut Self { &mut *(p as *mut Self) }

    #[inline]
    pub fn as_bytes(&self) -> &Nul<u8> { &self.0 }

    #[inline]
    pub fn as_bytes_mut(&mut self) -> &mut Nul<u8> { &mut self.0 }

    #[inline]
    pub fn as_ptr(&self) -> *const u8 { self.0.as_ptr() }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *const u8 { self.0.as_mut_ptr() }

    #[inline]
    pub fn chars(&self) -> ::core::str::Chars { self[..].chars() }

    #[inline]
    pub fn char_indices(&self) -> ::core::str::CharIndices { self[..].char_indices() }

    #[inline]
    pub fn is_char_boundary(&self, k: usize) -> bool { self[..].is_char_boundary(k) }
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
/// # #![feature(const_str_as_ptr)] #[macro_use] extern crate null_terminated; use null_terminated::Nul; fn main() {
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
/// # #![feature(const_str_as_ptr)] #[macro_use] extern crate null_terminated; use null_terminated::NulStr; fn main() {
/// static s: &'static NulStr = str0_utf8!("Hello, world!");
/// # }
/// ```
#[macro_export]
macro_rules! str0_utf8 {
    ($s:expr) => (unsafe {
        $crate::NulStr::new_unchecked(concat!($s, "\0").as_ptr() as *mut _)
    })
}

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
