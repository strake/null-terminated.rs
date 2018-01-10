#![no_std]

#![feature(const_fn)]
#![feature(extern_types)]

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

pub struct Nul<A>([A; 0], Opaque);

impl<A> Nul<A> {
    #[inline]
    pub const fn as_ptr(&self) -> *const A { self as *const Self as *const A }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut A { self as *mut Self as *mut A }

    #[inline]
    pub const fn iter(&self) -> Iter<A> { Iter(self.as_ptr(), PhantomData) }

    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<A> { IterMut(self.as_mut_ptr(), PhantomData) }

    #[inline]
    pub unsafe fn new_unchecked(p: *const A) -> &'static Nul<A> {
        Self::new_unchecked_mut(p as _)
    }

    #[inline]
    pub unsafe fn new_unchecked_mut(p: *mut A) -> &'static mut Nul<A> {
        &mut *(p as *mut Nul<A>)
    }

    #[inline]
    pub fn len(&self) -> usize { unsafe {
        if 0 == mem::size_of::<A>() { return 0; }
        let mut p = self.as_ptr();
        while !is_null(&*p) { p = p.offset(1); }
        ptr_diff(p, self.as_ptr())
    } }

    #[inline]
    pub fn get(&self, i: usize) -> Option<&A> { self[..].get(i) }

    #[inline]
    pub fn get_mut(&mut self, i: usize) -> Option<&mut A> { self[..].get_mut(i) }

    #[inline]
    pub fn split_at(&self, i: usize) -> (&[A], &Self) {
        self.try_split_at(i).expect("index out of bounds")
    }

    #[inline]
    pub fn split_at_mut(&mut self, i: usize) -> (&mut [A], &mut Self) {
        self.try_split_at_mut(i).expect("index out of bounds")
    }

    #[inline]
    pub fn try_split_at(&self, i: usize) -> Option<(&[A], &Self)> {
        let mut it = self.iter();
        for _ in 0..i { if let None = it.next() { return None; } }
        Some(unsafe { (slice::from_raw_parts(self.as_ptr(), i), <&Self>::from(it)) })
    }

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

#[macro_export]
macro_rules! str0 {
    ($s:tt) => (unsafe {
        $crate::Nul::<u8>::new_unchecked_mut(concat!($s, "\0").as_ptr() as *mut _)
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
