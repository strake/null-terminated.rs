#![no_std]

#![feature(const_fn)]
#![feature(extern_types)]

extern crate fallible;
extern crate idem;

use core::cmp::*;
use core::fmt::{self, Debug, Display};
use core::marker::PhantomData;
use core::mem;
use core::ops::*;
use core::slice;
use fallible::*;
use idem::dec::Zero;

extern { type Opaque; }

pub struct Nul<A>([A; 0], Opaque);

impl<A> Nul<A> {
    #[inline]
    pub const fn as_ptr(&self) -> *const A { &self.0[0] as *const A as *mut A }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut A { &mut self.0[0] as *mut A }

    #[inline]
    pub const fn iter(&self) -> Iter<A> { Iter(self.as_ptr(), PhantomData) }

    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<A> { IterMut(self.as_mut_ptr(), PhantomData) }
}

impl<A: Zero> Nul<A> {
    #[inline]
    pub fn len(&self) -> usize { unsafe {
        if 0 == mem::size_of::<A>() { return 0; }
        let mut p = self.as_ptr();
        while !(*p).is_zero() { p = p.offset(1); }
        ptr_diff(p, self.as_ptr())
    } }

    #[inline]
    pub fn get(&self, i: usize) -> Option<&A> { self[..].get(i) }

    #[inline]
    pub fn get_mut(&mut self, i: usize) -> Option<&mut A> { self[..].get_mut(i) }
}

impl<A: Zero, I> Index<I> for Nul<A> where [A]: Index<I> {
    type Output = <[A] as Index<I>>::Output;
    #[inline]
    fn index(&self, i: I) -> &Self::Output {
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len()).index(i) }
    }
}

impl<A: Zero, I> IndexMut<I> for Nul<A> where [A]: IndexMut<I> {
    #[inline]
    fn index_mut(&mut self, i: I) -> &mut Self::Output {
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()).index_mut(i) }
    }
}

impl<A: Zero + Debug> Debug for Nul<A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self[..].fmt(f) }
}

impl<A: Zero + PartialEq> PartialEq for Nul<A> {
    #[inline]
    fn eq(&self, other: &Self) -> bool { self[..] == other[..] }
}

impl<A: Zero + Eq> Eq for Nul<A> {}

impl<A: Zero + PartialOrd> PartialOrd for Nul<A> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        <[A]>::partial_cmp(&self[..], &other[..])
    }
}

impl<A: Zero + Ord> Ord for Nul<A> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering { <[A]>::cmp(&self[..], &other[..]) }
}

impl<'a, A: Zero> TryFrom<&'a [A]> for &'a Nul<A> {
    type Error = ();
    #[inline]
    fn try_from(xs: &'a [A]) -> Result<Self, ()> {
        if xs.last().map(A::is_zero).unwrap_or(false) { Ok(unsafe { mem::transmute(&xs[0]) }) }
        else { Err(()) }
    }
}

impl<'a, A: Zero> TryFrom<&'a mut [A]> for &'a mut Nul<A> {
    type Error = ();
    #[inline]
    fn try_from(xs: &'a mut [A]) -> Result<Self, ()> {
        if xs.last().map(A::is_zero).unwrap_or(false) {
            Ok(unsafe { mem::transmute(&mut xs[0]) })
        } else { Err(()) }
    }
}

impl<'a, A: Zero> IntoIterator for &'a Nul<A> {
    type Item = &'a A;
    type IntoIter = Iter<'a, A>;
    #[inline]
    fn into_iter(self) -> Iter<'a, A> { self.iter() }
}

impl<'a, A: Zero> IntoIterator for &'a mut Nul<A> {
    type Item = &'a mut A;
    type IntoIter = IterMut<'a, A>;
    #[inline]
    fn into_iter(self) -> IterMut<'a, A> { self.iter_mut() }
}

#[derive(Clone)]
pub struct Iter<'a, A: 'a>(*const A, PhantomData<&'a A>);

unsafe impl<'a, T: Sync> Send for Iter<'a, T> {}
unsafe impl<'a, T: Sync> Sync for Iter<'a, T> {}

impl<'a, A: 'a + Zero> Iterator for Iter<'a, A> {
    type Item = &'a A;
    #[inline]
    fn next(&mut self) -> Option<&'a A> { unsafe {
        if (*self.0).is_zero() { None } else {
            let ptr = self.0;
            self.0 = ptr.offset(1);
            Some(&*ptr)
        }
    } }
}

pub struct IterMut<'a, A: 'a>(*mut A, PhantomData<&'a mut A>);

unsafe impl<'a, T: Send> Send for IterMut<'a, T> {}
unsafe impl<'a, T: Sync> Sync for IterMut<'a, T> {}

impl<'a, A: 'a + Zero> Iterator for IterMut<'a, A> {
    type Item = &'a mut A;
    #[inline]
    fn next(&mut self) -> Option<&'a mut A> { unsafe {
        if (*self.0).is_zero() { None } else {
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

#[inline]
fn ptr_diff<A>(p: *const A, q: *const A) -> usize {
    use ::core::num::Wrapping as w;
    (w(p as usize) - w(q as usize)).0/mem::size_of::<A>()
}
