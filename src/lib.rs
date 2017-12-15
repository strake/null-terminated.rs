#![no_std]

extern crate fallible;
extern crate idem;

use core::mem;
use core::ops::*;
use core::slice;
use fallible::*;
use idem::dec::Zero;

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Slice<A>([A]);

impl<A> Slice<A> {
    #[inline]
    pub fn as_ptr(&self) -> *const A { &self[0] }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut A { &mut self[0] }
}

impl<A: Zero> Slice<A> {
    #[inline]
    pub unsafe fn from_ptr(ptr: *const A) -> &'static Self { Self::from_mut_ptr(ptr as _) }

    #[inline]
    pub unsafe fn from_mut_ptr(ptr: *mut A) -> &'static mut Self {
        let mut i = 0;
        while !(*ptr.offset(i)).is_zero() { i += 1; }
        mem::transmute(slice::from_raw_parts_mut(ptr, (i as usize)+1))
    }
}

impl<'a, A: Zero> TryFrom<&'a [A]> for &'a Slice<A> {
    type Error = ();
    #[inline]
    fn try_from(xs: &'a [A]) -> Result<Self, ()> {
        if xs.last().map(A::is_zero).unwrap_or(false) { Ok(unsafe { mem::transmute(xs) }) }
        else { Err(()) }
    }
}

impl<'a, A: Zero> TryFrom<&'a mut [A]> for &'a mut Slice<A> {
    type Error = ();
    #[inline]
    fn try_from(xs: &'a mut [A]) -> Result<Self, ()> {
        if xs.last().map(A::is_zero).unwrap_or(false) { Ok(unsafe { mem::transmute(xs) }) }
        else { Err(()) }
    }
}

impl<A> Deref for Slice<A> {
    type Target = [A];
    #[inline]
    fn deref(&self) -> &[A] { &self.0[0..self.0.len()-1] }
}

impl<A> DerefMut for Slice<A> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [A] { let l = self.0.len(); &mut self.0[0..l-1] }
}
