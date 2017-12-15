#![no_std]

extern crate fallible;
extern crate idem;

use core::mem;
use fallible::*;
use idem::dec::Zero;

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Slice<A>([A]);

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
