#![no_main]
#![feature(nll)]

extern crate null_terminated;
extern crate syscall;
use null_terminated::Nul;
use syscall::syscall;

#[no_mangle]
extern "C" fn main(_: isize, args: &'static Nul<&'static Nul<u8>>) -> isize {
    let mut n_flag = false;
    let mut argi = args.iter().peekable();
    loop {
        argi.next();
        let arg = match argi.peek() {
            None => break,
            Some(arg) => arg,
        };
        if Some(b'-') != arg.get(0).map(Clone::clone) { break }
        for flag in arg.iter().skip(1) {
            match flag {
                b'n' => n_flag = true,
                _ => {
                    write(2, "Usage: echo [-n] <arg>...".as_bytes());
                    return 1;
                }
            }
        }
    }
    let mut c = 0;
    for (k, arg) in argi.enumerate() {
        if k > 0 { c |= write(1, " ".as_bytes()); }
        c |= dputs(arg, 1);
    }
    if !n_flag { c |= write(1, "\n".as_bytes()); }
    c
}

fn dputs(s: &Nul<u8>, fd: isize) -> isize { write(fd, &s[..]) }

fn write(fd: isize, bs: &[u8]) -> isize {
    unsafe { syscall!(WRITE, fd, bs.as_ptr(), bs.len()) as _ }
}
