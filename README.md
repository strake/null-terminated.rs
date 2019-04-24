# null-terminated

Library of [null-terminated slices](struct.Nul.html) and
[UTF-8-encoded strings](struct.NulStr.html), references to which are thin pointers for
efficiency and ease of use with FFI

The likely primary use cases are C FFI and OS ABI (for example: on Unix, many system calls
take, and the initial environment involves, null-terminated arguments).

As the representation is a bare pointer to the element type, one can declare foreign
functions which merely take arguments or return values of type `Nul<_>`, for example:
```rust
extern "C" {
    fn strlen(_: &Nul<u8>) -> usize;
    fn strchr(_: &Nul<u8>, _: c_int) -> &Nul<u8>;
}
```

For further examples, see the docs of [`Nul`](struct.Nul.html).

License: MIT OR Apache-2.0
