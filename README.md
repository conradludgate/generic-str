# generic-str

The one true string type in Rust!

> This project intends to be a proof-of-concept for an idea I had a few months back.

## Explaination

Rust notoriously has a few different string types. The two main contenders are:

- `&str` which is a 'string reference'. It's non-resizable and it's mutability is limited.
- `String` which is an 'owned string'. It's resizable and can be mutated simply.

It turns out that these two strings aren't too different.
`str` is just a string that's backed by a `[u8]` byte slice.
Similarly, `String` is just a string that's [backed by a `Vec<u8>`](https://github.com/rust-lang/rust/blob/88e5ae2dd3/library/alloc/src/string.rs#L294-L296).

So why are they really different types? Couldn't we theoretically have something like

```rust
type str = StringBase<[u8]>;
type String = StringBase<Vec<u8>>;
```

So that's what this is. It's mostly up to feature parity with the standard library strings. A lot of the standard trait implementations are there too.

I've also implemented

```rust
type str32 = StringBase<[char]>;
type String32 = StringBase<Vec<char>>;
```

for utf-32 applications.

## generic-vec

So there was some [discussion about whether `Allocator` was the best abstraction for customising `Vec` storage](https://internals.rust-lang.org/t/is-custom-allocators-the-right-abstraction/13460).
I was very intrigured by this concept, and I made use of an [implementation that RustyYato contributed](https://github.com/RustyYato/generic-vec) in the thread in this project.

So, now I have

```rust
use generic_vec::{GenericVec, raw::Heap};
pub type String<A = Global> = OwnedString<u8, Heap<u8, A>>;
pub type OwnedString<U, S> = StringBase<GenericVec<U, S>>;
```

Which might look more complicated, and you'd be right, but it then allows for static allocated but resizable strings!

```rust
pub type ArrayString<const N: usize> = OwnedString<u8, UninitBuffer<[u8; N], u8>>;
```

And I get to re-use all of the same code from when implementing `String`,
because it's all implemented on the base `OwnedString` type for string manipulations that needs resizablility.
