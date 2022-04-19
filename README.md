# async-ops

[![CI](https://github.com/saserr/async-ops/actions/workflows/CI.yml/badge.svg)](https://github.com/saserr/async-ops/actions/workflows/CI.yml)
[![codecov](https://codecov.io/gh/saserr/async-ops/branch/main/graph/badge.svg?token=2K2DABXJMS)](https://codecov.io/gh/saserr/async-ops)
[![License](https://img.shields.io/badge/license-Apache--2.0_OR_MIT-blue.svg)](
https://github.com/saserr/async-ops)

This crate provides a way to use
[some `std::ops` traits](#supported-stdops-traits) with `Futures`. To be able to
use a `std::ops` trait with a `Future`, first you need to wrap the `Future`
with `Async` using `async_ops::on`. Then, as long the `Future::Output` type
implements a supported `std::ops` trait, then the same `std::ops` trait will be
implemented by the `Async` instance.

Another option is to wrap a `Future` with `Async` using `async_ops::assignable!`
to enable usage of the `Assign` variants of `std::ops` traits on the `Future`.

## Example

When writing `async` code it is common to do operations that are supported
through `std::ops`. For example, adding to numbers might look like this:

```rust
use futures_executor::block_on;

// Immediately returning a number is done for simplicity and production code
// wouldn't just immediately return a value.
let a = async { 40 };
let b = async { 2 };

let result = async { a.await + b.await };

assert_eq!(42, block_on(result));
```

Actually, the above code is not optimally implemented because `a` and `b` are
`await`-ed sequentially, instead of concurrently. The appropriate solution is to
use `join!` to be able to concurrently `await` both values like this:

```rust
use futures_executor::block_on;
use futures_util::join;

let a = async { 40 };
let b = async { 2 };

let result = async {
  let (a, b) = join!(a, b);
  a + b
};

assert_eq!(42, block_on(result));
```

Or, just use `async_ops::on` to do the same thing like the above example in one
line:

```rust
use futures_executor::block_on;

let a = async { 40 };
let b = async { 2 };

let result = async { (async_ops::on(a) + b).await };

assert_eq!(42, block_on(result));
```

Note that the `async_ops::on` example will also concurrently `await` both
values.

## Supported `std::ops` traits

<details>
<summary><b>Add</b></summary>

`Async` implements `Add<Rhs> where Rhs: Future` when the wrapped
`Future::Output` type implements `Add<Rhs::Output>`. The resulting type of the
addition is
`Async<impl Future<Output = <Future::Output as Add<Rhs::Output>>::Output>>`.

```rust
use futures_executor::block_on;

let a = async { 40 };
let b = async { 2 };

let result = async { (async_ops::on(a) + b).await };

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>AddAssign</b></summary>

`Async` implements `AddAssign<Rhs> where Rhs: Future` when the wrapped `Future`
type implements `Assignable<<Async<Future> as Add<Rhs>>::Output>`, which in turn
requires the `Future::Output` type to implement `Add<Rhs::Output>`.

```rust
use futures_executor::block_on;

let a = async { 40 };
let b = async { 2 };

let result = async {
  async_ops::assignable!(a);
  a += b;
  a.await
};

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>BitAnd</b></summary>

`Async` implements `BitAnd<Rhs> where Rhs: Future` when the wrapped
`Future::Output` type implements `BitAnd<Rhs::Output>`. The resulting type of
the bitwise and is
`Async<impl Future<Output = <Future::Output as BitAnd<Rhs::Output>>::Output>>`.

```rust
use futures_executor::block_on;

let a = async { 110 };
let b = async { 59 };

let result = async { (async_ops::on(a) & b).await };

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>BitAndAssign</b></summary>

`Async` implements `BitAndAssign<Rhs> where Rhs: Future` when the wrapped
`Future` type implements `Assignable<<Async<Future> as BitAnd<Rhs>>::Output>`,
which in turn requires the `Future::Output` type to implement
`BitAnd<Rhs::Output>`.

```rust
use futures_executor::block_on;

let a = async { 110 };
let b = async { 59 };

let result = async {
  async_ops::assignable!(a);
  a &= b;
  a.await
};

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>BitOr</b></summary>

`Async` implements `BitOr<Rhs> where Rhs: Future` when the wrapped
`Future::Output` type implements `BitOr<Rhs::Output>`. The resulting type of the
bitwise or is
`Async<impl Future<Output = <Future::Output as BitOr<Rhs::Output>>::Output>>`.

```rust
use futures_executor::block_on;

let a = async { 40 };
let b = async { 10 };

let result = async { (async_ops::on(a) | b).await };

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>BitOrAssign</b></summary>

`Async` implements `BitOrAssign<Rhs> where Rhs: Future` when the wrapped
`Future` type implements `Assignable<<Async<Future> as BitOr<Rhs>>::Output>`,
which in turn requires the `Future::Output` type to implement
`BitOr<Rhs::Output>`.

```rust
use futures_executor::block_on;

let a = async { 40 };
let b = async { 10 };

let result = async {
  async_ops::assignable!(a);
  a |= b;
  a.await
};

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>BitXor</b></summary>

`Async` implements `BitXor<Rhs> where Rhs: Future` when the wrapped
`Future::Output` type implements `BitXor<Rhs::Output>`. The resulting type of
the bitwise xor is
`Async<impl Future<Output = <Future::Output as BitXor<Rhs::Output>>::Output>>`.

```rust
use futures_executor::block_on;

let a = async { 38 };
let b = async { 12 };

let result = async { (async_ops::on(a) ^ b).await };

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>BitXorAssign</b></summary>

`Async` implements `BitXorAssign<Rhs> where Rhs: Future` when the wrapped
`Future` type implements `Assignable<<Async<Future> as BitXor<Rhs>>::Output>`,
which in turn requires the `Future::Output` type to implement
`BitXor<Rhs::Output>`.

```rust
use futures_executor::block_on;

let a = async { 38 };
let b = async { 12 };

let result = async {
  async_ops::assignable!(a);
  a ^= b;
  a.await
};

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>Div</b></summary>

`Async` implements `Div<Rhs> where Rhs: Future` when the wrapped
`Future::Output` type implements `Div<Rhs::Output>`. The resulting type of the
division is
`Async<impl Future<Output = <Future::Output as Div<Rhs::Output>>::Output>>`.

```rust
use futures_executor::block_on;

let a = async { 84 };
let b = async { 2 };

let result = async { (async_ops::on(a) / b).await };

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>DivAssign</b></summary>

`Async` implements `DivAssign<Rhs> where Rhs: Future` when the wrapped `Future`
type implements `Assignable<<Async<Future> as Div<Rhs>>::Output>`, which in turn
requires the `Future::Output` type to implement `Div<Rhs::Output>`.

```rust
use futures_executor::block_on;

let a = async { 84 };
let b = async { 2 };

let result = async {
  async_ops::assignable!(a);
  a /= b;
  a.await
};

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>Mul</b></summary>

`Async` implements `Mul<Rhs> where Rhs: Future` when the wrapped
`Future::Output` type implements `Mul<Rhs::Output>`. The resulting type of the
multiplication is
`Async<impl Future<Output = <Future::Output as Mul<Rhs::Output>>::Output>>`.

```rust
use futures_executor::block_on;

let a = async { 21 };
let b = async { 2 };

let result = async { (async_ops::on(a) * b).await };

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>MulAssign</b></summary>

`Async` implements `MulAssign<Rhs> where Rhs: Future` when the wrapped `Future`
type implements `Assignable<<Async<Future> as Mul<Rhs>>::Output>`, which in turn
requires the `Future::Output` type to implement `Mul<Rhs::Output>`.

```rust
use futures_executor::block_on;

let a = async { 21 };
let b = async { 2 };

let result = async {
  async_ops::assignable!(a);
  a *= b;
  a.await
};

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>Neg</b></summary>

`Async` implements `Neg` when the wrapped `Future::Output` type implements
`Neg`. The resulting type of the negation is
`Async<impl Future<Output = <Future::Output as Neg>::Output>>`.

```rust
use futures_executor::block_on;

let a = async { -42 };

let result = async { (-async_ops::on(a)).await };

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>Not</b></summary>

`Async` implements `Not` when the wrapped `Future::Output` type implements
`Not`. The resulting type of the logical negation is
`Async<impl Future<Output = <Future::Output as Not>::Output>>`.

```rust
use futures_executor::block_on;

let a = async { 213_u8 };

let result = async { (!async_ops::on(a)).await };

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>Rem</b></summary>

`Async` implements `Rem<Rhs> where Rhs: Future` when the wrapped
`Future::Output` type implements `Rem<Rhs::Output>`. The resulting type of the
reminder operation is
`Async<impl Future<Output = <Future::Output as Rem<Rhs::Output>>::Output>>`.

```rust
use futures_executor::block_on;

let a = async { 42 };
let b = async { 5 };

let result = async { (async_ops::on(a) % b).await };

assert_eq!(2, block_on(result));
```

</details>

<details>
<summary><b>RemAssign</b></summary>

`Async` implements `RemAssign<Rhs> where Rhs: Future` when the wrapped `Future`
type implements `Assignable<<Async<Future> as Rem<Rhs>>::Output>`, which in turn
requires the `Future::Output` type to implement `Rem<Rhs::Output>`.

```rust
use futures_executor::block_on;

let a = async { 42 };
let b = async { 5 };

let result = async {
  async_ops::assignable!(a);
  a %= b;
  a.await
};

assert_eq!(2, block_on(result));
```

</details>

<details>
<summary><b>Shl</b></summary>

`Async` implements `Shl<Rhs> where Rhs: Future` when the wrapped
`Future::Output` type implements `Shl<Rhs::Output>`. The resulting type of the
left shift is
`Async<impl Future<Output = <Future::Output as Shl<Rhs::Output>>::Output>>`.

```rust
use futures_executor::block_on;

let a = async { 21 };
let b = async { 1 };

let result = async { (async_ops::on(a) << b).await };

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>ShlAssign</b></summary>

`Async` implements `ShlAssign<Rhs> where Rhs: Future` when the wrapped `Future`
type implements `Assignable<<Async<Future> as Shl<Rhs>>::Output>`, which in turn
requires the `Future::Output` type to implement `Shl<Rhs::Output>`.

```rust
use futures_executor::block_on;

let a = async { 21 };
let b = async { 1 };

let result = async {
  async_ops::assignable!(a);
  a <<= b;
  a.await
};

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>Shr</b></summary>

`Async` implements `Shr<Rhs> where Rhs: Future` when the wrapped
`Future::Output` type implements `Shr<Rhs::Output>`. The resulting type of the
right shift is
`Async<impl Future<Output = <Future::Output as Shr<Rhs::Output>>::Output>>`.

```rust
use futures_executor::block_on;

let a = async { 168 };
let b = async { 2 };

let result = async { (async_ops::on(a) >> b).await };

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>ShrAssign</b></summary>

`Async` implements `ShrAssign<Rhs> where Rhs: Future` when the wrapped `Future`
type implements `Assignable<<Async<Future> as Shr<Rhs>>::Output>`, which in turn
requires the `Future::Output` type to implement `Shr<Rhs::Output>`.

```rust
use futures_executor::block_on;

let a = async { 168 };
let b = async { 2 };

let result = async {
  async_ops::assignable!(a);
  a >>= b;
  a.await
};

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>Sub</b></summary>

`Async` implements `Sub<Rhs> where Rhs: Future` when the wrapped
`Future::Output` type implements `Sub<Rhs::Output>`. The resulting type of the
subtraction is
`Async<impl Future<Output = <Future::Output as Sub<Rhs::Output>>::Output>>`.

```rust
use futures_executor::block_on;

let a = async { 44 };
let b = async { 2 };

let result = async { (async_ops::on(a) - b).await };

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>SubAssign</b></summary>

`Async` implements `SubAssign<Rhs> where Rhs: Future` when the wrapped `Future`
type implements `Assignable<<Async<Future> as Sub<Rhs>>::Output>`, which in turn
requires the `Future::Output` type to implement `Sub<Rhs::Output>`.

```rust
use futures_executor::block_on;

let a = async { 44 };
let b = async { 2 };

let result = async {
  async_ops::assignable!(a);
  a -= b;
  a.await
};

assert_eq!(42, block_on(result));
```

</details>

## License

Licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE)
or <http://www.apache.org/licenses/LICENSE-2.0>)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or
<http://opensource.org/licenses/MIT>)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the
[Apache License Version 2.0](LICENSE-APACHE), shall be dual licensed as above,
without any additional terms or conditions.
