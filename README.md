# async-ops

[![CI](https://github.com/saserr/async-ops/actions/workflows/CI.yml/badge.svg)](https://github.com/saserr/async-ops/actions/workflows/CI.yml)
[![codecov](https://codecov.io/gh/saserr/async-ops/branch/main/graph/badge.svg?token=2K2DABXJMS)](https://codecov.io/gh/saserr/async-ops)

This crate provides a way to use
[some `std::ops` traits](#supported-stdops-traits) with `Futures`. To be able to
use a `std::ops` traits with a `Future`, first you need to wrap the `Future`
with `Async` using `async_ops::on`. Then, as long the `Future::Output` type
implements a supported `std::ops` trait, then the same `std::ops` trait will be
implemented by the `Async` instance.

Another option is to wrap a `Future` with `Async` using `async_ops::assignable`
to enable usage of the `Assign` variants of `std::ops` traits on the `Future`.

## Example

When writing `async` code it is common to do operations that are supported
through `std::ops`. For example, adding to numbers might look like this:

```rust
use futures::executor::block_on;

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
use futures::executor::block_on;
use futures::join;

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
use futures::executor::block_on;

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
`Future::Output` type implements `Add<Rhs::Output>`. The result of the
addition is
`Async<impl Future<Output = <Future::Output as Add<Rhs::Output>>::Output>>`.

```rust
use futures::executor::block_on;

let a = async { 40 };
let b = async { 2 };

let result = async { (async_ops::on(a) + b).await };

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>AddAssign</b></summary>

`Async` implements `AddAssign<Rhs> where Rhs: Future` when the wrapped
`Future` type implements `Assignable<<Async<Future> as Add<Rhs>>::Output>`,
which in turn requires the `Future::Output` type to implement
`Add<Rhs::Output>`.

```rust
use futures::executor::block_on;

let a = async { 40 };
let b = async { 2 };

let result = async {
  let mut a = async_ops::assignable(a);
  a += b;
  a.await
};

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>Div</b></summary>

`Async` implements `Div<Rhs> where Rhs: Future` when the wrapped
`Future::Output` type implements `Div<Rhs::Output>`. The result of the
division is
`Async<impl Future<Output = <Future::Output as Div<Rhs::Output>>::Output>>`.

```rust
use futures::executor::block_on;

let a = async { 84 };
let b = async { 2 };

let result = async { (async_ops::on(a) / b).await };

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>DivAssign</b></summary>

`Async` implements `DivAssign<Rhs> where Rhs: Future` when the wrapped
`Future` type implements `Assignable<<Async<Future> as Div<Rhs>>::Output>`,
which in turn requires the `Future::Output` type to implement
`Div<Rhs::Output>`.

```rust
use futures::executor::block_on;

let a = async { 84 };
let b = async { 2 };

let result = async {
  let mut a = async_ops::assignable(a);
  a /= b;
  a.await
};

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>Mul</b></summary>

`Async` implements `Mul<Rhs> where Rhs: Future` when the wrapped
`Future::Output` type implements `Mul<Rhs::Output>`. The result of the
multiplication is
`Async<impl Future<Output = <Future::Output as Mul<Rhs::Output>>::Output>>`.

```rust
use futures::executor::block_on;

let a = async { 21 };
let b = async { 2 };

let result = async { (async_ops::on(a) * b).await };

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>MulAssign</b></summary>

`Async` implements `MulAssign<Rhs> where Rhs: Future` when the wrapped
`Future` type implements `Assignable<<Async<Future> as Mul<Rhs>>::Output>`,
which in turn requires the `Future::Output` type to implement
`Mul<Rhs::Output>`.

```rust
use futures::executor::block_on;

let a = async { 21 };
let b = async { 2 };

let result = async {
  let mut a = async_ops::assignable(a);
  a *= b;
  a.await
};

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>Sub</b></summary>

`Async` implements `Sub<Rhs> where Rhs: Future` when the wrapped
`Future::Output` type implements `Sub<Rhs::Output>`. The result of the
subtraction is
`Async<impl Future<Output = <Future::Output as Sub<Rhs::Output>>::Output>>`.

```rust
use futures::executor::block_on;

let a = async { 44 };
let b = async { 2 };

let result = async { (async_ops::on(a) - b).await };

assert_eq!(42, block_on(result));
```

</details>

<details>
<summary><b>SubAssign</b></summary>

`Async` implements `SubAssign<Rhs> where Rhs: Future` when the wrapped
`Future` type implements `Assignable<<Async<Future> as Sub<Rhs>>::Output>`,
which in turn requires the `Future::Output` type to implement
`Sub<Rhs::Output>`.

```rust
use futures::executor::block_on;

let a = async { 44 };
let b = async { 2 };

let result = async {
  let mut a = async_ops::assignable(a);
  a -= b;
  a.await
};

assert_eq!(42, block_on(result));
```

</details>
