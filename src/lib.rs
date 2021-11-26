// Copyright 2021 Sanjin Sehic
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![warn(missing_docs)]

//! `std:ops` traits for `Future`
//!
//! This crate provides a way to use
//! [some `std::ops` traits](#supported-stdops-traits) with [futures](Future).
//! To be able to use a [`std::ops`] trait with a `Future`, first you need to
//! wrap the `Future` with [`Async`] using [`async_ops::on`](crate::on). Then,
//! as long the `Future::Output` type implements a supported `std::ops` trait,
//! then the same `std::ops` trait will be implemented by the `Async` instance.
//!
//! Another option is to wrap a `Future` with `Async` using
//! [`async_ops::assignable`](crate::assignable) to enable usage of the `Assign`
//! variants of `std::ops` traits on the `Future`.
//!
//! # Example
//!
//! When writing `async` code it is common to do operations that are supported
//! through `std::ops`. For example, adding to numbers might look like this:
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! // Immediately returning a number is done for simplicity and production code
//! // wouldn't just immediately return a value.
//! let a = async { 40 };
//! let b = async { 2 };
//!
//! let result = async { a.await + b.await };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! Actually, the above code is not optimally implemented because `a` and `b`
//! are `await`-ed sequentially, instead of concurrently. The appropriate
//! solution is to use `join!` to be able to concurrently `await` both values
//! like this:
//!
//! ```rust
//! # use futures::executor::block_on;
//! # let a = async { 40 };
//! # let b = async { 2 };
//!
//! use futures::join;
//!
//! let result = async {
//!   let (a, b) = join!(a, b);
//!   a + b
//! };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! Or, just use [`async_ops::on`](crate::on) to do the same thing like the
//! above example in one line:
//!
//! ```rust
//! # use futures::executor::block_on;
//! # let a = async { 40 };
//! # let b = async { 2 };
//!
//! let result = async { (async_ops::on(a) + b).await };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! Note that the `async_ops::on` example will also concurrently `await` both
//! values.
//!
//! # Supported `std::ops` traits
//!
//! ## Add
//!
//! `Async` implements `Add<Rhs> where Rhs: Future` when the wrapped
//! `Future::Output` type implements `Add<Rhs::Output>`. The resulting type of
//! the addition is
//! `Async<impl Future<Output = <Future::Output as Add<Rhs::Output>>::Output>>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 40 };
//! let b = async { 2 };
//!
//! let result = async { (async_ops::on(a) + b).await };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## AddAssign
//!
//! `Async` implements `AddAssign<Rhs> where Rhs: Future` when the wrapped
//! `Future` type implements `Assignable<<Async<Future> as Add<Rhs>>::Output>`,
//! which in turn requires the `Future::Output` type to implement
//! `Add<Rhs::Output>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 40 };
//! let b = async { 2 };
//!
//! let result = async {
//!   let mut a = async_ops::assignable(a);
//!   a += b;
//!   a.await
//! };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## BitAnd
//!
//! `Async` implements `BitAnd<Rhs> where Rhs: Future` when the wrapped
//! `Future::Output` type implements `BitAnd<Rhs::Output>`. The resulting type
//! of the bitwise and is
//! `Async<impl Future<Output = <Future::Output as BitAnd<Rhs::Output>>::Output>>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 110 };
//! let b = async { 59 };
//!
//! let result = async { (async_ops::on(a) & b).await };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## BitAndAssign
//!
//! `Async` implements `BitAndAssign<Rhs> where Rhs: Future` when the wrapped
//! `Future` type implements
//! `Assignable<<Async<Future> as BitAnd<Rhs>>::Output>`, which in turn requires
//! the `Future::Output` type to implement `BitAnd<Rhs::Output>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 110 };
//! let b = async { 59 };
//!
//! let result = async {
//!   let mut a = async_ops::assignable(a);
//!   a &= b;
//!   a.await
//! };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## BitOr
//!
//! `Async` implements `BitOr<Rhs> where Rhs: Future` when the wrapped
//! `Future::Output` type implements `BitOr<Rhs::Output>`. The resulting type of
//! the bitwise or is
//! `Async<impl Future<Output = <Future::Output as BitOr<Rhs::Output>>::Output>>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 40 };
//! let b = async { 10 };
//!
//! let result = async { (async_ops::on(a) | b).await };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## BitOrAssign
//!
//! `Async` implements `BitOrAssign<Rhs> where Rhs: Future` when the wrapped
//! `Future` type implements
//! `Assignable<<Async<Future> as BitOr<Rhs>>::Output>`, which in turn requires
//! the `Future::Output` type to implement `BitOr<Rhs::Output>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 40 };
//! let b = async { 10 };
//!
//! let result = async {
//!   let mut a = async_ops::assignable(a);
//!   a |= b;
//!   a.await
//! };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## BitXor
//!
//! `Async` implements `BitXor<Rhs> where Rhs: Future` when the wrapped
//! `Future::Output` type implements `BitXor<Rhs::Output>`. The resulting type
//! of the bitwise xor is
//! `Async<impl Future<Output = <Future::Output as BitXor<Rhs::Output>>::Output>>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 38 };
//! let b = async { 12 };
//!
//! let result = async { (async_ops::on(a) ^ b).await };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## BitXorAssign
//!
//! `Async` implements `BitXorAssign<Rhs> where Rhs: Future` when the wrapped
//! `Future` type implements
//! `Assignable<<Async<Future> as BitXor<Rhs>>::Output>`, which in turn requires
//! the `Future::Output` type to implement `BitXor<Rhs::Output>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 38 };
//! let b = async { 12 };
//!
//! let result = async {
//!   let mut a = async_ops::assignable(a);
//!   a ^= b;
//!   a.await
//! };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## Div
//!
//! `Async` implements `Div<Rhs> where Rhs: Future` when the wrapped
//! `Future::Output` type implements `Div<Rhs::Output>`. The resulting type of
//! the division is
//! `Async<impl Future<Output = <Future::Output as Div<Rhs::Output>>::Output>>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 84 };
//! let b = async { 2 };
//!
//! let result = async { (async_ops::on(a) / b).await };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## DivAssign
//!
//! `Async` implements `DivAssign<Rhs> where Rhs: Future` when the wrapped
//! `Future` type implements `Assignable<<Async<Future> as Div<Rhs>>::Output>`,
//! which in turn requires the `Future::Output` type to implement
//! `Div<Rhs::Output>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 84 };
//! let b = async { 2 };
//!
//! let result = async {
//!   let mut a = async_ops::assignable(a);
//!   a /= b;
//!   a.await
//! };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## Mul
//!
//! `Async` implements `Mul<Rhs> where Rhs: Future` when the wrapped
//! `Future::Output` type implements `Mul<Rhs::Output>`. The resulting type of
//! the multiplication is
//! `Async<impl Future<Output = <Future::Output as Mul<Rhs::Output>>::Output>>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 21 };
//! let b = async { 2 };
//!
//! let result = async { (async_ops::on(a) * b).await };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## MulAssign
//!
//! `Async` implements `MulAssign<Rhs> where Rhs: Future` when the wrapped
//! `Future` type implements `Assignable<<Async<Future> as Mul<Rhs>>::Output>`,
//! which in turn requires the `Future::Output` type to implement
//! `Mul<Rhs::Output>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 21 };
//! let b = async { 2 };
//!
//! let result = async {
//!   let mut a = async_ops::assignable(a);
//!   a *= b;
//!   a.await
//! };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## Neg
//!
//! `Async` implements `Neg` when the wrapped `Future::Output` type implements
//! `Neg`. The resulting type of the negation is
//! `Async<impl Future<Output = <Future::Output as Neg>::Output>>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { -42 };
//!
//! let result = async { (-async_ops::on(a)).await };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## Not
//!
//! `Async` implements `Not` when the wrapped `Future::Output` type implements
//! `Not`. The resulting type of the logical negation is
//! `Async<impl Future<Output = <Future::Output as Not>::Output>>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 213_u8 };
//!
//! let result = async { (!async_ops::on(a)).await };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## Rem
//!
//! `Async` implements `Rem<Rhs> where Rhs: Future` when the wrapped
//! `Future::Output` type implements `Rem<Rhs::Output>`. The resulting type of
//! the reminder operation is
//! `Async<impl Future<Output = <Future::Output as Rem<Rhs::Output>>::Output>>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 42 };
//! let b = async { 5 };
//!
//! let result = async { (async_ops::on(a) % b).await };
//!
//! assert_eq!(2, block_on(result));
//! ```
//!
//! ## RemAssign
//!
//! `Async` implements `RemAssign<Rhs> where Rhs: Future` when the wrapped
//! `Future` type implements `Assignable<<Async<Future> as Rem<Rhs>>::Output>`,
//! which in turn requires the `Future::Output` type to implement
//! `Rem<Rhs::Output>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 42 };
//! let b = async { 5 };
//!
//! let result = async {
//!   let mut a = async_ops::assignable(a);
//!   a %= b;
//!   a.await
//! };
//!
//! assert_eq!(2, block_on(result));
//! ```
//!
//! ## Shl
//!
//! `Async` implements `Shl<Rhs> where Rhs: Future` when the wrapped
//! `Future::Output` type implements `Shl<Rhs::Output>`. The resulting type of
//! the left shift is
//! `Async<impl Future<Output = <Future::Output as Shl<Rhs::Output>>::Output>>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 21 };
//! let b = async { 1 };
//!
//! let result = async { (async_ops::on(a) << b).await };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## ShlAssign
//!
//! `Async` implements `ShlAssign<Rhs> where Rhs: Future` when the wrapped
//! `Future` type implements `Assignable<<Async<Future> as Shl<Rhs>>::Output>`,
//! which in turn requires the `Future::Output` type to implement
//! `Shl<Rhs::Output>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 21 };
//! let b = async { 1 };
//!
//! let result = async {
//!   let mut a = async_ops::assignable(a);
//!   a <<= b;
//!   a.await
//! };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## Shr
//!
//! `Async` implements `Shr<Rhs> where Rhs: Future` when the wrapped
//! `Future::Output` type implements `Shr<Rhs::Output>`. The resulting type of
//! the right shift is
//! `Async<impl Future<Output = <Future::Output as Shr<Rhs::Output>>::Output>>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 168 };
//! let b = async { 2 };
//!
//! let result = async { (async_ops::on(a) >> b).await };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## ShrAssign
//!
//! `Async` implements `ShrAssign<Rhs> where Rhs: Future` when the wrapped
//! `Future` type implements `Assignable<<Async<Future> as Shr<Rhs>>::Output>`,
//! which in turn requires the `Future::Output` type to implement
//! `Shr<Rhs::Output>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 168 };
//! let b = async { 2 };
//!
//! let result = async {
//!   let mut a = async_ops::assignable(a);
//!   a >>= b;
//!   a.await
//! };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## Sub
//!
//! `Async` implements `Sub<Rhs> where Rhs: Future` when the wrapped
//! `Future::Output` type implements `Sub<Rhs::Output>`. The resulting type of
//! the subtraction is
//! `Async<impl Future<Output = <Future::Output as Sub<Rhs::Output>>::Output>>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 44 };
//! let b = async { 2 };
//!
//! let result = async { (async_ops::on(a) - b).await };
//!
//! assert_eq!(42, block_on(result));
//! ```
//!
//! ## SubAssign
//!
//! `Async` implements `SubAssign<Rhs> where Rhs: Future` when the wrapped
//! `Future` type implements `Assignable<<Async<Future> as Sub<Rhs>>::Output>`,
//! which in turn requires the `Future::Output` type to implement
//! `Sub<Rhs::Output>`.
//!
//! ```rust
//! use futures::executor::block_on;
//!
//! let a = async { 44 };
//! let b = async { 2 };
//!
//! let result = async {
//!   let mut a = async_ops::assignable(a);
//!   a -= b;
//!   a.await
//! };
//!
//! assert_eq!(42, block_on(result));
//! ```

mod ops;

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

use futures::future::BoxFuture;
use pin_project_lite::pin_project;

pub use ops::{
  add, bitand, bitor, bitxor, div, mul, neg, not, rem, shl, shr, sub, Add, Assignable, Binary,
  BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub, Unary,
};

/// Wraps the given [`Future`] with [`Async`].
///
/// # Example
///
/// ```rust
/// use futures::executor::block_on;
///
/// let a = async { 40 };
/// let b = async { 2 };
///
/// let result = async { (async_ops::on(a) + b).await };
///
/// assert_eq!(42, block_on(result));
/// ```
pub fn on<Fut: Future>(future: Fut) -> Async<Fut> {
  Async { future }
}

/// Wraps the given [`Future`] with [`Async`] that can be used with the `Assign`
/// variants of [`std::ops`] traits.
///
/// See also [`Async::assignable`].
///
/// # Example
///
/// ```rust
/// use futures::executor::block_on;
///
/// let a = async { 40 };
/// let b = async { 2 };
///
/// let result = async {
///   let mut a = async_ops::assignable(a);
///   a += b;
///   a.await
/// };
///
/// assert_eq!(42, block_on(result));
/// ```
pub fn assignable<'a, Fut: Future + Send + 'a>(future: Fut) -> Async<BoxFuture<'a, Fut::Output>> {
  let future: BoxFuture<Fut::Output> = Assignable::from(future);
  Async { future }
}

pin_project! {
  /// A wrapper class for a [`Future`] that enables usage of some [`std::ops`]
  /// traits.
  ///
  /// This struct will implement a supported `std::ops` trait when
  /// `<Fut as Future>::Output` type implements the same `std::ops` trait.
  #[must_use = "futures do nothing unless you `.await` or poll them"]
  pub struct Async<Fut: Future> {
    #[pin]
    future: Fut
  }
}

impl<Fut: Future> Async<Fut> {
  /// Wraps the inner [`Future`] in [`Async`] with the given `Assignable` type
  /// so that it can be used with `Assign` variants of [`std::ops`] traits.
  ///
  /// See also [`async_ops::assignable`](crate::assignable).
  ///
  /// # Example
  ///
  /// ```rust
  /// use futures::executor::block_on;
  /// use futures::future::LocalBoxFuture;
  ///
  /// let a = async { 40 };
  /// let b = async { 2 };
  ///
  /// let result = async {
  ///   let mut a = async_ops::on(a).assignable::<LocalBoxFuture<usize>>();
  ///   a += b;
  ///   a.await
  /// };
  ///
  /// assert_eq!(42, block_on(result));
  /// ```
  pub fn assignable<T: Assignable<Fut> + Future>(self) -> Async<T> {
    Async {
      future: T::from(self.future),
    }
  }

  /// Does the given [`Unary`] operation `Op` on the wrapped [`Future`] in
  /// [`Async`] and returns the result in a new [`Async`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use std::future::{ready, Ready};
  /// use futures::executor::block_on;
  /// use async_ops::Unary;
  ///
  /// struct Return42;
  ///
  /// impl<Operand> Unary<Operand> for Return42 {
  ///   type Output = Ready<usize>;
  ///   fn op(_: Operand) -> Self::Output {
  ///     ready(42)
  ///   }
  /// }
  ///
  /// let a = async { 2 };
  ///
  /// let result = async {
  ///   async_ops::on(a).unary_op(Return42).await
  /// };
  ///
  /// assert_eq!(42, block_on(result));
  /// ```
  pub fn unary_op<Op: Unary<Fut>>(self, _: Op) -> Async<Op::Output>
  where
    Op::Output: Future,
  {
    crate::on(Op::op(self.future))
  }

  /// Does the given [`Binary`] operation `Op` on the wrapped [`Future`] in
  /// [`Async`] and the given right-hand operand and returns the result in a new
  /// [`Async`].
  ///
  /// See also [`Async::op_assign`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use futures::executor::block_on;
  /// use async_ops::Binary;
  ///
  /// struct ReturnRhs;
  ///
  /// impl<Lhs, Rhs> Binary<Lhs, Rhs> for ReturnRhs {
  ///   type Output = Rhs;
  ///   fn op(_: Lhs, rhs: Rhs) -> Self::Output {
  ///     rhs
  ///   }
  /// }
  ///
  /// let a = async { 2 };
  /// let b = async { 42 };
  ///
  /// let result = async {
  ///   async_ops::on(a).op(ReturnRhs, b).await
  /// };
  ///
  /// assert_eq!(42, block_on(result));
  /// ```
  pub fn op<Rhs, Op: Binary<Fut, Rhs>>(self, _: Op, rhs: Rhs) -> Async<Op::Output>
  where
    Op::Output: Future,
  {
    crate::on(Op::op(self.future, rhs))
  }

  /// Does the given [`Binary`] operation `Op` on the wrapped [`Future`] in
  /// [`Async`] and the given right-hand operand and assigns it to `self`.
  ///
  /// See also [`Async::op`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use futures::executor::block_on;
  /// use async_ops::Binary;
  ///
  /// struct ReturnRhs;
  ///
  /// impl<Lhs, Rhs> Binary<Lhs, Rhs> for ReturnRhs {
  ///   type Output = Rhs;
  ///   fn op(_: Lhs, rhs: Rhs) -> Self::Output {
  ///     rhs
  ///   }
  /// }
  ///
  /// let a = async { 2 };
  /// let b = async { 42 };
  ///
  /// let result = async {
  ///   let mut a = async_ops::assignable(a);
  ///   a.op_assign(ReturnRhs, b);
  ///   a.await
  /// };
  ///
  /// assert_eq!(42, block_on(result));
  /// ```
  pub fn op_assign<Rhs, Op: Binary<Fut, Rhs>>(&mut self, _: Op, rhs: Rhs)
  where
    Fut: Assignable<Op::Output>,
    Op::Output: Future,
  {
    Op::op_assign(&mut self.future, rhs);
  }
}

impl<Fut: Future> Future for Async<Fut> {
  type Output = Fut::Output;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    self.project().future.poll(cx)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  use std::cell::RefCell;
  use std::rc::Rc;

  use futures::future::FutureExt;

  pin_project! {
    #[derive(Default)]
    struct FakeFuture<T> {
      value: Option<T>,
      // This is of course not safe in the multi-threaded world and normally
      // Arc and future-safe Mutex should be used. However, because we are only
      // using now_or_never() to immediately poll the future on the same thread,
      // it is safe to use Rc and RefCell here.
      polled_times: Rc<RefCell<usize>>,
    }
  }

  impl<T> Future for FakeFuture<T> {
    type Output = T;

    fn poll(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Self::Output> {
      let this = self.project();
      *this.polled_times.borrow_mut() += 1;
      match this.value.take() {
        Some(value) => Poll::Ready(value),
        None => Poll::Pending,
      }
    }
  }

  #[test]
  fn ready_when_the_wrapped_future_is_ready() {
    let mut future = FakeFuture::default();
    let polled_times = future.polled_times.clone();

    assert_eq!(0, *polled_times.borrow());

    future.value = Some(42);
    assert_eq!(Some(42), on(future).now_or_never());

    assert_eq!(1, *polled_times.borrow());
  }

  #[test]
  fn pending_when_the_wrapped_future_is_pending() {
    let future = FakeFuture::<usize>::default();
    let polled_times = future.polled_times.clone();

    assert_eq!(0, *polled_times.borrow());

    assert_eq!(None, on(future).now_or_never());

    assert_eq!(1, *polled_times.borrow());
  }
}

#[cfg(doctest)]
mod readme {
  use doc_comment::doctest;

  doctest!("../README.md");
}
