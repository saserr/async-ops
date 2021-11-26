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

use std::future::Future;
use std::pin::Pin;
use std::ptr;
use std::task::{Context, Poll};

use futures::future::{join, BoxFuture, FutureExt, Join, LocalBoxFuture};
use futures::ready;
use paste::paste;
use pin_project_lite::pin_project;

use crate::Async;

/// Trait for types that can be used with the [`Binary::op_assign`] to assign
/// the result of the [`Binary`] operation to the left-hand operand.
///
/// See [`Async::assignable`](crate::Async::assignable).
pub trait Assignable<T> {
  /// Wrap the given value with `Self`.
  fn from(value: T) -> Self;
}

impl<'a, T, Fut: Future<Output = T> + Send + 'a> Assignable<Fut> for BoxFuture<'a, T> {
  /// Wrap the given [`Future`] with [`BoxFuture`].
  fn from(future: Fut) -> Self {
    future.boxed()
  }
}

impl<'a, T, Fut: Future<Output = T> + 'a> Assignable<Fut> for LocalBoxFuture<'a, T> {
  /// Wrap the given [`Future`] with [`LocalBoxFuture`].
  fn from(future: Fut) -> Self {
    future.boxed_local()
  }
}

/// Trait that represents an unary operation on the operand of type `Operand`
/// that returns the result of type `Output`.
///
/// See [`Async::unary_op`](crate::Async::unary_op).
pub trait Unary<Operand> {
  /// The resulting type after applying the unary operation.
  type Output;

  /// Do the unary operation on the given operand.
  fn op(operand: Operand) -> Self::Output;
}

/// Trait that represents a binary operation on the left-hand operand of type
/// `Lhs` and the right-hand operand of type `Rhs` that returns the result of
/// type `Output`.
///
/// See [`Async::op`](crate::Async::op) and
/// [`Async::op_assign`](crate::Async::op_assign).
pub trait Binary<Lhs, Rhs> {
  /// The resulting type after applying the binary operation.
  type Output;

  /// Do the binary operation on given operands.
  fn op(lhs: Lhs, rhs: Rhs) -> Self::Output;

  /// Do the binary operation on given operands and assign the result to the
  /// `lhs` operand.
  fn op_assign(lhs: &mut Lhs, rhs: Rhs)
  where
    Lhs: Assignable<Self::Output>,
  {
    unsafe {
      let this = ptr::read(lhs);
      ptr::write(lhs, Lhs::from(Self::op(this, rhs)))
    }
  }
}

macro_rules! from_std_unary_ops {
  ($($Op:ident),*) => {$(
    paste! {
      #[doc = concat!(
        "Returns a [`Future`] that will resolve the given `Future` ",
        "and [`", stringify!([<$Op:lower>]), "`]",
        "(std::ops::", stringify!($Op), "::", stringify!([<$Op:lower>]), ") ",
        "its result.\n\n# Example\n\n",
        "```rust\n",
        "use futures::executor::block_on;\n",
        "use async_ops::", stringify!([<$Op:lower>]), ";\n\n",
        "let a = async { 42 };\n\n",
        "let result = async {\n",
        "  ", stringify!([<$Op:lower>]),"(a).await\n",
        "};\n\n",
        "assert_eq!(std::ops::", stringify!($Op), "::",
        stringify!([<$Op:lower>]), "(42), block_on(result));")]
      pub fn [<$Op:lower>]<Operand: std::ops::$Op>(
        operand: impl Future<Output = Operand>,
      ) -> impl Future<Output = Operand::Output> {
        $Op::op(operand)
      }

      pin_project! {
        #[doc = concat!(
          "A [`Future`] that will resolve a `Future` and ",
          "[`", stringify!([<$Op:lower>]), "`]",
          "(std::ops::", stringify!($Op), "::", stringify!([<$Op:lower>]), ") ",
          "its result.")]
        #[must_use = "futures do nothing unless you `.await` or poll them"]
        pub struct [<Async $Op>]<Operand: Future> {
          #[pin]
          operand: Operand
        }
      }

      impl<Operand: Future> Future for [<Async $Op>]<Operand>
      where
        Operand::Output: std::ops::$Op,
      {
        type Output = <Operand::Output as std::ops::$Op>::Output;

        fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
          let operand = ready!(self.project().operand.poll(cx));
          Poll::Ready(std::ops::$Op::[<$Op:lower>](operand))
        }
      }

      #[doc = concat!(
        "A [`Unary`] operation that will concurrently resolve a [`Future`] ",
        "and [`", stringify!([<$Op:lower>]), "`]",
        "(std::ops::", stringify!($Op), "::", stringify!([<$Op:lower>]), ") ",
        "its result.\n\n# Example\n\n",
        "```rust\n",
        "use futures::executor::block_on;\n",
        "use async_ops::", stringify!($Op), ";\n\n",
        "let a = async { 42 };\n\n",
        "let result = async {\n",
        "  async_ops::on(a).unary_op(", stringify!($Op),").await\n",
        "};\n\n",
        "assert_eq!(std::ops::", stringify!($Op), "::",
        stringify!([<$Op:lower>]), "(42), block_on(result));")]
      pub struct $Op;

      impl<Operand: Future> Unary<Operand> for $Op
      where
        Operand::Output: std::ops::$Op,
      {
        type Output = [<Async $Op>]<Operand>;

        fn op(operand: Operand) -> Self::Output {
          [<Async $Op>] { operand }
        }
      }

      impl<Operand: Future> std::ops::$Op for Async<Operand>
      where
        Operand::Output: std::ops::$Op,
      {
        type Output = Async<[<Async $Op>]<Operand>>;

        fn [<$Op:lower>](self) -> Self::Output {
          crate::on($Op::op(self.future))
        }
      }
    }
  )*};
}

macro_rules! from_std_binary_ops {
  ($($Op:ident),*) => {$(
    paste! {
      #[doc = concat!(
        "Returns a [`Future`] that will concurrently resolve given `Futures` ",
        "and [`", stringify!([<$Op:lower>]), "`]",
        "(std::ops::", stringify!($Op), "::", stringify!([<$Op:lower>]), ") ",
        "their results.\n\n# Example\n\n",
        "```rust\n",
        "use futures::executor::block_on;\n",
        "use async_ops::", stringify!([<$Op:lower>]), ";\n\n",
        "let a = async { 42 };\n",
        "let b = async { 2 };\n\n",
        "let result = async {\n",
        "  ", stringify!([<$Op:lower>]),"(a, b).await\n",
        "};\n\n",
        "assert_eq!(std::ops::", stringify!($Op), "::",
        stringify!([<$Op:lower>]), "(42, 2), block_on(result));")]
      pub fn [<$Op:lower>]<Lhs: std::ops::$Op<Rhs>, Rhs>(
        lhs: impl Future<Output = Lhs>,
        rhs: impl Future<Output = Rhs>,
      ) -> impl Future<Output = Lhs::Output> {
        $Op::op(lhs, rhs)
      }

      pin_project! {
        #[doc = concat!(
          "A [`Future`] that will concurrently resolve two `Futures` and ",
          "[`", stringify!([<$Op:lower>]), "`]",
          "(std::ops::", stringify!($Op), "::", stringify!([<$Op:lower>]), ") ",
          "their results.")]
        #[must_use = "futures do nothing unless you `.await` or poll them"]
        pub struct [<Async $Op>]<Lhs: Future, Rhs: Future> {
          #[pin]
          future: Join<Lhs, Rhs>
        }
      }

      impl<Lhs: Future, Rhs: Future> Future for [<Async $Op>]<Lhs, Rhs>
      where
        Lhs::Output: std::ops::$Op<Rhs::Output>,
      {
        type Output = <Lhs::Output as std::ops::$Op<Rhs::Output>>::Output;

        fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
          let (lhs, rhs) = ready!(self.project().future.poll(cx));
          Poll::Ready(std::ops::$Op::[<$Op:lower>](lhs, rhs))
        }
      }

      #[doc = concat!(
        "A [`Binary`] operation that will concurrently resolve two ",
        "[`Futures`](Future) and [`", stringify!([<$Op:lower>]), "`]",
        "(std::ops::", stringify!($Op), "::", stringify!([<$Op:lower>]), ") ",
        "their results.\n\n# Example\n\n",
        "```rust\n",
        "use futures::executor::block_on;\n",
        "use async_ops::", stringify!($Op), ";\n\n",
        "let a = async { 42 };\n",
        "let b = async { 2 };\n\n",
        "let result = async {\n",
        "  async_ops::on(a).op(", stringify!($Op),", b).await\n",
        "};\n\n",
        "assert_eq!(std::ops::", stringify!($Op), "::",
        stringify!([<$Op:lower>]), "(42, 2), block_on(result));")]
      pub struct $Op;

      impl<Lhs: Future, Rhs: Future> Binary<Lhs, Rhs> for $Op
      where
        Lhs::Output: std::ops::$Op<Rhs::Output>,
      {
        type Output = [<Async $Op>]<Lhs, Rhs>;

        fn op(lhs: Lhs, rhs: Rhs) -> Self::Output {
          [<Async $Op>] {
            future: join(lhs, rhs),
          }
        }
      }

      impl<Lhs: Future, Rhs: Future> std::ops::$Op<Rhs> for Async<Lhs>
      where
        Lhs::Output: std::ops::$Op<Rhs::Output>,
      {
        type Output = Async<[<Async $Op>]<Lhs, Rhs>>;

        fn [<$Op:lower>](self, rhs: Rhs) -> Self::Output {
          crate::on($Op::op(self.future, rhs))
        }
      }

      impl<Lhs, Rhs> std::ops::[<$Op Assign>]<Rhs> for Async<Lhs>
      where
        Lhs: Assignable<[<Async $Op>]<Lhs, Rhs>> + Future,
        Rhs: Future,
        <Lhs as Future>::Output: std::ops::$Op<Rhs::Output>,
      {
        fn [<$Op:lower _assign>](&mut self, rhs: Rhs) {
          $Op::op_assign(&mut self.future, rhs);
        }
      }
    }
  )*};
}

from_std_unary_ops!(Neg, Not);
from_std_binary_ops!(Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Shl, Shr, Sub);

#[cfg(test)]
mod tests {
  use super::*;

  use std::future::ready;

  use futures::executor::block_on;

  struct ReturnRhs;

  impl<Lhs, Rhs> Binary<Lhs, Rhs> for ReturnRhs {
    type Output = Rhs;

    fn op(_: Lhs, rhs: Rhs) -> Self::Output {
      rhs
    }
  }

  #[test]
  fn box_future_op_assign() {
    let mut future: BoxFuture<usize> = Assignable::from(ready(2));

    ReturnRhs::op_assign(&mut future, ready(42));

    assert_eq!(42, block_on(future));
  }

  #[test]
  fn local_box_future_op_assign() {
    let mut future: LocalBoxFuture<usize> = Assignable::from(ready(2));

    ReturnRhs::op_assign(&mut future, ready(42));

    assert_eq!(42, block_on(future));
  }
}
