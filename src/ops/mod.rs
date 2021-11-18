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

pub mod add;
pub mod sub;

use std::future::Future;
use std::ptr;

use futures::future::{BoxFuture, FutureExt, LocalBoxFuture};

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
