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
use std::ops::AddAssign;
use std::pin::Pin;
use std::task::{Context, Poll};

use futures::future::{join, Join};
use futures::ready;
use pin_project_lite::pin_project;

use crate::ops::{Assignable, Binary};
use crate::Async;

/// Returns a [`Future`] that will concurrently resolve given `Futures` and sum
/// their results using [`std::ops::Add`].
///
/// # Example
///
/// ```rust
/// use futures::executor::block_on;
/// use async_ops::add;
///
/// let a = async { 40 };
/// let b = async { 2 };
///
/// let result = async {
///   add(a, b).await
/// };
///
/// assert_eq!(42, block_on(result));
pub fn add<Lhs: std::ops::Add<Rhs>, Rhs>(
  lhs: impl Future<Output = Lhs>,
  rhs: impl Future<Output = Rhs>,
) -> impl Future<Output = Lhs::Output> {
  Add::op(lhs, rhs)
}

pin_project! {
  /// A [`Future`] that will concurrently resolve two `Futures` and sum their
  /// results using [`std::ops::Add`].
  #[must_use = "futures do nothing unless you `.await` or poll them"]
  pub struct AsyncAdd<Lhs: Future, Rhs: Future> {
    #[pin]
    future: Join<Lhs, Rhs>
  }
}

impl<Lhs: Future, Rhs: Future> Future for AsyncAdd<Lhs, Rhs>
where
  Lhs::Output: std::ops::Add<Rhs::Output>,
{
  type Output = <Lhs::Output as std::ops::Add<Rhs::Output>>::Output;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let (a, b) = ready!(self.project().future.poll(cx));
    Poll::Ready(a + b)
  }
}

/// A [`Binary`] operation that will concurrently resolve two `Futures` and sum
/// their results using [`std::ops::Add`].
///
/// # Example
///
/// ```rust
/// use futures::executor::block_on;
/// use async_ops::Add;
///
/// let a = async { 40 };
/// let b = async { 2 };
///
/// let result = async {
///   async_ops::on(a).op(Add, b).await
/// };
///
/// assert_eq!(42, block_on(result));
/// ```
pub struct Add;

impl<Lhs: Future, Rhs: Future> Binary<Lhs, Rhs> for Add
where
  Lhs::Output: std::ops::Add<Rhs::Output>,
{
  type Output = AsyncAdd<Lhs, Rhs>;

  fn op(lhs: Lhs, rhs: Rhs) -> Self::Output {
    AsyncAdd {
      future: join(lhs, rhs),
    }
  }
}

impl<Lhs: Future, Rhs: Future> std::ops::Add<Rhs> for Async<Lhs>
where
  Lhs::Output: std::ops::Add<Rhs::Output>,
{
  type Output = Async<AsyncAdd<Lhs, Rhs>>;

  fn add(self, rhs: Rhs) -> Self::Output {
    crate::on(Add::op(self.future, rhs))
  }
}

impl<Lhs, Rhs> AddAssign<Rhs> for Async<Lhs>
where
  Lhs: Assignable<AsyncAdd<Lhs, Rhs>> + Future,
  Rhs: Future,
  <Lhs as Future>::Output: std::ops::Add<Rhs::Output>,
{
  fn add_assign(&mut self, rhs: Rhs) {
    Add::op_assign(&mut self.future, rhs);
  }
}

#[cfg(test)]
mod tests {
  use std::future::ready;

  use futures::executor::block_on;

  #[test]
  fn add() {
    assert_eq!(
      42,
      block_on(async {
        let a = ready(40);
        let b = ready(2);
        (crate::on(a) + b).await
      })
    );
  }

  #[test]
  fn add_assign() {
    assert_eq!(
      42,
      block_on(async {
        let mut result = crate::assignable(ready(40));
        result += ready(2);
        result.await
      })
    );
  }
}
