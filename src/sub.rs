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
use std::ops::{Sub, SubAssign};
use std::pin::Pin;
use std::ptr;
use std::task::{Context, Poll};

use futures::future::{join, BoxFuture, Join};
use futures::ready;
use pin_project_lite::pin_project;

use crate::Async;

pin_project! {
  /// A [`Future`] that concurrently resolves two `Futures` and subtracts their
  /// results of using [`std::ops::Sub`].
  #[must_use = "futures do nothing unless you `.await` or poll them"]
  pub struct AsyncSub<Lhs: Future, Rhs: Future> {
    #[pin]
    future: Join<Lhs, Rhs>
  }
}

impl<Lhs: Future, Rhs: Future> AsyncSub<Lhs, Rhs> {
  pub fn new(lhs: Lhs, rhs: Rhs) -> Self {
    Self {
      future: join(lhs, rhs),
    }
  }
}

impl<Lhs: Future, Rhs: Future> Future for AsyncSub<Lhs, Rhs>
where
  Lhs::Output: Sub<Rhs::Output>,
{
  type Output = <Lhs::Output as Sub<Rhs::Output>>::Output;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let (a, b) = ready!(self.project().future.poll(cx));
    Poll::Ready(a - b)
  }
}

impl<Lhs: Future, Rhs: Future> Sub<Rhs> for Async<Lhs>
where
  Lhs::Output: Sub<Rhs::Output>,
{
  type Output = Async<AsyncSub<Lhs, Rhs>>;

  fn sub(self, rhs: Rhs) -> Self::Output {
    crate::on(AsyncSub::new(self.future, rhs))
  }
}

impl<'a, Lhs, Rhs> SubAssign<Rhs> for Async<BoxFuture<'a, Lhs>>
where
  Lhs: Sub<Rhs::Output, Output = Lhs> + Send + 'a,
  Rhs: Future + Send + 'a,
  Rhs::Output: Send,
{
  fn sub_assign(&mut self, rhs: Rhs) {
    unsafe {
      let future = ptr::read(&self.future);
      ptr::write(&mut self.future, Box::pin(AsyncSub::new(future, rhs)))
    };
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  use std::future::ready;

  use futures::executor::block_on;

  #[test]
  fn async_sub() {
    assert_eq!(42, block_on(AsyncSub::new(ready(44), ready(2))));
  }

  #[test]
  fn sub() {
    assert_eq!(
      42,
      block_on(async {
        let a = ready(44);
        let b = ready(2);
        (crate::on(a) - b).await
      })
    );
  }

  #[test]
  fn sub_assign() {
    assert_eq!(
      42,
      block_on(async {
        let mut result = crate::assignable(ready(44));
        result -= ready(2);
        result.await
      })
    );
  }
}
