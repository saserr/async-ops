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
//! This crate provides a way to use some [`std::ops`] traits with
//! [futures](Future). To be able to use a `std::ops` traits with a `Future`,
//! first you need to wrap the `Future` with [`Async`] using
//! [`async_ops::on`](crate::on). Then, as long the `Future::Output` type
//! implements a supported `std::ops` trait, then the same `std::ops` trait will
//! be implemented by the `Async` instance.

use std::future::Future;
use std::pin::Pin;

use std::task::{Context, Poll};

use pin_project_lite::pin_project;

/// Wraps the given [`Future`] with [`Async`].
pub fn on<Fut: Future>(future: Fut) -> Async<Fut> {
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

impl<Fut: Future> Future for Async<Fut> {
  type Output = Fut::Output;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    self.project().future.poll(cx)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  use std::sync::{Arc, Mutex};

  use futures::task::{waker, ArcWake};

  struct Waker;

  impl ArcWake for Waker {
    fn wake_by_ref(_: &Arc<Self>) {
      unimplemented!()
    }
  }

  pin_project! {
    #[derive(Default)]
    struct FakeFuture<T> {
      value: Option<T>,
      polled_times: Arc<Mutex<usize>>,
      was_ready: Arc<Mutex<bool>>,
    }
  }

  impl<T> Future for FakeFuture<T> {
    type Output = T;

    fn poll(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Self::Output> {
      let this = self.project();
      *this.polled_times.lock().unwrap() += 1;
      match this.value.take() {
        Some(value) => {
          *this.was_ready.lock().unwrap() = true;
          Poll::Ready(value)
        }
        None => {
          assert!(!*this.was_ready.lock().unwrap());
          Poll::Pending
        }
      }
    }
  }

  #[test]
  fn ready_when_the_wrapped_future_is_ready() {
    let mut future = FakeFuture::default();
    let polled_times = future.polled_times.clone();
    let was_ready = future.was_ready.clone();

    assert_eq!(0, *polled_times.lock().unwrap());
    assert!(!*was_ready.lock().unwrap());

    future.value = Some(42);
    let mut future = on(future);
    assert!(matches!(
      Pin::new(&mut future).poll(&mut Context::from_waker(&waker(Arc::new(Waker)))),
      Poll::Ready(42)
    ));

    assert_eq!(1, *polled_times.lock().unwrap());
    assert!(*was_ready.lock().unwrap());
  }

  #[test]
  fn pending_when_the_wrapped_future_is_pending() {
    let future = FakeFuture::<usize>::default();
    let polled_times = future.polled_times.clone();
    let was_ready = future.was_ready.clone();

    assert_eq!(0, *polled_times.lock().unwrap());
    assert!(!*was_ready.lock().unwrap());

    let mut future = on(future);
    assert!(matches!(
      Pin::new(&mut future).poll(&mut Context::from_waker(&waker(Arc::new(Waker)))),
      Poll::Pending
    ));

    assert_eq!(1, *polled_times.lock().unwrap());
    assert!(!*was_ready.lock().unwrap());
  }
}
