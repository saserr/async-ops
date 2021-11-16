# async-ops

[![CI](https://github.com/saserr/async-ops/actions/workflows/CI.yml/badge.svg)](https://github.com/saserr/async-ops/actions/workflows/CI.yml)
[![codecov](https://codecov.io/gh/saserr/async-ops/branch/main/graph/badge.svg?token=2K2DABXJMS)](https://codecov.io/gh/saserr/async-ops)

This crate provides a way to use some `std::ops` traits with `Futures`. To be
able to use a `std::ops` traits with a `Future`, first you need to wrap the
`Future` with `Async` using `async_ops::on`. Then, as long the `Future::Output`
type implements a supported `std::ops` trait, then the same `std::ops` trait
will be implemented by the `Async` instance.
