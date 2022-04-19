# Changelog

All notable changes to `async-ops` project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [1.0.0] - 2021-11-25

### Added

- New `Async` trait that enables usage of some `std::ops` traits with `Futures`.
- Implementation of `std::ops::Add` and `std::ops::AddAssign` traits for
`Async`.
- Implementation of `std::ops::Sub` and `std::ops::SubAssign` traits for
`Async`.
- Implementation of `std::ops::Mul` and `std::ops::MulAssign` traits for
`Async`.
- Implementation of `std::ops::Div` and `std::ops::DivAssign` traits for
`Async`.
- Implementation of `std::ops::Rem` and `std::ops::RemAssign` traits for
`Async`.
- Implementation of `std::ops::Neg` trait for `Async`.
- Implementation of `std::ops::Not` trait for `Async`.
- Implementation of `std::ops::BitAnd` and `std::ops::BitAndAssign` traits for
`Async`.
- Implementation of `std::ops::BitOr` and `std::ops::BitOrAssign` traits for
`Async`.
- Implementation of `std::ops::BitXor` and `std::ops::BitXorAssign` traits for
`Async`.
- Implementation of `std::ops::Shl` and `std::ops::ShlAssign` traits for
`Async`.
- Implementation of `std::ops::Shr` and `std::ops::ShrAssign` traits for
`Async`.
