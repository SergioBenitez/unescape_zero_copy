# Unescape (zero copy)

[![Crates.io](https://img.shields.io/crates/v/unescape_zero_copy.svg)](https://crates.io/crates/unescape_zero_copy)
[![MIT License](https://img.shields.io/github/license/MWPuppire/unescape_zero_copy.svg)](https://github.com/MWPuppire/unescape_zero_copy/blob/main/LICENSE)

Unescapes strings with C-style escape sequences, written to minimize memory
copying. Other crates (e.g. [`unescaper`](https://crates.io/crates/unescaper))
like to allocate every for every string, but most strings don't need any
unescaping and so can be returned as-is. This library does that.

Supports `no_std` by returning an iterator, or can return a `Cow` that allocates
as needed with the `std` feature (enabled by default).

No automated tests yet cause I'm lazy, but it has been manually tested for many
cases.

## Usage

```rust
assert_eq!(unescape_zero_copy::unescape(r"Hello\x0aworld").unwrap(), "Hello\nworld");
```

## License

The code is released under the MIT license.
