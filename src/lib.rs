#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Small library to unescape strings, without needing to allocate for strings
//! without escape sequences. Tries to support a variety of languages, including
//! through custom parsers if needed, though it mainly supports C-style escape
//! escape sequences by default.
//!
//! Escape sequences supported by default:
//! * `\a` to a bell character.
//! * `\b` to a backspace.
//! * `\f` to a form feed.
//! * `\n` to a line feed.
//! * `\t` to a (horizontal) tab.
//! * `\v` to a vertical tab.
//! * `\\` to a backslash.
//! * `\'` to a single quote.
//! * `\"` to a double quote.
//! * `\/` to a slash (unescaped per ECMAScript).
//! * `\` followed by a new line keeps the same new line.
//! * `\xNN` to the Unicode character in the two hex digits.
//! * `\uNNNN` as above, but with four hex digits.
//! * `\UNNNNNNNN` as above, but with eight hex digits.
//! * `\u{NN...}` as above, but with variable hex digits.
//! * octal sequences are decoded to the Unicode character.

use core::fmt;
use core::num::ParseIntError;

#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::borrow::Cow;
#[cfg(feature = "std")]
use std::borrow::Cow;

/// Errors which may be returned by the unescaper.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// Error type for a string ending in a backslash without a following escape
    /// sequence.
    IncompleteSequence,
    /// Error type for a string ending in a Unicode escape sequence (e.g. `\x`)
    /// without the appropriate amount of hex digits.
    IncompleteUnicode,
    /// Error type for a Unicode sequence without a valid character code.
    InvalidUnicode(u32),
    /// Error type for unknown escape sequences.
    UnknownSequence(char),
    /// Errors from parsing Unicode hexadecimal numbers.
    ParseIntError(ParseIntError),
}

impl From<ParseIntError> for Error {
    fn from(this: ParseIntError) -> Self {
        Error::ParseIntError(this)
    }
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::IncompleteSequence => f.write_str("unexpected end of string after `\\`"),
            Self::IncompleteUnicode => {
                f.write_str("unexpected end of string in Unicode escape sequence")
            }
            Self::InvalidUnicode(code) => write!(f, "invalid Unicode character code {code}"),
            Self::UnknownSequence(ch) => write!(f, "unknown escape sequence starting with `{ch}`"),
            Self::ParseIntError(err) => write!(f, "error parsing integer: {err}"),
        }
    }
}
#[cfg(feature = "std")]
impl std::error::Error for Error {}

/// A fragment of a string, either an escaped character or the largest string
/// slice before the next escape sequence.
pub enum StringFragment<'a> {
    /// A string slice between escape sequences.
    Raw(&'a str),
    /// An unescaped character from an escape sequence.
    Escaped(char),
    /// An escape sequence that produced no character.
    /// None of the default escape sequences do this, but some languages (e.g.
    /// Lua) have an escape sequence that trims out whitespace.
    Empty,
}

fn unicode_char(s: &str, chars: usize) -> Result<(char, &str), Error> {
    if s.len() < chars {
        Err(Error::IncompleteUnicode)
    } else {
        let num = u32::from_str_radix(&s[0..chars], 16)?;
        let ch = char::from_u32(num).ok_or(Error::InvalidUnicode(num))?;
        Ok((ch, &s[chars..]))
    }
}

// called after encountering the backslash
fn escape_sequence(s: &str) -> Result<(char, &str), Error> {
    let mut chars = s.chars();
    let next = chars.next().ok_or(Error::IncompleteSequence)?;
    match next {
        'a' => Ok(('\x07', chars.as_str())),
        'b' => Ok(('\x08', chars.as_str())),
        'f' => Ok(('\x0C', chars.as_str())),
        'n' => Ok(('\n', chars.as_str())),
        'r' => Ok(('\r', chars.as_str())),
        't' => Ok(('\t', chars.as_str())),
        'v' => Ok(('\x0B', chars.as_str())),
        '\\' | '\'' | '\"' | '/' => Ok((next, chars.as_str())),
        '\r' | '\n' => Ok((next, chars.as_str())),
        'x' => unicode_char(chars.as_str(), 2),
        'u' => {
            let s = chars.as_str();
            if chars.next() == Some('{') {
                let s = chars.as_str();
                let size = chars.by_ref().take_while(|n| *n != '}').count();
                let num = u32::from_str_radix(&s[0..size], 16)?;
                let ch = char::from_u32(num).ok_or(Error::InvalidUnicode(num))?;
                Ok((ch, chars.as_str()))
            } else {
                unicode_char(s, 4)
            }
        }
        'U' => unicode_char(chars.as_str(), 8),
        _ => {
            let count = s.chars().take_while(|n| n.is_digit(8)).count().min(3);
            if count > 0 {
                let num = u32::from_str_radix(&s[0..count], 8)?;
                let ch = char::from_u32(num).ok_or(Error::InvalidUnicode(num))?;
                Ok((ch, &s[count..]))
            } else {
                Err(Error::UnknownSequence(next))
            }
        }
    }
}

/// An iterator producing unescaped characters of a string.
#[derive(Clone, Debug)]
pub struct UnescapeDefault<'a> {
    split: core::str::Split<'a, char>,
    rem: Option<core::str::Chars<'a>>,
}

impl<'a> UnescapeDefault<'a> {
    /// Make a new unescaper over the given string.
    pub fn new(from: &'a str) -> Self {
        let mut split = from.split('\\');
        let rem = split
            .next()
            .and_then(|s| if s.is_empty() { None } else { Some(s.chars()) });
        Self { split, rem }
    }

    /// Get the next string fragment rather than just the next character.
    /// Advances the iterator accordingly.
    pub fn next_fragment(&mut self) -> Option<Result<StringFragment<'a>, Error>> {
        if let Some(rem) = self.rem.take() {
            let s = rem.as_str();
            Some(Ok(StringFragment::Raw(s)))
        } else {
            self.next().map(|opt| opt.map(StringFragment::Escaped))
        }
    }
}

impl<'a> Iterator for UnescapeDefault<'a> {
    type Item = Result<char, Error>;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(ref mut rem) = self.rem {
            if let Some(next) = rem.next() {
                Some(Ok(next))
            } else {
                self.rem = None;
                self.next()
            }
        } else {
            let next = self.split.next()?;
            if next.is_empty() {
                match self.split.next() {
                    None => Some(Err(Error::IncompleteSequence)),
                    Some("") => Some(Ok('\\')),
                    Some(s) => {
                        self.rem = Some(s.chars());
                        Some(Ok('\\'))
                    }
                }
            } else {
                Some(match escape_sequence(next) {
                    Ok((ch, rem)) => {
                        if !rem.is_empty() {
                            self.rem = Some(rem.chars());
                        }
                        Ok(ch)
                    }
                    Err(e) => Err(e),
                })
            }
        }
    }
}
impl<'a> core::iter::FusedIterator for UnescapeDefault<'a> {}

/// Unescape the string into a [`std::borrow::Cow`] string which only allocates
/// if any escape sequences were found; otherwise, the original string is
/// returned unchanged.
#[cfg(any(feature = "std", feature = "alloc"))]
pub fn unescape_default(s: &str) -> Result<Cow<str>, Error> {
    let mut out = Cow::default();
    let mut unescaped = UnescapeDefault::new(s);
    while let Some(fragment) = unescaped.next_fragment().transpose()? {
        match fragment {
            StringFragment::Raw(s) => out += s,
            StringFragment::Escaped(c) => out.to_mut().push(c),
            StringFragment::Empty => (),
        }
    }
    Ok(out)
}

/// An unescaper using a custom escape sequence method instead of the default.
/// Otherwise functions the same as [`UnescapeDefault`].
#[derive(Clone, Debug)]
pub struct Unescape<'a, F: FnMut(&str) -> Result<(Option<char>, &str), E>, E: From<Error>> {
    split: core::str::Split<'a, char>,
    rem: Option<core::str::Chars<'a>>,
    escape_sequence: F,
}

impl<'a, F: FnMut(&str) -> Result<(Option<char>, &str), E>, E: From<Error>> Unescape<'a, F, E> {
    /// Make a new unescaper over the given string, using the given escape
    /// sequence function rather than the default one.
    ///
    /// The escape sequence parser is called _after_ a backslash has been found,
    /// and shouldn't check for the presence of one. The tuple in the `Result`
    /// should contain the character returned (or `None` if the sequence
    /// produces no character) and the remaining portion of the string after
    /// parsing; e.g. a string `"\nabc"` should return `('\n', "abc")`.
    pub fn new(escape_sequence: F, from: &'a str) -> Self {
        let mut split = from.split('\\');
        let rem = split
            .next()
            .and_then(|s| if s.is_empty() { None } else { Some(s.chars()) });
        Self {
            split,
            rem,
            escape_sequence,
        }
    }

    /// Get the next string fragment rather than just the next character.
    /// Advances the iterator accordingly.
    pub fn next_fragment(&mut self) -> Option<Result<StringFragment<'a>, E>> {
        if let Some(rem) = self.rem.take() {
            let s = rem.as_str();
            Some(Ok(StringFragment::Raw(s)))
        } else {
            self.next().map(|opt| {
                opt.map(|ch| {
                    if let Some(ch) = ch {
                        StringFragment::Escaped(ch)
                    } else {
                        StringFragment::Empty
                    }
                })
            })
        }
    }
}

impl<'a, F: FnMut(&str) -> Result<(Option<char>, &str), E>, E: From<Error>> Iterator
    for Unescape<'a, F, E>
{
    type Item = Result<Option<char>, E>;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(ref mut rem) = self.rem {
            if let Some(next) = rem.next() {
                Some(Ok(Some(next)))
            } else {
                self.rem = None;
                self.next()
            }
        } else {
            let next = self.split.next()?;
            if next.is_empty() {
                Some(if let Some(s) = self.split.next() {
                    match (self.escape_sequence)("\\") {
                        Ok((ch, _)) => {
                            if !s.is_empty() {
                                self.rem = Some(s.chars());
                            }
                            Ok(ch)
                        }
                        Err(e) => Err(e),
                    }
                } else {
                    Err(E::from(Error::IncompleteSequence))
                })
            } else {
                Some(match (self.escape_sequence)(next) {
                    Ok((ch, rem)) => {
                        if !rem.is_empty() {
                            self.rem = Some(rem.chars());
                        }
                        Ok(ch)
                    }
                    Err(e) => Err(e),
                })
            }
        }
    }
}
impl<'a, F: FnMut(&str) -> Result<(Option<char>, &str), E>, E: From<Error>>
    core::iter::FusedIterator for Unescape<'a, F, E>
{
}

/// Unescape the string like [`unescape_default`], but with a custom escape
/// sequence parser.
///
/// The escape sequence parser is used instead of the default escape sequences.
/// More information on the parser can be found at [`Unescape::new`].
#[cfg(any(feature = "std", feature = "alloc"))]
pub fn unescape<F: FnMut(&str) -> Result<(Option<char>, &str), E>, E: From<Error>>(
    escape_sequence: F,
    s: &str,
) -> Result<Cow<str>, E> {
    let mut out = Cow::default();
    let mut unescaped = Unescape::new(escape_sequence, s);
    while let Some(fragment) = unescaped.next_fragment().transpose()? {
        match fragment {
            StringFragment::Raw(s) => out += s,
            StringFragment::Escaped(c) => out.to_mut().push(c),
            StringFragment::Empty => (),
        }
    }
    Ok(out)
}

#[cfg(all(test, feature = "std"))]
mod test {
    use super::*;
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;
    use std::borrow::Cow;

    #[test]
    fn borrow_strings_without_escapes() {
        assert!(matches!(
            unescape_default("hello").unwrap(),
            Cow::Borrowed(_)
        ));
        assert!(matches!(
            unescape_default("longer\nstring").unwrap(),
            Cow::Borrowed(_)
        ));
    }

    #[test]
    fn unescapes_backslashes() {
        assert_eq!(unescape_default(r"\\").unwrap(), "\\");
        assert_eq!(unescape_default(r"\\\\").unwrap(), "\\\\");
        assert_eq!(unescape_default(r"\\\\\\").unwrap(), "\\\\\\");
        assert_eq!(unescape_default(r"\\a").unwrap(), "\\a");
        assert_eq!(unescape_default(r"\\\"), Err(Error::IncompleteSequence));
    }

    #[test]
    fn unicode_escapes() {
        assert_eq!(unescape_default(r"\u1234").unwrap(), "\u{1234}");
        assert_eq!(unescape_default(r"\u{1234}").unwrap(), "\u{1234}");
        assert_eq!(unescape_default(r"\U0010FFFF").unwrap(), "\u{10FFFF}");
        assert_eq!(unescape_default(r"\x20").unwrap(), " ");
    }

    #[quickcheck]
    fn inverts_escape_default(s: String) -> TestResult {
        let escaped: String = s.escape_default().collect();
        if escaped == s {
            // only bother testing strings that need escaped
            return TestResult::discard();
        }
        let unescaped = unescape_default(&escaped);
        match unescaped {
            Ok(unescaped) => TestResult::from_bool(s == unescaped),
            Err(e) => TestResult::error(e.to_string()),
        }
    }
}
#[cfg(all(test, not(feature = "std")))]
compile_error!("Tests currently require `std` feature");
