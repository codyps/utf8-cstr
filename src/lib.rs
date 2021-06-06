#[cfg(test)]
#[macro_use]
extern crate assert_matches;

use std::ffi::CStr;
use std::str::Utf8Error;
use std::convert::AsRef;
use std::mem::transmute;
use std::os::raw::c_char;
use std::ops::Deref;
use std::fmt;
use std::slice;


#[derive(Debug)]
pub enum Utf8CStrError {
    NoNulTerm,
    EmbeddedNulTerm(usize),
    Utf8Error(Utf8Error)
}

/**
 * A wrapper that promises it's contents are null-terminated & validly utf-8 encoded
 *
 * Plain `std::ffi::CStr` only promises null termination, but some ffi (and other bits) require
 * strings that are both valid utf8 and null terminated.
 */
#[derive(PartialEq, Eq)]
#[repr(C)]
pub struct Utf8CStr {
    inner: CStr,
}

impl fmt::Debug for Utf8CStr {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let s : &str = self.as_ref();
        write!(fmt, "{:?}", s)
    }
}

impl fmt::Display for Utf8CStr {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let s : &str = self.as_ref();
        write!(fmt, "{}", s)
    }
}

impl Utf8CStr {
    /// Construct a `Utf8CStr` with no checking.
    ///
    /// # Safety
    ///
    ///  - `'a` must be the correct lifetime
    ///  - `v` must be nul terminated
    ///  - `v` must be utf-8 encoded (for use in `&str`)
    ///  - `l` must be the length of `v` including the nul terminator
    pub unsafe fn from_raw_parts<'a>(v: *const c_char, l: usize) -> &'a Self {
        Self::from_bytes_with_nul_unchecked(slice::from_raw_parts(v as *const u8, l))
    }

    /// Construct a `Utf8CStr` with minimal checking.
    ///
    /// This currently will scan for the terminating '\0' just to establish the length for various
    /// slices.
    ///
    /// # Safety
    ///
    ///  - `'a` must be the correct lifetime
    ///  - `v` must be nul terminated
    ///  - `v` must be utf-8 encoded (for use in `&str`)
    pub unsafe fn from_ptr_unchecked<'a>(v: *const c_char) -> &'a Self {
        Self::from_cstr_unchecked(CStr::from_ptr(v))
    }

    /// Failable conversion from a CStr.
    ///
    /// Verifies that the CStr is utf8 encoded.
    ///
    /// NOTE: Only handles non-mutable variants. We may want to accept &mut as well in the future.
    pub fn from_cstr(v: &CStr) -> Result<&Self, Utf8Error> {
        v.to_str()?;
        Ok(unsafe { transmute(v)})
    }

    /// Convert from a `&CStr` without any checking
    ///
    /// # Safety
    ///
    ///  - `v` must be valid utf8 for use in a `&str`
    pub unsafe fn from_cstr_unchecked(v: &CStr) -> &Utf8CStr {
        Self::from_bytes_with_nul_unchecked(v.to_bytes_with_nul())
    }

    /// Convert directly from bytes
    ///
    /// NOTE: right now this scans `b` a few times over. Ideally, we'd adjust it to only scan `b`
    /// once.
    pub fn from_bytes(b: &[u8]) -> Result<&Self, Utf8CStrError> {
        // FIXME: use from_bytes_with_nul when stabilized
        for (l, &v) in b[0..b.len() - 1].iter().enumerate() {
            if v == b'\0' {
                return Err(Utf8CStrError::EmbeddedNulTerm(l));
            }
        }
        if b[b.len() - 1] != b'\0' {
            return Err(Utf8CStrError::NoNulTerm);
        }

        let c = unsafe { CStr::from_bytes_with_nul_unchecked(b) };
        Self::from_cstr(c).map_err(|e| Utf8CStrError::Utf8Error(e))
    }

    /// Raw conversion from basic data type with no checking.
    pub unsafe fn from_bytes_with_nul_unchecked(b: &[u8]) -> &Self {
        transmute(CStr::from_bytes_with_nul_unchecked(b))
    }

    pub fn as_ptr(&self) -> *const c_char {
        let v : &CStr = self.as_ref();
        v.as_ptr()
    }

}

impl AsRef<str> for Utf8CStr {
    fn as_ref(&self) -> &str {
        unsafe { transmute(self.inner.to_bytes()) }
    }
}

impl AsRef<CStr> for Utf8CStr {
    fn as_ref(&self) -> &CStr {
        unsafe { transmute(self) }
    }
}

impl Deref for Utf8CStr {
    type Target = str;
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::Utf8CStr;
    use super::Utf8CStrError;
    #[test]
    fn it_works() {
        let x = Utf8CStr::from_bytes(b"hello\0").unwrap();
        assert_matches!(Utf8CStr::from_bytes(b"hell").err().unwrap(), Utf8CStrError::NoNulTerm);
        assert_matches!(Utf8CStr::from_bytes(b"hell\0d").err().unwrap(), Utf8CStrError::EmbeddedNulTerm(4));
        assert_matches!(Utf8CStr::from_bytes(&[8,1,23,4,0xff, 0]).err().unwrap(), Utf8CStrError::Utf8Error(_));


        println!("{:?}", x);
        println!("{}", x);

        assert_eq!(x, x);
        assert_ne!(x, Utf8CStr::from_bytes(b"hell\0").unwrap());

        let v = b"hello\0";
        let b = unsafe { Utf8CStr::from_raw_parts(v.as_ptr() as *const _, v.len()) };
        assert_eq!(b, x);
    }
}
