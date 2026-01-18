//! Default hasher for IndexMap.

use core::hash::{BuildHasher, Hasher};
use foldhash::fast::RandomState;

/// Default hash builder for IndexMap.
#[derive(Clone, Debug, Default)]
pub struct DefaultHashBuilder {
    inner: RandomState,
}

impl BuildHasher for DefaultHashBuilder {
    type Hasher = DefaultHasher;

    #[inline(always)]
    fn build_hasher(&self) -> Self::Hasher {
        DefaultHasher {
            inner: self.inner.build_hasher(),
        }
    }
}

/// Default hasher.
#[derive(Clone)]
pub struct DefaultHasher {
    inner: <RandomState as BuildHasher>::Hasher,
}

impl Hasher for DefaultHasher {
    #[inline(always)]
    fn write(&mut self, bytes: &[u8]) {
        self.inner.write(bytes);
    }

    #[inline(always)]
    fn write_u8(&mut self, i: u8) {
        self.inner.write_u8(i);
    }

    #[inline(always)]
    fn write_u16(&mut self, i: u16) {
        self.inner.write_u16(i);
    }

    #[inline(always)]
    fn write_u32(&mut self, i: u32) {
        self.inner.write_u32(i);
    }

    #[inline(always)]
    fn write_u64(&mut self, i: u64) {
        self.inner.write_u64(i);
    }

    #[inline(always)]
    fn write_u128(&mut self, i: u128) {
        self.inner.write_u128(i);
    }

    #[inline(always)]
    fn write_usize(&mut self, i: usize) {
        self.inner.write_usize(i);
    }

    #[inline(always)]
    fn write_i8(&mut self, i: i8) {
        self.inner.write_i8(i);
    }

    #[inline(always)]
    fn write_i16(&mut self, i: i16) {
        self.inner.write_i16(i);
    }

    #[inline(always)]
    fn write_i32(&mut self, i: i32) {
        self.inner.write_i32(i);
    }

    #[inline(always)]
    fn write_i64(&mut self, i: i64) {
        self.inner.write_i64(i);
    }

    #[inline(always)]
    fn write_i128(&mut self, i: i128) {
        self.inner.write_i128(i);
    }

    #[inline(always)]
    fn write_isize(&mut self, i: isize) {
        self.inner.write_isize(i);
    }

    #[inline(always)]
    fn finish(&self) -> u64 {
        self.inner.finish()
    }
}
