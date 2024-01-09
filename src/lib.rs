//! 64-bit time value with nanosecond precision.
//!
//! The upper 34 bits represent seconds since the UNIX epoch (1970-01-01 00:00:00) until the year
//! 2514. The remaining 30 bits represent sub-second nanoseconds.

mod source;

use std::{fmt, time::{SystemTime, UNIX_EPOCH, Duration}, ops::Add};

use minicbor::{Encode, Decode};
use serde::{Serialize, Deserialize};

pub use source::TimeSource;

/// Bitmask leaving subsecond nanos.
const NANO_MASK: u64 = 0x3FFF_FFFF;

/// Max. number of seconds the time value can represent.
const MAX_SECONDS: u64 = 0x3_FFFF_FFFF;

/// Max. number of subsecond nanoseconds.
const MAX_SUBSEC_NANOS: u32 = 999_999_999;

/// A time value with nanosecond precision.
///
/// Values range from 1970-01-01 00:00:00 to 2514-05-30 01:53:03.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Encode, Decode, Serialize, Deserialize)]
#[cbor(transparent)]
#[serde(transparent)]
pub struct Time(#[n(0)] u64);

impl Time {
    /// The minimum time value.
    pub const MIN: Self = Time(0);

    /// The maximum time value.
    pub const MAX: Self = Time(0xFFFF_FFFF_FB9A_C9FF);

    /// Create a new time value.
    ///
    /// # Panics
    ///
    /// This method asserts that seconds do not exceed 2^34 and that nanoseconds are less than 10^9.
    pub const fn new(seconds: u64, nanos: u32) -> Self {
        assert!(seconds <= MAX_SECONDS);
        assert!(nanos <= MAX_SUBSEC_NANOS);
        Self(seconds << 30 | nanos as u64)
    }

    /// Try to create a new time value.
    pub const fn try_new(seconds: u64, nanos: u32) -> Result<Self, OutOfRange> {
        if seconds > MAX_SECONDS || nanos > MAX_SUBSEC_NANOS {
            return Err(OutOfRange(()))
        }
        Ok(Self(seconds << 30 | nanos as u64))
    }

    /// Get the current system time.
    ///
    /// # Panics
    ///
    /// If the reported system time is before 1970-01-01 00:00:00.
    pub fn now() -> Self {
        Self::try_now().expect("SystemTime >= Unix epoch")
    }

    /// Get the current system time.
    ///
    /// May fail if the reported time is before 1970-01-01 00:00:00.
    pub fn try_now() -> Result<Self, OutOfRange> {
        let t = SystemTime::now();
        let Ok(d) = t.duration_since(UNIX_EPOCH) else {
            return Err(OutOfRange(()))
        };
        Ok(Self::new(d.as_secs(), d.subsec_nanos()))
    }

    /// Get the current system time using `CLOCK_REALTIME_COARSE`.
    ///
    /// This is faster but less precise than the `Self::now`.
    ///
    /// # Panics
    ///
    /// If the reported time is out of bounds.
    #[cfg(feature = "coarse")]
    pub fn coarse() -> Self {
        Self::try_coarse().expect("valid time")
    }

    /// Get the current system time using `CLOCK_REALTIME_COARSE`.
    ///
    /// This is faster but less precise than the `Self::now`.
    #[cfg(feature = "coarse")]
    pub fn try_coarse() -> Result<Self, OutOfRange> {
        use rustix::time::{clock_gettime, ClockId};
        let t = clock_gettime(ClockId::RealtimeCoarse);
        if t.tv_sec < 0 || t.tv_nsec < 0 || t.tv_sec > MAX_SECONDS as i64 || t.tv_nsec > MAX_SUBSEC_NANOS.into() {
            return Err(OutOfRange(()))
        }
        Ok(Self((t.tv_sec as u64) << 30 | t.tv_nsec as u64))
    }

    /// Contruct a time value from the given seconds.
    pub const fn try_from_seconds(s: u64) -> Result<Self, OutOfRange> {
        if s > MAX_SECONDS {
            return Err(OutOfRange(()))
        }
        Ok(Self(s << 30))
    }

    /// Contruct a time value from the given seconds.
    ///
    /// # Panics
    ///
    /// If seconds are out of range.
    pub fn from_seconds(s: u64) -> Self {
        Self::try_from_seconds(s).expect("seconds in range")
    }

    pub const fn seconds(self) -> u64 {
        self.0 >> 30
    }

    pub const fn second_nanos(self) -> u32 {
        (self.0 & NANO_MASK) as u32
    }

    pub fn add_nanos(self, n: u32) -> Self {
        self.add_nanos_checked(n).expect("no overflow")
    }

    pub fn add_seconds(self, s: u64) -> Self {
        self.add_seconds_checked(s).expect("no overflow")
    }

    pub fn add_minutes(self, h: u32) -> Self {
        self.add_minutes_checked(h).expect("no overflow")
    }

    pub fn add_hours(self, h: u32) -> Self {
        self.add_hours_checked(h).expect("no overflow")
    }

    pub fn add_days(self, d: u16) -> Self {
        self.add_days_checked(d).expect("no overflow")
    }

    pub fn add_nanos_checked(self, n: u32) -> Option<Self> {
        let n = self.second_nanos().checked_add(n)?;
        let s = self.seconds().checked_add((n / 1_000_000_000).into())?;
        if s > MAX_SECONDS {
            return None
        }
        Some(Self::new(s, n % 1_000_000_000))
    }

    pub fn add_seconds_checked(self, s: u64) -> Option<Self> {
        let s = self.seconds().checked_add(s)?;
        if s > MAX_SECONDS {
            return None
        }
        Some(Self::new(s, self.second_nanos()))
    }

    pub fn add_minutes_checked(self, h: u32) -> Option<Self> {
        self.add_seconds_checked(u64::from(h) * 60)
    }

    pub fn add_hours_checked(self, h: u32) -> Option<Self> {
        self.add_seconds_checked(u64::from(h) * 3600)
    }

    pub fn add_days_checked(self, d: u16) -> Option<Self> {
        self.add_seconds_checked(u64::from(d) * 24 * 3600)
    }

    pub fn sub_seconds(self, s: u64) -> Self {
        self.sub_seconds_checked(s).expect("no underflow")
    }

    pub fn sub_seconds_checked(self, s: u64) -> Option<Self> {
        let s = self.seconds().checked_sub(s)?;
        Some(Self::new(s, self.second_nanos()))
    }

    pub const fn to_duration(self) -> Duration {
        Duration::new(self.seconds(), self.second_nanos())
    }

    pub fn duration_since(self, earlier: Self) -> Option<Duration> {
        self.to_duration().checked_sub(earlier.to_duration())
    }

    #[cfg(feature = "utc")]
    pub fn to_utc_string(self) -> Option<String> {
        let s = self.seconds();
        let n = self.second_nanos();
        if let Ok(utc) = tz::UtcDateTime::from_timespec(s as i64, n) {
            Some(utc.to_string())
        } else {
            None
        }
    }
}

impl From<Time> for u64 {
    fn from(value: Time) -> Self {
        value.0
    }
}

impl TryFrom<u64> for Time {
    type Error = OutOfRange;

    fn try_from(n: u64) -> Result<Self, Self::Error> {
        let t = Self(n);
        if t.second_nanos() > MAX_SUBSEC_NANOS {
            return Err(OutOfRange(()))
        }
        Ok(t)
    }
}

/// Error if values go out of range.
#[derive(Debug)]
pub struct OutOfRange(());

impl fmt::Display for OutOfRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("out of range")
    }
}

impl std::error::Error for OutOfRange {}

impl Add<Duration> for Time {
    type Output = Self;

    fn add(self, d: Duration) -> Self::Output {
        self.add_seconds(d.as_secs())
            .add_nanos(d.subsec_nanos())
    }
}

impl fmt::Display for Time {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.seconds();
        let n = self.second_nanos();
        write!(f, "{s}.{n}")
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;
    use super::Time;

    #[test]
    fn max_time() {
        // time to parts and back
        let s = Time::MAX.seconds();
        let n = Time::MAX.second_nanos();
        let t = Time::new(s, n);
        assert_eq!(s, t.seconds());
        assert_eq!(n, t.second_nanos());

        // can create a time from the max. time integer
        let n: u64 = Time::MAX.into();
        assert!(Time::try_from(n).is_ok());
        assert!(Time::try_from(n + 1).is_err());
        assert!(Time::try_from(u64::MAX).is_err());

        // check overflow handling
        assert!(Time::MAX.add_nanos_checked(1).is_none());
        assert!(Time::MAX.add_seconds_checked(1).is_none());
    }

    #[test]
    fn add_nanos() {
        let a = Time::new(0, 999_999_999);
        let b = a.add_nanos(1);
        assert_eq!(b, Time::new(1, 0));

        let a = Time::new(1, 500);
        let b = a.add_nanos(1000);
        assert_eq!(b, Time::new(1, 1500));
    }

    #[test]
    fn add_time() {
        let a = Time::now();
        let b = a + Duration::from_secs(30);
        let c = b.to_duration();
        assert_eq!(Duration::from_secs(30), c - a.to_duration())
    }

    #[test]
    fn conversion() {
        let t = Time::now();
        assert_eq!(Some(t), Time::try_from(u64::from(t)).ok())
    }
}
