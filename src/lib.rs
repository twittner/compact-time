//! 64-bit time value with nanosecond precision.
//!
//! Time values range from 1970-01-01T00:00:00.0Z to 2554-07-21T23:34:33.709551615Z.
mod source;

use std::{fmt, time::{SystemTime, UNIX_EPOCH, Duration}, ops::{Add, Sub}};

use minicbor::{Encode, Decode};
use serde::{Serialize, Deserialize};

pub use source::TimeSource;

const NANO: u64 = 1_000_000_000;

/// A time value with nanosecond precision.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Encode, Decode, Serialize, Deserialize)]
#[cbor(transparent)]
#[serde(transparent)]
pub struct Time(#[n(0)] u64);

impl Time {
    /// The minimum time value.
    pub const MIN: Self = Time(0);

    /// The maximum time value.
    pub const MAX: Self = Time(u64::MAX);

    /// Get the current system time.
    ///
    /// # Panics
    ///
    /// If the reported system time is before 1970-01-01T00:00:00Z or after
    /// 2554-07-21T23:34:33.709551615Z.
    pub fn now() -> Self {
        Self::try_now().expect("SystemTime in range")
    }

    /// Get the current system time.
    ///
    /// May fail if the reported time is before 1970-01-01T00:00:00Z or after
    /// 2554-07-21T23:34:33.709551615Z
    pub fn try_now() -> Result<Self, OutOfRange> {
        let t = SystemTime::now();
        let Ok(d) = t.duration_since(UNIX_EPOCH) else {
            return Err(OutOfRange(()))
        };
        Self::try_from_sn(d.as_secs(), d.subsec_nanos())
    }

    /// Get the current system time using `CLOCK_REALTIME_COARSE`.
    ///
    /// This is faster but less precise than the `Self::now`.
    ///
    /// # Panics
    ///
    /// If the reported system time is before 1970-01-01T00:00:00Z or after
    /// 2554-07-21T23:34:33.709551615Z.
    #[cfg(feature = "coarse")]
    pub fn coarse() -> Self {
        Self::try_coarse().expect("valid time")
    }

    /// Get the current system time using `CLOCK_REALTIME_COARSE`.
    ///
    /// This is faster but less precise than the `Self::now`.
    ///
    /// May fail if the reported time is before 1970-01-01T00:00:00Z or after
    /// 2554-07-21T23:34:33.709551615Z
    #[cfg(feature = "coarse")]
    pub fn try_coarse() -> Result<Self, OutOfRange> {
        use rustix::time::{clock_gettime, ClockId};
        let t = clock_gettime(ClockId::RealtimeCoarse);
        if t.tv_sec < 0 || t.tv_nsec < 0 {
            return Err(OutOfRange(()))
        }
        Self::try_from_sn(t.tv_sec as u64, t.tv_nsec as u64)
    }

    /// Construct a time value from the given seconds.
    ///
    /// # Panics
    ///
    /// If seconds are out of range.
    pub fn from_seconds(s: u64) -> Self {
        Self::try_from_seconds(s).expect("seconds in range")
    }

    /// Contruct a time value from the given seconds.
    pub fn try_from_seconds(s: u64) -> Result<Self, OutOfRange> {
        Self::try_from_sn(s, 0u64)
    }

    /// Construct a time value from the given nanoseconds.
    pub const fn from_nanos(n: u64) -> Self {
        Self(n)
    }

    /// Seconds since the Unix epoch.
    pub const fn seconds(self) -> u64 {
        self.0 / NANO
    }

    /// Nanoseconds since the Unix epoch.
    pub const fn nanos(self) -> u64 {
        self.0
    }

    /// Return sub-second nanos.
    pub const fn second_nanos(self) -> u64 {
        self.nanos() - self.seconds() * NANO
    }

    pub fn try_add(self, t: Time) -> Result<Self, OutOfRange> {
        let n = self.0.checked_add(t.0).ok_or(OutOfRange(()))?;
        Ok(Self(n))
    }

    pub fn try_sub(self, t: Time) -> Result<Self, OutOfRange> {
        let n = self.0.checked_sub(t.0).ok_or(OutOfRange(()))?;
        Ok(Self(n))
    }

    pub fn add_nanos(self, n: u64) -> Self {
        self.add_nanos_checked(n).expect("no overflow")
    }

    pub fn add_seconds(self, s: u64) -> Self {
        self.add_seconds_checked(s).expect("no overflow")
    }

    pub fn add_minutes(self, m: u64) -> Self {
        self.add_minutes_checked(m).expect("no overflow")
    }

    pub fn add_hours(self, h: u64) -> Self {
        self.add_hours_checked(h).expect("no overflow")
    }

    pub fn add_days(self, d: u64) -> Self {
        self.add_days_checked(d).expect("no overflow")
    }

    pub fn add_nanos_checked(self, n: u64) -> Option<Self> {
        let n = self.0.checked_add(n)?;
        Some(Self(n))
    }

    pub fn add_seconds_checked(self, s: u64) -> Option<Self> {
        self.add_nanos_checked(s.checked_mul(NANO)?)
    }

    pub fn add_minutes_checked(self, m: u64) -> Option<Self> {
        self.add_seconds_checked(m.checked_mul(60)?)
    }

    pub fn add_hours_checked(self, h: u64) -> Option<Self> {
        self.add_seconds_checked(h.checked_mul(3600)?)
    }

    pub fn add_days_checked(self, d: u64) -> Option<Self> {
        self.add_seconds_checked(d.checked_mul(24 * 3600)?)
    }

    pub fn sub_nanos(self, n: u64) -> Self {
        self.sub_nanos_checked(n).expect("no underflow")
    }

    pub fn sub_seconds(self, s: u64) -> Self {
        self.sub_seconds_checked(s).expect("no underflow")
    }

    pub fn sub_minutes(self, m: u64) -> Self {
        self.sub_minutes_checked(m).expect("no underflow")
    }

    pub fn sub_hours(self, h: u64) -> Self {
        self.sub_hours_checked(h).expect("no underflow")
    }

    pub fn sub_days(self, d: u64) -> Self {
        self.sub_days_checked(d).expect("no underflow")
    }

    pub fn sub_nanos_checked(self, n: u64) -> Option<Self> {
        let n = self.0.checked_sub(n)?;
        Some(Self(n))
    }

    pub fn sub_seconds_checked(self, s: u64) -> Option<Self> {
        self.sub_nanos_checked(s.checked_mul(NANO)?)
    }

    pub fn sub_minutes_checked(self, m: u64) -> Option<Self> {
        self.sub_seconds_checked(m.checked_mul(60)?)
    }

    pub fn sub_hours_checked(self, h: u64) -> Option<Self> {
        self.sub_seconds_checked(h.checked_mul(3600)?)
    }

    pub fn sub_days_checked(self, d: u64) -> Option<Self> {
        self.sub_seconds_checked(d.checked_mul(24 * 3600)?)
    }

    pub const fn to_duration(self) -> Duration {
        let s = self.seconds();
        let n = self.second_nanos();
        Duration::new(s, n as u32)
    }

    pub fn duration_since(self, earlier: Self) -> Option<Duration> {
        self.to_duration().checked_sub(earlier.to_duration())
    }

    pub fn as_u64(self) -> u64 {
        self.0
    }

    #[cfg(feature = "utc")]
    pub fn to_utc_string(self) -> Option<String> {
        let s = self.seconds();
        let n = self.second_nanos();
        if let Ok(utc) = tz::UtcDateTime::from_timespec(s as i64, n as u32) {
            Some(utc.to_string())
        } else {
            None
        }
    }

    /// Try to construct a time value from seconds and nanoseconds.
    fn try_from_sn<S: Into<u64>, N: Into<u64>>(s: S, n: N) -> Result<Self, OutOfRange> {
        let n = s.into()
            .checked_mul(NANO)
            .and_then(|x| x.checked_add(n.into()))
            .ok_or(OutOfRange(()))?;
        Ok(Self(n))
    }
}

impl From<Time> for u64 {
    fn from(value: Time) -> Self {
        value.0
    }
}

impl From<u64> for Time {
    fn from(n: u64) -> Self {
        Self(n)
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
            .add_nanos(d.subsec_nanos().into())
    }
}

impl Add<Time> for Time {
    type Output = Self;

    fn add(self, t: Time) -> Self::Output {
        self.add_nanos(t.nanos())
    }
}

impl Sub<Duration> for Time {
    type Output = Self;

    fn sub(self, d: Duration) -> Self::Output {
        self.sub_seconds(d.as_secs())
            .sub_nanos(d.subsec_nanos().into())
    }
}

impl Sub<Time> for Time {
    type Output = Self;

    fn sub(self, t: Time) -> Self::Output {
        self.sub_nanos(t.nanos())
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
    use quickcheck::{Arbitrary, Gen, quickcheck, TestResult};
    use super::{NANO, Time};

    impl Arbitrary for Time {
        fn arbitrary(g: &mut Gen) -> Self {
            Time::from(u64::arbitrary(g))
        }
    }

    quickcheck! {
        fn prop_sec_nano_id(s: u64, n: u64) -> TestResult {
            let n = n % NANO; // subsec nanos
            if s.checked_mul(NANO).and_then(|s| s.checked_add(n)).is_none() {
                return TestResult::discard()
            }
            let t = Time::try_from_sn(s, n).unwrap();
            let b = t.seconds() == s && t.second_nanos() == n;
            TestResult::from_bool(b)
        }

        fn prop_add_sub_nanos_id(t: Time, n: u64) -> TestResult {
            let Some(u) = t.add_nanos_checked(n) else {
                return TestResult::discard()
            };
            TestResult::from_bool(u.sub_nanos(n) == t)
        }

        fn prop_add_sub_secs_id(t: Time, s: u64) -> TestResult {
            let Some(u) = t.add_seconds_checked(s) else {
                return TestResult::discard()
            };
            TestResult::from_bool(u.sub_seconds(s) == t)
        }

        fn prop_add_sub_mins_id(t: Time, m: u64) -> TestResult {
            let Some(u) = t.add_minutes_checked(m) else {
                return TestResult::discard()
            };
            TestResult::from_bool(u.sub_minutes(m) == t)
        }

        fn prop_add_sub_hours_id(t: Time, h: u64) -> TestResult {
            let Some(u) = t.add_hours_checked(h) else {
                return TestResult::discard()
            };
            TestResult::from_bool(u.sub_hours(h) == t)
        }

        fn prop_add_sub_days_id(t: Time, d: u64) -> TestResult {
            let Some(u) = t.add_days_checked(d) else {
                return TestResult::discard()
            };
            TestResult::from_bool(u.sub_days(d) == t)
        }

        fn prop_second_nanos(t: Time) -> bool {
            t.nanos() - t.seconds() * NANO == t.second_nanos()
        }

        fn prop_add_1s_as_nanos(t: Time) -> TestResult {
            if Time::MAX.try_sub(t).map(|d| d < NANO.into()).unwrap_or(true) {
                return TestResult::discard()
            }
            let u = t.add_nanos(NANO);
            let b = u.seconds() - t.seconds() == 1 && u.second_nanos() - t.second_nanos() == 0;
            TestResult::from_bool(b)
        }
    }

    #[test]
    fn max_time() {
        assert!(Time::MAX.add_nanos_checked(1).is_none());
        assert!(Time::MAX.add_seconds_checked(1).is_none());
        assert!(Time::MAX.add_minutes_checked(1).is_none());
        assert!(Time::MAX.add_hours_checked(1).is_none());
        assert!(Time::MAX.add_days_checked(1).is_none());
    }

    #[test]
    fn min_time() {
        assert!(Time::MIN.sub_nanos_checked(1).is_none());
        assert!(Time::MIN.sub_seconds_checked(1).is_none());
        assert!(Time::MIN.sub_minutes_checked(1).is_none());
        assert!(Time::MIN.sub_hours_checked(1).is_none());
        assert!(Time::MIN.sub_days_checked(1).is_none());
    }
}
