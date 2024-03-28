//! 64-bit time value with nanosecond precision.
//!
//! Time values range from 1970-01-01T00:00:00.000000000Z to 2554-07-21T23:34:33.709551615Z.
mod source;

use std::{fmt, time::{SystemTime, UNIX_EPOCH, Duration}, ops::{Add, Sub}};

pub use source::TimeSource;

const NANO: u64 = 1_000_000_000;

/// A time value with nanosecond precision.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "minicbor", derive(minicbor::Encode, minicbor::Decode), cbor(transparent))]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize), serde(transparent))]
pub struct Time(#[cfg_attr(feature = "minicbor", n(0))] u64);

impl Time {
    /// The minimum time value (1970-01-01T00:00:00.000000000Z).
    pub const MIN: Self = Time(0);

    /// The maximum time value (2554-07-21T23:34:33.709551615Z).
    pub const MAX: Self = Time(u64::MAX);

    /// Get the current system time.
    ///
    /// # Panics
    ///
    /// If the reported system time is less than [`Time::MIN`] or greater than [`Time::MAX`].
    pub fn now() -> Self {
        Self::try_now().expect("SystemTime in range")
    }

    /// Get the current system time.
    ///
    /// Fails if the reported system time is less than [`Time::MIN`] or greater than [`Time::MAX`].
    pub fn try_now() -> Result<Self, OutOfRange> {
        let t = SystemTime::now();
        let Ok(d) = t.duration_since(UNIX_EPOCH) else {
            return Err(OutOfRange(()))
        };
        Self::try_from_sn(d.as_secs(), d.subsec_nanos())
    }

    /// Get the current system time using `CLOCK_REALTIME_COARSE`.
    ///
    /// This is faster but less precise than [`Time::now`].
    ///
    /// # Panics
    ///
    /// If the reported system time is less than [`Time::MIN`] or greater than [`Time::MAX`].
    #[cfg(feature = "coarse")]
    pub fn coarse() -> Self {
        Self::try_coarse().expect("valid time")
    }

    /// Get the current system time using `CLOCK_REALTIME_COARSE`.
    ///
    /// This is faster but less precise than [`Time::now`].
    ///
    /// Fails if the reported system time is less than [`Time::MIN`] or greater than [`Time::MAX`].
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
    /// If the given seconds are greater than [`Time::MAX`] seconds.
    pub fn from_seconds(s: u64) -> Self {
        Self::try_from_seconds(s).expect("seconds in range")
    }

    /// Construct a time value from the given seconds.
    ///
    /// Fails if the given seconds are greater than [`Time::MAX`] seconds.
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

    /// Subsecond nanoseconds.
    pub const fn second_nanos(self) -> u64 {
        self.nanos() - self.seconds() * NANO
    }

    /// Try to add the given time value.
    ///
    /// Fails if the result would be greater than [`Time::MAX`].
    pub fn try_add(self, t: Time) -> Result<Self, OutOfRange> {
        let n = self.0.checked_add(t.0).ok_or(OutOfRange(()))?;
        Ok(Self(n))
    }

    /// Try to substract the given time value.
    ///
    /// Fails if the result would be less than [`Time::MIN`].
    pub fn try_sub(self, t: Time) -> Result<Self, OutOfRange> {
        let n = self.0.checked_sub(t.0).ok_or(OutOfRange(()))?;
        Ok(Self(n))
    }

    /// Add the given number of nanoseconds.
    ///
    /// # Panics
    ///
    /// If the result would be greater than [`Time::MAX`]. See
    /// [`Time::add_nanos_checked`] for an alternative that does
    /// not panic.
    pub fn add_nanos(self, n: u64) -> Self {
        self.add_nanos_checked(n).expect("no overflow")
    }

    /// Add the given number of seconds.
    ///
    /// # Panics
    ///
    /// If the result would be greater than [`Time::MAX`]. See
    /// [`Time::add_seconds_checked`] for an alternative that does
    /// not panic.
    pub fn add_seconds(self, s: u64) -> Self {
        self.add_seconds_checked(s).expect("no overflow")
    }

    /// Add the given number of minutes.
    ///
    /// # Panics
    ///
    /// If the result would be greater than [`Time::MAX`]. See
    /// [`Time::add_minutes_checked`] for an alternative that does
    /// not panic.
    pub fn add_minutes(self, m: u64) -> Self {
        self.add_minutes_checked(m).expect("no overflow")
    }

    /// Add the given number of hours.
    ///
    /// # Panics
    ///
    /// If the result would be greater than [`Time::MAX`]. See
    /// [`Time::add_hours_checked`] for an alternative that does
    /// not panic.
    pub fn add_hours(self, h: u64) -> Self {
        self.add_hours_checked(h).expect("no overflow")
    }

    /// Add the given number of days.
    ///
    /// # Panics
    ///
    /// If the result would be greater than [`Time::MAX`]. See
    /// [`Time::add_days_checked`] for an alternative that does
    /// not panic.
    pub fn add_days(self, d: u64) -> Self {
        self.add_days_checked(d).expect("no overflow")
    }

    /// Add the given number of nanoseconds.
    ///
    /// Fails if the result would be greater than [`Time::MAX`].
    pub fn add_nanos_checked(self, n: u64) -> Result<Self, OutOfRange> {
        let n = self.0.checked_add(n).ok_or(OutOfRange::new())?;
        Ok(Self(n))
    }

    /// Add the given number of seconds.
    ///
    /// Fails if the result would be greater than [`Time::MAX`].
    pub fn add_seconds_checked(self, s: u64) -> Result<Self, OutOfRange> {
        self.add_nanos_checked(s.checked_mul(NANO).ok_or(OutOfRange::new())?)
    }

    /// Add the given number of minutes.
    ///
    /// Fails if the result would be greater than [`Time::MAX`].
    pub fn add_minutes_checked(self, m: u64) -> Result<Self, OutOfRange> {
        self.add_seconds_checked(m.checked_mul(60).ok_or(OutOfRange::new())?)
    }

    /// Add the given number of hours.
    ///
    /// Fails if the result would be greater than [`Time::MAX`].
    pub fn add_hours_checked(self, h: u64) -> Result<Self, OutOfRange> {
        self.add_seconds_checked(h.checked_mul(3600).ok_or(OutOfRange::new())?)
    }

    /// Add the given number of days.
    ///
    /// Fails if the result would be greater than [`Time::MAX`].
    pub fn add_days_checked(self, d: u64) -> Result<Self, OutOfRange> {
        self.add_seconds_checked(d.checked_mul(24 * 3600).ok_or(OutOfRange::new())?)
    }

    /// Substract the given number of nanoseconds.
    ///
    /// # Panics
    ///
    /// If the result would be less than [`Time::MIN`]. See
    /// [`Time::sub_nanos_checked`] for an alternative that does
    /// not panic.
    pub fn sub_nanos(self, n: u64) -> Self {
        self.sub_nanos_checked(n).expect("no underflow")
    }

    /// Substract the given number of seconds.
    ///
    /// # Panics
    ///
    /// If the result would be less than [`Time::MIN`]. See
    /// [`Time::sub_seconds_checked`] for an alternative that does
    /// not panic.
    pub fn sub_seconds(self, s: u64) -> Self {
        self.sub_seconds_checked(s).expect("no underflow")
    }

    /// Substract the given number of minutes.
    ///
    /// # Panics
    ///
    /// If the result would be less than [`Time::MIN`]. See
    /// [`Time::sub_minutes_checked`] for an alternative that does
    /// not panic.
    pub fn sub_minutes(self, m: u64) -> Self {
        self.sub_minutes_checked(m).expect("no underflow")
    }

    /// Substract the given number of hours.
    ///
    /// # Panics
    ///
    /// If the result would be less than [`Time::MIN`]. See
    /// [`Time::sub_hours_checked`] for an alternative that does
    /// not panic.
    pub fn sub_hours(self, h: u64) -> Self {
        self.sub_hours_checked(h).expect("no underflow")
    }

    /// Substract the given number of days.
    ///
    /// # Panics
    ///
    /// If the result would be less than [`Time::MIN`]. See
    /// [`Time::sub_days_checked`] for an alternative that does
    /// not panic.
    pub fn sub_days(self, d: u64) -> Self {
        self.sub_days_checked(d).expect("no underflow")
    }

    /// Substract the given number of nanoseconds.
    ///
    /// Fails if the result would be less than [`Time::MIN`].
    pub fn sub_nanos_checked(self, n: u64) -> Result<Self, OutOfRange> {
        let n = self.0.checked_sub(n).ok_or(OutOfRange::new())?;
        Ok(Self(n))
    }

    /// Substract the given number of seconds.
    ///
    /// Fails if the result would be less than [`Time::MIN`].
    pub fn sub_seconds_checked(self, s: u64) -> Result<Self, OutOfRange> {
        self.sub_nanos_checked(s.checked_mul(NANO).ok_or(OutOfRange::new())?)
    }

    /// Substract the given number of minutes.
    ///
    /// Fails if the result would be less than [`Time::MIN`].
    pub fn sub_minutes_checked(self, m: u64) -> Result<Self, OutOfRange> {
        self.sub_seconds_checked(m.checked_mul(60).ok_or(OutOfRange::new())?)
    }

    /// Substract the given number of hours.
    ///
    /// Fails if the result would be less than [`Time::MIN`].
    pub fn sub_hours_checked(self, h: u64) -> Result<Self, OutOfRange> {
        self.sub_seconds_checked(h.checked_mul(3600).ok_or(OutOfRange::new())?)
    }

    /// Substract the given number of days.
    ///
    /// Fails if the result would be less than [`Time::MIN`].
    pub fn sub_days_checked(self, d: u64) -> Result<Self, OutOfRange> {
        self.sub_seconds_checked(d.checked_mul(24 * 3600).ok_or(OutOfRange::new())?)
    }

    /// Convert this time value to the [`std::time::Duration`] since the Unix epoch.
    pub const fn to_duration(self) -> Duration {
        let s = self.seconds();
        let n = self.second_nanos();
        Duration::new(s, n as u32)
    }

    /// Convert the delta between this time and the given one into a [`std::time::Duration`].
    ///
    /// Returns `None` if the argument is greater that `self`.
    pub fn duration_since(self, earlier: Self) -> Option<Duration> {
        self.to_duration().checked_sub(earlier.to_duration())
    }

    /// Return this time value as a plain integer.
    pub fn as_u64(self) -> u64 {
        self.0
    }

    /// Format this time value as `YYYY-MM-DDThh:mm:ss.nnnnnnnnnZ`.
    ///
    /// *Requires feature `"utc"`*.
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
            .ok_or(OutOfRange::new())?;
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

impl OutOfRange {
    fn new() -> Self {
        Self(())
    }
}

impl fmt::Display for OutOfRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("out of range")
    }
}

impl std::error::Error for OutOfRange {}

impl Add<Duration> for Time {
    type Output = Self;

    /// Adds the given duration.
    ///
    /// # Panics
    ///
    /// If the result would be greater than [`Time::MAX`].
    fn add(self, d: Duration) -> Self::Output {
        self.add_seconds(d.as_secs())
            .add_nanos(d.subsec_nanos().into())
    }
}

impl Add<Time> for Time {
    type Output = Self;

    /// Adds the given time.
    ///
    /// # Panics
    ///
    /// If the result would be greater than [`Time::MAX`].
    fn add(self, t: Time) -> Self::Output {
        self.add_nanos(t.nanos())
    }
}

impl Sub<Duration> for Time {
    type Output = Self;

    /// Subtracts the given duration.
    ///
    /// # Panics
    ///
    /// If the result would be less than [`Time::MIN`].
    fn sub(self, d: Duration) -> Self::Output {
        self.sub_seconds(d.as_secs())
            .sub_nanos(d.subsec_nanos().into())
    }
}

impl Sub<Time> for Time {
    type Output = Self;

    /// Subtracts the given time.
    ///
    /// # Panics
    ///
    /// If the result would be less than [`Time::MIN`].
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
            let Ok(u) = t.add_nanos_checked(n) else {
                return TestResult::discard()
            };
            TestResult::from_bool(u.sub_nanos(n) == t)
        }

        fn prop_add_sub_secs_id(t: Time, s: u64) -> TestResult {
            let Ok(u) = t.add_seconds_checked(s) else {
                return TestResult::discard()
            };
            TestResult::from_bool(u.sub_seconds(s) == t)
        }

        fn prop_add_sub_mins_id(t: Time, m: u64) -> TestResult {
            let Ok(u) = t.add_minutes_checked(m) else {
                return TestResult::discard()
            };
            TestResult::from_bool(u.sub_minutes(m) == t)
        }

        fn prop_add_sub_hours_id(t: Time, h: u64) -> TestResult {
            let Ok(u) = t.add_hours_checked(h) else {
                return TestResult::discard()
            };
            TestResult::from_bool(u.sub_hours(h) == t)
        }

        fn prop_add_sub_days_id(t: Time, d: u64) -> TestResult {
            let Ok(u) = t.add_days_checked(d) else {
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
        assert!(Time::MAX.add_nanos_checked(1).is_err());
        assert!(Time::MAX.add_seconds_checked(1).is_err());
        assert!(Time::MAX.add_minutes_checked(1).is_err());
        assert!(Time::MAX.add_hours_checked(1).is_err());
        assert!(Time::MAX.add_days_checked(1).is_err());
    }

    #[test]
    fn min_time() {
        assert!(Time::MIN.sub_nanos_checked(1).is_err());
        assert!(Time::MIN.sub_seconds_checked(1).is_err());
        assert!(Time::MIN.sub_minutes_checked(1).is_err());
        assert!(Time::MIN.sub_hours_checked(1).is_err());
        assert!(Time::MIN.sub_days_checked(1).is_err());
    }
}
