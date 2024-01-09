use cfg_if::cfg_if;
use std::{sync::{atomic::{AtomicU64, Ordering, AtomicBool}, Arc}, thread::{self, JoinHandle}, time::Duration};
use super::Time;

/// Source of `Time` values which are computed asynchronously.
///
/// A `TimeSource` computes the current time in a fixed, configurable frequency, potentially
/// saving the overhead of system calls but with less resolution.
#[derive(Debug, Clone)]
pub struct TimeSource(Arc<Inner>);

#[derive(Debug)]
struct Inner {
    current: Arc<AtomicU64>,
    stop: Arc<AtomicBool>,
    thread: Option<JoinHandle<()>>
}

impl TimeSource {
    /// Creata a new `TimeSource` which gets the current time ate the given frequency.
    ///
    /// A thread is spawned to asynchronously getting the time.
    pub fn new(f: Duration) -> Self {
        Self(Arc::new(Inner::new(f)))
    }

    /// Get the current time.
    ///
    /// The time resolution is less than or equal to the frequency with which the
    /// time source has been created.
    pub fn get(&self) -> Time {
        self.0.get()
    }
}

impl Inner {
    fn new(f: Duration) -> Self {
        let current1 = Arc::new(AtomicU64::new(Time::now().into()));
        let current2 = current1.clone();

        let stop1 = Arc::new(AtomicBool::new(false));
        let stop2 = stop1.clone();

        let thread = thread::spawn(move || {
            while !stop2.load(Ordering::Acquire) {
                let now = {
                    cfg_if! {
                        if #[cfg(feature = "coarse")] {
                            Time::coarse()
                        } else {
                            Time::now()
                        }
                    }
                };
                current2.fetch_max(now.into(), Ordering::AcqRel);
                thread::sleep(f)
            }
        });

        Self {
            current: current1,
            stop: stop1,
            thread: Some(thread)
        }
    }

    fn get(&self) -> Time {
        Time(self.current.load(Ordering::Acquire))
    }
}

impl Drop for Inner {
    fn drop(&mut self) {
        if let Some(t) = self.thread.take() {
            self.stop.store(true, Ordering::Release);
            let _ = t.join();
        }
    }
}

#[cfg(test)]
mod tests {
    use std::thread;
    use std::time::Duration;
    use super::TimeSource;

    #[test]
    fn smoke() {
        let ts = TimeSource::new(Duration::from_secs(1));
        for _ in 0 .. 10 {
            println!("{:?}", ts.get().to_utc_string());
            thread::sleep(Duration::from_millis(500))
        }
    }
}
