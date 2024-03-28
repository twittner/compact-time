use clap::Parser;
use std::{process::exit, str::FromStr, fmt};
use compact_time::Time;

#[derive(Debug, Parser)]
#[command(author, version, about, long_about = None)]
#[non_exhaustive]
pub struct Args {
    /// Parse a time value string.
    #[arg(short, long)]
    read: Option<String>,

    /// Show the date and time in UTC.
    #[arg(short, long)]
    utc: bool,

    /// Show only the seconds or parse the string as a seconds value.
    #[arg(short, long, conflicts_with = "numeric")]
    seconds: bool,

    /// Show only the pure numeric value.
    #[arg(short, long, conflicts_with_all = ["seconds", "utc"])]
    numeric: bool
}

fn main() {
    let args = Args::parse();

    let time = if let Some(s) = args.read {
        if let Some((s, n)) = s.split_once('.') {
            let secs: u64 = read(s);
            let nano: u64 = read(n);
            let mut time = Time::try_from_seconds(secs);
            if !args.seconds {
                time = time.and_then(|t| t.add_nanos_checked(nano));
            }
            if let Ok(t) = time {
                t
            } else {
                eprintln!("value out of range");
                exit(1)
            }
        } else {
            let num: u64 = read(&s);
            let time = if args.seconds {
                Time::try_from_seconds(num)
            } else {
                Ok(Time::from(num))
            };
            if let Ok(t) = time {
                t
            } else {
                eprintln!("value out of range");
                exit(1)
            }
        }
    } else {
        Time::now()
    };

    if !args.utc {
        if args.seconds {
            println!("{}", time.seconds())
        } else if args.numeric {
            println!("{}", u64::from(time))
        } else {
            println!("{time}")
        }
    } else {
        let s = time.seconds();
        let n = if args.seconds { 0 } else { time.second_nanos() };
        match tz::UtcDateTime::from_timespec(s as i64, n as u32) {
            Ok(utc) => println!("{utc}"),
            Err(e)  => {
                eprintln!("{e}");
                exit(1)
            }
        }
    }
}

fn read<T>(s: &str) -> T
where
    T: FromStr,
    <T as FromStr>::Err: fmt::Display
{
    match s.parse() {
        Ok(x) => x,
        Err(e) => {
            eprintln!("{e}");
            exit(1)
        }
    }
}
