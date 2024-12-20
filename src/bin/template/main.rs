// FIXME delete this
// https://github.com/rust-lang/cargo/issues/3591#issuecomment-475701083
#![ allow( dead_code, unused_imports, unused_macros, unused_variables ) ]

use std::str::FromStr;
use anyhow::*;
use lazy_regex::regex_captures;

use advent_2024::collect::{MoreIntoIterator,MoreItertools};

fn main() -> Result<()> {
    let input = parse_input(include_str!("input.txt"))?;
    input.iter().for_each(|o| println!("{:?}", o));

    Ok(())
}

#[derive(Debug)]
struct Obj {
    str: String,
}

impl FromStr for Obj {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        let (_, str) = regex_captures!(r"Hello (.*)!", s).with_context(|| format!("Invalid: {}", s))?;
        Ok(Obj{ str: str.to_string() })
    }
}

fn parse_input(input: &str) -> Result<Vec<Obj>> {
    input.lines().map(|l| l.parse()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_input() { parse_input(include_str!("input.txt")).unwrap(); }

    parameterized_test::create!{ delete, n, { assert_eq!(n % 2, 0); } }
    delete! {
        me: 2,
    }
}
