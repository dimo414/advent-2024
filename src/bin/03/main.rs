use anyhow::*;
use lazy_regex::regex;

fn main() -> Result<()> {
    let input = parse_input(include_str!("input.txt"));
    println!("All muls: {}", all_muls(&input));
    println!("Enabled muls: {}", enabled_muls(&input));

    Ok(())
}

#[derive(Debug)]
enum Op {
    Do,
    Dont,
    Mul(i32, i32),
}

fn parse_input(input: &str) -> Vec<Op> {
    let regex = regex!(r"do\(\)|don't\(\)|mul\((\d{1,3}),(\d{1,3})\)");
    regex.captures_iter(input).map(|caps|
        match caps.get(0).expect("Non-none").as_str() {
            "do()" => Op::Do,
            "don't()" => Op::Dont,
            _ => Op::Mul(caps.get(1).expect("Valid group").as_str().parse::<i32>().expect("Valid number"),
                         caps.get(2).expect("Valid group").as_str().parse::<i32>().expect("Valid number")),
        }
    ).collect()
}

fn all_muls(ops: &[Op]) -> i32 {
    ops.iter().map(|op| match op {
        Op::Mul(x, y) => x * y,
        _ => 0,
    }).sum()
}

fn enabled_muls(ops: &[Op]) -> i32 {
    let mut sum = 0;
    let mut enabled = true;
    for op in ops {
        match op {
            Op::Do => enabled = true,
            Op::Dont => enabled = false,
            Op::Mul(x, y) => if enabled { sum += x * y },
        }
    }
    sum
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_input() { assert!(!parse_input(include_str!("input.txt")).is_empty()); }

    parameterized_test::create!{ example, (s, all, enabled), {
        let ops = parse_input(s);
        assert_eq!(all_muls(&ops), all, "{:?}", ops);
        assert_eq!(enabled_muls(&ops), enabled, "{:?}", ops);
    } }
    example! {
        example1: ("xmul(2,4)%&mul[3,7]!@^do_not_mul(5,5)+mul(32,64]then(mul(11,8)mul(8,5))", 161, 161),
        example2: ("xmul(2,4)&mul[3,7]!^don't()_mul(5,5)+mul(32,64](mul(11,8)undo()?mul(8,5))", 161, 48),
    }
}
