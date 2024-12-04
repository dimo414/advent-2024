use std::collections::HashMap;
use anyhow::*;
use itertools::Itertools;
use num::abs;

fn main() -> Result<()> {
    let (left, right) = parse_input(include_str!("input.txt"))?;
    let deltas = deltas(&left, &right);
    println!("Delta sum: {}", deltas.iter().sum::<i32>());
    println!("Similarity score: {}", freq_score(&left, &right));

    Ok(())
}

fn parse_input(input: &str) -> Result<(Vec<i32>, Vec<i32>)> {
    fn parse_line(line: &str) -> Result<(i32, i32)> {
        let mut split = line.split_whitespace();
        let left = split.next().with_context(|| format!("Invalid: {}", line))?;
        let right = split.next().with_context(|| format!("Invalid: {}", line))?;
        ensure!(split.next().is_none(), "Invalid: {}", line);
        Ok((left.parse()?, right.parse()?))
    }

    Ok(input.lines().map(parse_line).collect::<Result<Vec<_>>>()?.into_iter().unzip())
}

fn deltas(left: &[i32], right: &[i32]) -> Vec<i32> {
    left.iter().sorted().zip(right.iter().sorted()).map(|(l, r)| abs(l-r)).collect()
}

fn freq(v: &[i32]) -> HashMap<i32, i32> {
    let mut map = HashMap::new();
    for e in v {
        *map.entry(*e).or_insert(0) += 1;
    }
    map
}

fn freq_score(left: &[i32], right: &[i32]) -> i32 {
    let freq = freq(right);
    left.iter().map(|&e| e * freq.get(&e).unwrap_or(&0)).sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_input() { parse_input(include_str!("input.txt")).unwrap(); }

    #[test]
    fn parsing() {
        let (left, right) = parse_input(include_str!("example.txt")).unwrap();
        assert_eq!(left, [3,4,2,1,3,3]);
        assert_eq!(right, [4,3,5,3,9,3]);
    }

    #[test]
    fn delta() {
        assert_eq!(deltas(&[3,4,2,1,3,3], &[4,3,5,3,9,3]), [2, 1, 0, 1, 2, 5]);
    }

    #[test]
    fn score() {
        assert_eq!(freq_score(&[3,4,2,1,3,3], &[4,3,5,3,9,3]), 31);
    }
}
