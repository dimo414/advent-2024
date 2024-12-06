use std::collections::{HashMap, HashSet};
use std::str::FromStr;
use anyhow::*;
use itertools::Itertools;
use lazy_regex::regex_captures;

fn main() -> Result<()> {
    let (ordering, updates) = parse_input(include_str!("input.txt"))?;
    let (valid, mut invalid) = ordering.partition_valid(updates);
    println!("Valid pages sum: {}", middle_pages(&valid).iter().sum::<i32>());

    ordering.sort_all(&mut invalid);
    println!("Invalid pages sum: {}", middle_pages(&invalid).iter().sum::<i32>());

    Ok(())
}

#[derive(Debug)]
struct Ordering {
    comes_after: HashMap<i32, HashSet<i32>>,
}

impl Ordering {
    fn validate(&self, update: &[i32]) -> bool {
        let mut banned = HashSet::new();
        for page in update {
            if banned.contains(page) {
                return false;
            }
            if let Some(predecessors) = self.comes_after.get(page) {
                banned.extend(predecessors.iter().cloned());
            }
        }
        true
    }

    fn partition_valid(&self, updates: Vec<Vec<i32>>) -> (Vec<Vec<i32>>, Vec<Vec<i32>>) {
        updates.into_iter().partition(|u| self.validate(u))
    }

    fn sort(&self, update: &mut Vec<i32>) {
        let comes_after = |x,y| self.comes_after.get(&x).map(|pred| pred.contains(&y)).unwrap_or(false);
        let ordering = |x,y| {
            if comes_after(x, y) {
                return std::cmp::Ordering::Greater;
            }
            if comes_after(y, x) {
                return std::cmp::Ordering::Less;
            }
            // Returning Equal should work here, but it seems to not be needed
            // std::cmp::Ordering::Equal
            panic!("Unsupported, all pages are expected to be ordered")
        };

        update.sort_unstable_by(|&x, &y| ordering(x, y));
        debug_assert!(self.validate(&update));
    }

    fn sort_all(&self, updates: &mut Vec<Vec<i32>>) {
        for mut update in updates {
            self.sort(&mut update);
        }
    }
}

fn middle_pages(updates: &[Vec<i32>]) -> Vec<i32> {
    updates.iter().map(|u| u[u.len()/2]).collect()
}

impl FromStr for Ordering {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        let mut comes_after = HashMap::new();
        for line in s.lines() {
            let (_, before, after) = regex_captures!(r"(\d+)\|(\d+)", line).with_context(|| format!("Invalid: {}", line))?;
            let before = before.parse()?;
            let after = after.parse()?;
            comes_after.entry(after).or_insert_with(HashSet::new).insert(before);
        }
        Ok(Ordering{ comes_after })
    }
}

fn parse_input(input: &str) -> Result<(Ordering, Vec<Vec<i32>>)> {
    let parts = input.split("\n\n").collect_vec();
    ensure!(parts.len() == 2);
    let ordering: Ordering = parts[0].parse()?;

    let updates = parts[1].lines().map(|line|
        line.split(",").map(|n| n.parse::<i32>().with_context(|| format!("{}", n))).collect()
    ).collect::<Result<Vec<_>>>()?;

    Ok((ordering, updates))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_input() { parse_input(include_str!("input.txt")).unwrap(); }

    #[test]
    fn example() {
        let (ordering, updates) = parse_input(include_str!("example.txt")).unwrap();

        assert_eq!(updates.len(), 6);

        assert!(ordering.validate(&updates[0]));
        assert!(ordering.validate(&updates[1]));
        assert!(ordering.validate(&updates[2]));
        assert!(!ordering.validate(&updates[3]));
        assert!(!ordering.validate(&updates[4]));
        assert!(!ordering.validate(&updates[5]));

        let (valid, mut invalid) = ordering.partition_valid(updates);

        assert_eq!(middle_pages(&valid), [61, 53, 29]);

        ordering.sort_all(&mut invalid);
        assert_eq!(invalid[0], [97,75,47,61,53]);
        assert_eq!(invalid[1], [61,29,13]);
        assert_eq!(invalid[2], [97,75,47,29,13]);

        assert_eq!(middle_pages(&invalid), [47, 29, 47]);
    }
}
