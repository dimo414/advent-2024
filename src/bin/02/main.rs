use anyhow::*;

fn main() -> Result<()> {
    let input = parse_input(include_str!("input.txt"))?;
    let safety: Vec<_> = input.iter().map(|r| evaluate_safety(r)).collect();
    println!("Safe records: {}", safety.iter().filter(|&&s| s == 0).count());
    println!("Dampened records: {}", safety.iter().filter(|&&s| s <= 1).count());

    Ok(())
}

fn parse_input(input: &str) -> Result<Vec<Vec<i32>>> {
    input.lines().map(|l|
        l.split_whitespace().map(|n| n.parse().with_context(|| format!("{}", n))).collect()
    ).collect()
}

fn get_deltas(values: &[i32]) -> Vec<i32> {
    values.windows(2).map(|w| w[1] - w[0]).collect()
}

fn safe_deltas(deltas: &[i32]) -> bool {
    if deltas.is_empty() {
        return true; // unspecified
    }
    // all same sign, all between [1..3]
    deltas.iter().find(|&&d| d.signum() != deltas[0].signum()).is_none() &&
        deltas.iter().find(|&&d| d.abs() < 1 || d.abs() > 3).is_none()
}

// An O(n) solution is described here:
// https://old.reddit.com/r/adventofcode/comments/1h57o7r/2024_day2_part_2_what_is_the_more_efficient_way/m0407wd/
fn evaluate_safety(report: &[i32]) -> usize {
    let deltas = get_deltas(report);
    if safe_deltas(&deltas) { return 0; }
    // check first and last elements first, since we can do those without allocating new vecs
    if safe_deltas(&deltas[1..]) || safe_deltas(&deltas[..deltas.len()-1]) { return 1; }

    for i in 1..report.len()-1 {
        let removed = [&report[..i], &report[i+1..]].concat();
        let deltas = get_deltas(&removed);
        if safe_deltas(&deltas) { return 1; }
    }

    return 100 // arbitrary value
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_input() { parse_input(include_str!("input.txt")).unwrap(); }

    #[test]
    fn delta() {
        assert_eq!(get_deltas(&[7, 6, 4, 2, 1]), [-1, -2, -2, -1]);
    }

    #[test]
    fn example() {
        let records = parse_input(include_str!("example.txt")).unwrap();
        let safety: Vec<_> = records.iter().map(|r| evaluate_safety(r)).collect();
        assert_eq!(safety, [0, 100, 100, 1, 1, 0]);
    }
}
