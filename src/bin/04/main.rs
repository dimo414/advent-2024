use std::collections::HashMap;
use std::str::FromStr;
use anyhow::*;

use advent_2024::euclid::{Bounds, Point, point, Vector, vector};

fn main() -> Result<()> {
    let input: Wordsearch = include_str!("input.txt").parse()?;
    println!("XMASes: {}", input.find_xmas());
    println!("X-MASes: {}", input.find_x_mas());

    Ok(())
}

#[derive(Debug)]
struct Wordsearch {
    grid: HashMap<Point, char>,
    bounds: Bounds,
}

impl Wordsearch {
    fn get(&self, pos: Point) -> char {
        *self.grid.get(&pos).unwrap_or(&' ')
    }

    fn find_xmas(&self) -> i32 {
        let mut sum = 0;
        for pos in self.bounds.iter() {
            if self.get(pos) == 'X' {
                sum += self.count_xmas(pos);
            }
        }
        sum
    }

    fn count_xmas(&self, pos: Point) -> i32 {
        debug_assert_eq!(self.get(pos), 'X');
        Vector::ORDINAL.iter().filter(|dir| self.is_xmas(pos, **dir)).count() as i32
    }

    fn is_xmas(&self, pos: Point, dir: Vector) -> bool {
        for (i, c) in "XMAS".chars().enumerate() {
            if self.get(pos + (dir * i as i32)) != c {
                return false;
            }
        }
        true
    }

    fn find_x_mas(&self) -> i32 {
        let mut sum = 0;
        for pos in self.bounds.iter() {
            if self.is_x_mas(pos) {
                sum += 1;
            }
        }
        sum
    }

    fn is_x_mas(&self, pos: Point) -> bool {
        if self.get(pos) != 'A' {
            return false;
        }

        let tl = self.get(pos + vector(-1, -1));
        let tr = self.get(pos + vector(1, -1));
        let bl = self.get(pos + vector(-1, 1));
        let br = self.get(pos + vector(1, 1));

        let left_diagonal = (tl == 'M' && br == 'S') || (tl == 'S' && br == 'M');
        let right_diagonal = (tr == 'M' && bl == 'S') || (tr == 'S' && bl == 'M');
        left_diagonal && right_diagonal
    }
}

impl FromStr for Wordsearch {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        let mut grid = HashMap::new();
        for (y, l) in s.lines().enumerate() {
            for (x, c) in l.chars().enumerate() {
                let pos = point(x as i32, y as i32);
                grid.insert(pos, c);
            }
        }

        let bounds = Bounds::from_points(grid.keys()).context("Invalid")?;
        Ok(Wordsearch{ grid, bounds })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_input() { include_str!("input.txt").parse::<Wordsearch>().unwrap(); }

    #[test]
    fn example_xmas() {
        let wordsearch: Wordsearch = include_str!("example.txt").parse().unwrap();
        assert_eq!(wordsearch.find_xmas(), 18);
    }

    #[test]
    fn example_x_mas() {
        let wordsearch: Wordsearch = include_str!("example.txt").parse().unwrap();
        assert_eq!(wordsearch.find_x_mas(), 9);
    }
}
