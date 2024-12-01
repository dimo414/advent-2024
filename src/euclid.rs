// Referenced https://docs.rs/rusttype/0.5.2/src/rusttype/geometry.rs.html
// Other resources:
//   https://crates.io/crates/euclid - https://doc.servo.org/src/euclid/point.rs.html
mod point {
    use super::*;
    use std::fmt;
    use std::ops::{Add,AddAssign,Sub};
    use std::str::FromStr;
    use anyhow::{Context, Error, Result};
    use lazy_regex::regex_captures;

    #[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
    pub struct Point {
        pub x: i32,
        pub y: i32,
    }

    #[inline]
    pub const fn point(x: i32, y: i32) -> Point {
        Point { x, y }
    }

    impl Point {
        pub const ORIGIN: Point = point(0, 0);
    }

    impl Add<&Vector> for Point {
        type Output = Point;

        fn add(self, vec: &Vector) -> Point {
            point(self.x + vec.x, self.y + vec.y)
        }
    }

    impl Add<&Vector> for &Point {
        type Output = Point;

        fn add(self, vec: &Vector) -> Point {
            point(self.x + vec.x, self.y + vec.y)
        }
    }

    impl Add<Vector> for &Point {
        type Output = Point;

        fn add(self, vec: Vector) -> Point {
            point(self.x + vec.x, self.y + vec.y)
        }
    }

    impl Add<Vector> for Point {
        type Output = Point;

        fn add(self, vec: Vector) -> Point {
            point(self.x + vec.x, self.y + vec.y)
        }
    }

    impl AddAssign<Vector> for Point {
        fn add_assign(&mut self, vec: Vector) {
            *self = point(self.x + vec.x, self.y + vec.y);
        }
    }

    impl AddAssign<&Vector> for Point {
        fn add_assign(&mut self, vec: &Vector) {
            *self = point(self.x + vec.x, self.y + vec.y);
        }
    }

    impl Sub for Point {
        type Output = Vector;

        fn sub(self, point: Point) -> Vector { vector(self.x - point.x, self.y - point.y) }
    }

    impl Sub for &Point {
        type Output = Vector;

        fn sub(self, point: &Point) -> Vector { vector(self.x - point.x, self.y - point.y) }
    }

    impl FromStr for Point {
        type Err = Error;

        fn from_str(s: &str) -> Result<Self> {
            // r"^([^,]+),([^,]+)$" would be more strict - worth it?
            let (_, x, y) = regex_captures!(r"^\(?([^(,]+),([^),]+)\)?$", s)
                .with_context(|| format!("Invalid point '{}'", s))?;
            let x: i32 = x.trim().parse()?;
            let y: i32 = y.trim().parse()?;
            Ok(point(x, y))
        }
    }

    impl fmt::Debug for Point {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "({}, {})", self.x, self.y)
        }
    }

    impl fmt::Display for Point {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{:?}", self)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn parse() {
            assert_eq!("3, 4".parse::<Point>().unwrap(), point(3, 4));
            assert_eq!("-3,-4".parse::<Point>().unwrap(), point(-3, -4));
            assert_eq!("(40,30)".parse::<Point>().unwrap(), point(40, 30));
            assert_eq!("(-3, -5)".parse::<Point>().unwrap(), point(-3, -5));

            assert!("abc".parse::<Point>().is_err());
        }

        #[test]
        fn add() {
            assert_eq!(point(1, 0) + super::super::vector(2, 3), point(3, 3));
        }
        #[test]
        fn sub() {
            assert_eq!(point(3, 3) - point(1, 0), super::super::vector(2, 3));
        }
    }
}
pub use self::point::{Point,point};

mod bounds {
    use super::*;

    #[derive(Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
    pub struct Bounds {
        pub min: Point,
        pub max: Point,
    }

    #[inline]
    pub const fn bounds(min: Point, max: Point) -> Bounds {
        assert!(min.x <= max.x);
        assert!(min.y <= max.y);
        Bounds{ min, max }
    }

    impl Bounds {
        pub fn from_points<'a>(points: impl IntoIterator<Item = &'a Point>) -> Option<Bounds> {
            let bound: Option<(Point, Point)> = points.into_iter().fold(None, |r , c|
                match r {
                    Some((min, max)) => {
                        Some((
                            point(std::cmp::min(min.x, c.x), std::cmp::min(min.y, c.y)),
                            point(std::cmp::max(max.x, c.x), std::cmp::max(max.y, c.y))
                        ))
                    },
                    None => Some((*c, *c)),
                }
            );
            bound.map(|(min, max)| bounds(min, max))
        }

        pub fn contains(&self, pos: Point) -> bool {
            self.min.x <= pos.x && self.min.y <= pos.y && self.max.x >= pos.x && self.max.y >= pos.y
        }

        pub fn intersects(&self, other: Bounds) -> bool {
            self.min.x <= other.max.x && self.max.x >= other.min.x && self.min.y <= other.max.y && self.max.y >= other.min.y
        }

        pub fn size(&self) -> Vector { vector(self.max.x - self.min.x + 1, self.max.y - self.min.y + 1) }

        pub fn area(&self) -> i32 { let s = self.size(); s.x * s.y }

        pub fn iter(&self) -> impl Iterator<Item = Point> + '_ {
            self.iter_rows().flatten()
        }

        pub fn iter_rows(&self) -> impl Iterator<Item = impl Iterator<Item = Point> + '_> {
            (self.min.y..=self.max.y).map(move |y| (self.min.x..=self.max.x).map(move |x| point(x, y)))
        }
    }


    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn bounding() {
            let points = vec!(point(1, 2), point(2, 3), point(0, 5));
            assert_eq!(Bounds::from_points(&points), Some(bounds(point(0, 2), point(2, 5))));
        }

        #[test]
        fn in_bounds() {
            let zero_zero = point(0, 0);
            let two_two = point(2, 2);
            let five_six = point(5, 6);
            let bound = bounds(zero_zero, two_two);
            assert!(bound.contains(two_two));
            assert!(!bound.contains(five_six));
        }

        #[test]
        fn intersects() {
            let bounds_a = bounds(point(0, 0), point(3, 3));
            let bounds_b = bounds(point(1, -1), point(4, 2));
            let bounds_c = bounds(point(4, 2), point(5, 3));
            assert!(bounds_a.intersects(bounds_b));
            assert!(bounds_b.intersects(bounds_a));
            assert!(!bounds_a.intersects(bounds_c));
            assert!(!bounds_c.intersects(bounds_a));

            let bounds_m = bounds(point(0, 0), point(2, 0));
            let bounds_n = bounds(point(1, 0), point(1, 2));
            assert!(bounds_m.intersects(bounds_n));
            assert!(bounds_n.intersects(bounds_m));
        }

        #[test]
        fn size_and_area() {
            let bound = bounds(point(-1, -1), point(2, 4));
            assert_eq!(bound.size(), vector(4, 6));
            assert_eq!(bound.area(), 4*6);
        }

        #[test]
        fn display_bounds() {
            let points = vec!(point(1, 2), point(3, 1), point(0, -1));
            let display_points: Vec<Vec<_>> = Bounds::from_points(&points).unwrap().iter_rows()
                .map(|row| row.collect())
                .collect();
            assert_eq!(display_points, vec!(
                vec!(point(0, -1), point(1, -1), point(2, -1), point(3, -1)),
                vec!(point(0, 0), point(1, 0), point(2, 0), point(3, 0)),
                vec!(point(0, 1), point(1, 1), point(2, 1), point(3, 1)),
                vec!(point(0, 2), point(1, 2), point(2, 2), point(3, 2)),
            ));
        }
    }
}
pub use self::bounds::{Bounds,bounds};

mod vector {
    use std::fmt;
    use std::str::FromStr;
    use std::ops::{Add,AddAssign,Mul};
    use anyhow::{Error, Result};

    #[derive(Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
    pub struct Vector {
        pub x: i32,
        pub y: i32,
    }

    #[inline]
    pub const fn vector(x: i32, y: i32) -> Vector {
        Vector { x, y }
    }

    impl Vector {
        pub const ZERO: Vector = vector(0, 0);

        // https://en.wikipedia.org/wiki/Points_of_the_compass
        pub const CARDINAL: &'static [Vector] = &[
            vector(-1, 0), vector(0, -1), vector(1, 0), vector(0, 1)];
        pub const ORDINAL: &'static [Vector] = &[
            vector(-1, 0), vector(-1, -1), vector(0, -1), vector(1, -1),
            vector(1, 0), vector(1, 1), vector(0, 1), vector(-1, 1)];

        pub fn abs(&self) -> Self {
            vector(self.x.abs(), self.y.abs())
        }

        pub fn signum(&self) -> Self {
            debug_assert!(self.x == 0 || self.y == 0 || self.x.abs() == self.y.abs(),
                          "{}.signum() is lossy; use signum_unchecked() if this is acceptable", self);
            self.signum_unchecked()
        }

        pub fn signum_unchecked(&self) -> Self {
            vector(self.x.signum(), self.y.signum())
        }

        pub fn len(&self) -> f64 {
            (self.x as f64).hypot(self.y as f64)
        }

        pub fn grid_len(&self) -> u32 {
            (self.x.abs() + self.y.abs()) as u32
        }

        pub fn left90(&self) -> Self { vector(-self.y, self.x) }

        pub fn right90(&self) -> Self { vector(self.y, -self.x) }
    }

    impl Add<Vector> for Vector {
        type Output = Vector;

        fn add(self, vec: Self) -> Self {
            vector(self.x + vec.x, self.y + vec.y)
        }
    }

    impl Add<&Vector> for Vector {
        type Output = Vector;

        fn add(self, vec: &Self) -> Self {
            vector(self.x + vec.x, self.y + vec.y)
        }
    }

    impl AddAssign<Vector> for Vector {
        fn add_assign(&mut self, vec: Self) {
            *self = vector(self.x + vec.x, self.y + vec.y);
        }
    }

    impl AddAssign<&Vector> for Vector {
        fn add_assign(&mut self, vec: &Self) {
            *self = vector(self.x + vec.x, self.y + vec.y);
        }
    }

    impl Mul<i32> for Vector {
        type Output = Vector;

        fn mul(self, m: i32) -> Self {
            vector(self.x * m, self.y * m)
        }
    }

    impl FromStr for Vector {
        type Err = Error;

        fn from_str(s: &str) -> Result<Self> {
            // Just reuse point's parser
            let p: super::Point = s.parse()?;
            Ok(vector(p.x, p.y))
        }
    }

    impl fmt::Debug for Vector {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "({}, {})", self.x, self.y)
        }
    }

    impl fmt::Display for Vector {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{:?}", self)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::super::point;
        use super::*;
        use assert_approx_eq::assert_approx_eq;

        #[test]
        fn parse() {
            assert_eq!("3, 4".parse::<Vector>().unwrap(), vector(3, 4));
            assert_eq!("-3,-4".parse::<Vector>().unwrap(), vector(-3, -4));
        }

        #[test]
        fn len() {
            assert_approx_eq!(vector(3, -4).len(), 5_f64, f64::EPSILON);
        }

        parameterized_test::create!{ grid_lens, (p1, p2, d), {
            assert_eq!((p1 - p2).grid_len(), d);
            assert_eq!((p2 - p1).grid_len(), d);
        }}
        grid_lens! {
            a: (point(1,1), point(1,1), 0),
            b: (point(1,1), point(1,2), 1),
            c: (point(1,1), point(2,2), 2),
            d: (point(1,1), point(1,5), 4),
            e: (point(1,1), point(8,3), 9),
            f: (point(1,1), point(-1,-1), 4),
        }

        #[test]
        fn turns() {
            let v = vector(2, 1);
            assert_eq!(v.right90(), vector(1, -2));
            assert_eq!(v.left90(), vector(-1, 2));
        }
    }
}
pub use self::vector::{Vector,vector};
