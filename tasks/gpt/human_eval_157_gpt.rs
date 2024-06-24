/// Given the lengths of the three sides of a triangle. Return true if the three
/// sides form a right-angled triangle, false otherwise.
/// A right-angled triangle is a triangle in which one angle is a right angle or
/// 90 degrees.
///
/// # Examples
///
/// ```
/// assert_eq!(right_angle_triangle(3, 4, 5), true);
/// assert_eq!(right_angle_triangle(1, 2, 3), false);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn right_angle_triangle(a: i32, b: i32, c: i32) -> (result: bool) {
    // Initialize a mutable tuple to hold the sides
    let mut sides = (a, b, c);

    // Manually sort the values in the tuple
    if sides.0 > sides.1 { sides = (sides.1, sides.0, sides.2); }
    if sides.1 > sides.2 { sides = (sides.0, sides.2, sides.1); }
    if sides.0 > sides.1 { sides = (sides.1, sides.0, sides.2); }

    // Check if the triangle is a right-angled triangle
    sides.0 * sides.0 + sides.1 * sides.1 == sides.2 * sides.2
}
}
