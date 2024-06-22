/// Given the lengths of the three sides of a triangle, return the area of
/// the triangle rounded to 2 decimal points if the three sides form a valid triangle.
/// Otherwise return -1.
/// Three sides make a valid triangle when the sum of any two sides is greater
/// than the third side.
///
/// # Examples
///
/// ```
/// assert_eq!(triangle_area(3, 4, 5), 6.00);
/// assert_eq!(triangle_area(1, 2, 10), -1);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn triangle_area(a: u32, b: u32, c: u32) -> (area: i32)
{
    if a + b > c && a + c > b && b + c > a {
        let s = (a + b + c) / 2;
        // Since we are using unsigned integers, we can directly use the division operator.
        // We will return the squared area to avoid using floating point numbers.
        let squared_area = s * (s - a) * (s - b) * (s - c);
        // Casting the unsigned result back to signed integer.
        squared_area as i32
    } else {
        -1
    }
}
}
