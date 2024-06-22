/// Given length of a side and height return area for a triangle.

use vstd::prelude::*;
fn main() {}

verus!{
fn triangle_area(a: i32, h: i32) -> (area: i32) {
    // Since direct division of signed integers is not supported, we use bit-shifting to the right by one bit to divide by two.
    let product = a * h;

    product >> 1 // Shift right by one bit to divide by two
}
}
