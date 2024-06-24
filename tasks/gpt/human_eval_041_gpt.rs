/// Imagine a road that's a perfectly straight infinitely long line.
/// n cars are driving left to right; simultaneously, a different set of n cars
/// are driving right to left. The two sets of cars start out being very far from each other.
/// All cars move in the same speed. Two cars are said to collide
/// when a car that's moving left to right hits a car that's moving right to left.
/// However, the cars are infinitely sturdy and strong; as a result, they continue moving
/// in their trajectory as if they did not collide.
///
/// This function outputs the number of such collisions.

use vstd::prelude::*;
fn main() {}

verus!{
fn car_race_collision(n: i32) -> (result: i32)
{
    // Since all cars have the same speed and start far from each other,
    // each car going left to right will eventually collide with each car
    // going right to left. Therefore, the total number of collisions is n^2.
    n * n
}
}
