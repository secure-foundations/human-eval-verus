/// Given a positive integer n, you have to make a pile of n levels of stones.
/// The first level has n stones.
/// The number of stones in the next level is:
///     - the next odd number if n is odd.
///     - the next even number if n is even.
/// Return the number of stones in each level in a Vec<u32>, where element at index
/// i represents the number of stones in the level (i+1).
///
/// # Examples
///
/// ```
/// let stones = make_a_pile(3);
/// assert_eq!(stones, vec![3, 5, 7]);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn make_a_pile(n: u32) -> (stones: Vec<u32>) {
    
    let mut stones = Vec::new();
    let mut current_stones = n;
    let mut i = 0;
    while i < n {
        stones.push(current_stones);
        current_stones += 2;
        i += 1;
    }
    stones
}
}
