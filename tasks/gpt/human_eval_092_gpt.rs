/// Create a function that takes 3 numbers.
/// Returns true if one of the numbers is equal to the sum of the other two, and all numbers are integers.
/// Returns false in any other cases.
///
/// # Examples
///
/// ```
/// assert_eq!(any_int(5, 2, 7), true);
///
/// assert_eq!(any_int(3, 2, 2), false);
///
/// assert_eq!(any_int(3, -2, 1), true);
///
/// assert_eq!(any_int(3.6, -2.2, 2), false); // This example will not compile in Rust as the function signature will only accept integers
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn any_int(x: i32, y: i32, z: i32) -> (result: bool) {
    
    x == y + z || y == x + z || z == x + y
}
}
