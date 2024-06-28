/// Add two numbers x and y
/// 
/// # Examples
/// 
/// ```
/// assert_eq!(add(2, 3), 5);
/// assert_eq!(add(5, 7), 12);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn add(x: i32, y: i32) -> (ret: i32) {
    
    x + y
}
}
