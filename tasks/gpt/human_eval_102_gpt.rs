/// This function takes two positive numbers x and y and returns the
/// biggest even integer number that is in the range [x, y] inclusive. If 
/// there's no such number, then the function should return -1.
///
/// For example:
/// choose_num(12, 15) = 14
/// choose_num(13, 12) = -1

use vstd::prelude::*;
fn main() {}

verus!{
fn choose_num(x: u32, y: u32) -> (ret: i32) {
    
    if x > y {
        return -1;
    }
    let mut i = y;
    while i >= x {
        if i % 2 == 0 {
            return i as i32;
        }
        if i == x {
            // Prevent underflow when i reaches 0
            break;
        }
        i -= 1;
    }
    -1
}
}
