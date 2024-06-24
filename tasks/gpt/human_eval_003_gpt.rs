/// You're given a list of deposit and withdrawal operations on a bank account that starts with
/// zero balance. Your task is to detect if at any point the balance of account falls below zero, and
/// at that point function should return true. Otherwise it should return false.
///
/// # Examples
///
/// ```
/// # fn main() {
/// assert_eq!(below_zero(&[1, 2, 3]), false);
/// assert_eq!(below_zero(&[1, 2, -4, 5]), true);
/// # }
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn below_zero(operations: Vec<i32>) -> (result: bool) {
    
    let mut balance = 0;
    let mut i = 0;
    while i < operations.len() {
        balance += operations[i];
        if balance < 0 {
            return true;
        }
        i += 1;
    }
    false
}
}
