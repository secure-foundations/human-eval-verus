/// Return True is list elements are monotonically increasing or decreasing.

use vstd::prelude::*;
fn main() {}

verus!{
fn monotonic(l: Vec<i32>) -> (result: bool) {
    
    if l.len() == 0 || l.len() == 1 {
        return true;
    }

    let mut increasing = false;
    let mut decreasing = false;

    let mut i = 0;
    while i < l.len() - 1 {
        if l[i] < l[i + 1] {
            increasing = true;
        } else if l[i] > l[i + 1] {
            decreasing = true;
        }

        if increasing && decreasing {
            return false;
        }
        i += 1;
    }

    true
}
}
