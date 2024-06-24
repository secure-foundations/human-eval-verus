/// Create a function that returns a tuple (a, b), where 'a' is
/// the largest of negative integers, and 'b' is the smallest
/// of positive integers in a list.
/// If there is no negative or positive integers, return them as None.
///
/// Examples:
/// largest_smallest_integers(vec![2, 4, 1, 3, 5, 7]) == (None, Some(1))
/// largest_smallest_integers(vec![]) == (None, None)
/// largest_smallest_integers(vec![0]) == (None, None)

use vstd::prelude::*;
fn main() {}

verus!{
fn largest_negative(lst: Vec<i32>) -> (ret: Option<i32>) {
    let mut largest_negative = None;
    let mut i = 0;
    while i < lst.len() {
        let num = lst[i];
        if num < 0 {
            largest_negative = match largest_negative {
                None => Some(num),
                Some(current) => Some(if num > current { num } else { current }),
            };
        }
        i += 1;
    }
    largest_negative
}

fn smallest_positive(lst: Vec<i32>) -> (ret: Option<i32>) {
    let mut smallest_positive = None;
    let mut i = 0;
    while i < lst.len() {
        let num = lst[i];
        if num > 0 {
            smallest_positive = match smallest_positive {
                None => Some(num),
                Some(current) => Some(if num < current { num } else { current }),
            };
        }
        i += 1;
    }
    smallest_positive
}
}
