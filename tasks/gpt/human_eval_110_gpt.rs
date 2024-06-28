/// In this problem, you will implement a function that takes two lists of numbers,
/// and determines whether it is possible to perform an exchange of elements
/// between them to make lst1 a list of only even numbers.
/// There is no limit on the number of exchanged elements between lst1 and lst2.
/// If it is possible to exchange elements between the lst1 and lst2 to make
/// all the elements of lst1 to be even, return "YES".
/// Otherwise, return "NO".
/// For example:
/// exchange([1, 2, 3, 4], [1, 2, 3, 4]) => "YES"
/// exchange([1, 2, 3, 4], [1, 5, 3, 4]) => "NO"
/// It is assumed that the input lists will be non-empty.

use vstd::prelude::*;
fn main() {}

verus!{
fn exchange(lst1: &mut Vec<i32>, lst2: &mut Vec<i32>) -> (ret: bool) {
    
    let mut odd_in_lst1 = 0;
    let mut i = 0;
    while i < lst1.len() {
        // Check if the number is odd using bitwise AND operation
        if (lst1[i] & 1) != 0 {
            odd_in_lst1 += 1;
        }
        i += 1;
    }

    let mut even_in_lst2 = 0;
    let mut j = 0;
    while j < lst2.len() {
        // Check if the number is even using bitwise AND operation
        if (lst2[j] & 1) == 0 {
            even_in_lst2 += 1;
        }
        j += 1;
    }

    odd_in_lst1 <= even_in_lst2
}
}
