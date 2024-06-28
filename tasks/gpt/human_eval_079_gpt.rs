/// You will be given a number in decimal form and your task is to convert it to
/// binary format. The function should return a string, with each character representing a binary
/// number. Each character in the string will be '0' or '1'.
///
/// There will be an extra couple of characters 'db' at the beginning and at the end of the string.
/// The extra characters are there to help with the format.
///
/// Examples:
/// decimal_to_binary(15)   // returns "db1111db"
/// decimal_to_binary(32)   // returns "db100000db"

use vstd::prelude::*;
fn main() {}

verus!{
fn decimal_to_binary(decimal: u32) -> (binary: u32)
{
    let mut binary = 0;
    let mut n = decimal;
    let mut base = 1;

    while n > 0 {
        let remainder = n % 2;
        binary = binary + remainder * base;
        n = n / 2;
        base = base * 10;
    }
    binary
}
}
