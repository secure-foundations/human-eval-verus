/// This function will take a vector of integers. For all entries in the vector, the function shall square the integer entry if its index is a 
/// multiple of 3 and will cube the integer entry if its index is a multiple of 4 and not a multiple of 3. The function will not 
/// change the entries in the vector whose indexes are not a multiple of 3 or 4. The function shall then return the sum of all entries.
///
/// Examples:
/// For lst = vec![1,2,3] the output should be 6
/// For lst = vec![]  the output should be 0
/// For lst = vec![-1,-5,2,-1,-5]  the output should be -126

use vstd::prelude::*;
fn main() {}

verus!{
fn sum_squares(lst: Vec<i32>) -> (ret:i32)
{
    let mut sum: i32 = 0;
    let mut index: usize = 0;
    while index < lst.len()
    {
        let value: i32 = lst[index];
        if index % 3 == 0 {
            sum += value * value; // equivalent to value.pow(2) but without using pow
        } else if index % 4 == 0 {
            sum += value * value * value; // equivalent to value.pow(3) but without using pow
        } else {
            sum += value;
        }
        index += 1;
    }
    sum
}
}