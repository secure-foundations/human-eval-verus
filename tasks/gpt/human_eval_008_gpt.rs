/// For a given list of integers, return a tuple consisting of a sum and a product of all the integers in a list.
/// Empty sum should be equal to 0 and empty product should be equal to 1.
///
/// # Examples
///
/// ```
/// # use your_crate_name::sum_product;
/// assert_eq!(sum_product(&[]), (0, 1));
/// assert_eq!(sum_product(&[1, 2, 3, 4]), (10, 24));
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
struct SumProduct {
    sum: i32,
    product: i32,
}

fn sum_product(numbers: Vec<i32>) -> (ret: SumProduct) {
    let mut sum = 0;
    let mut product = 1;
    let mut i = 0;

    while i < numbers.len() {
        sum += numbers[i];
        product *= numbers[i];
        i += 1;
    }

    SumProduct { sum, product }
}
}
