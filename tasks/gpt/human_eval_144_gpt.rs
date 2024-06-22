/// Your task is to implement a function that will simplify the expression
/// x * n. The function returns `true` if x * n evaluates to a whole number and `false`
/// otherwise. Both `x` and `n`, are string representation of a fraction, and have the following format,
/// `<numerator>/<denominator>` where both numerator and denominator are positive whole numbers.
///
/// You can assume that `x`, and `n` are valid fractions, and do not have zero as denominator.
///
/// # Examples
///
/// ```
/// simplify("1/5", "5/1") == true;
/// simplify("1/6", "2/1") == false;
/// simplify("7/10", "10/2") == false;
/// ```

use vstd::prelude::*;
fn main() {}

verus!{

fn is_whole_number(num: i64, den: i64) -> (result: bool) {
    // Assuming den is not zero and both num and den are positive
    // If den divides num evenly, then num is a multiple of den, which means the division is a whole number
    let mut multiple = den;
    while multiple <= num {
        if multiple == num {
            return true;
        }
        multiple += den;
    }
    false
}

fn simplify(x: (i64, i64), n: (i64, i64)) -> (result: bool) {
    // Simplify the multiplication of the two fractions
    let num = x.0 * n.0;
    let den = x.1 * n.1;

    // Check if the result is a whole number
    is_whole_number(num, den)
}
}
