/*
### ID
HumanEval/45
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn triangle_area(a: u64, h: u64) -> (area: u64)
    requires
        a > 0,  // side length must be positive
        h > 0,  // height must be positive
        a * h / 2 <= u64::MAX  // area must not overflow `u64`
        ,
    ensures
        area == a * h / 2,  // area of a triangle is 1/2 * base * height
{
    // We can't just write `a * h / 2` because the multiplication of
    // `a * h` might overflow. Instead, we do the division `a / 2`
    // before multiplying by `h`. This requires us to deal with the
    // possibility of a remainder during that division. Note that some
    // parentheses below aren't necessary, but are included to make
    // the code more readable.
    if a % 2 == 0 {
        assert(a % 2 == 0 ==> (a / 2) * h == a * h / 2) by (nonlinear_arith);
        (a / 2) * h
    } else {
        assert(a % 2 == 1 ==> (a / 2) * h + (h / 2) == a * h / 2) by (nonlinear_arith);
        (a / 2) * h + (h / 2)
    }
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def triangle_area(a, h):
    """Given length of a side and high return area for a triangle.
    >>> triangle_area(5, 3)
    7.5
    """

*/

/*
### ENTRY POINT
triangle_area
*/

/*
### CANONICAL SOLUTION
    return a * h / 2.0

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate(5, 3) == 7.5
    assert candidate(2, 2) == 2.0
    assert candidate(10, 8) == 40.0


*/
