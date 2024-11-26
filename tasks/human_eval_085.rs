/*
### ID
HumanEval/85
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

/// Returns x if x is odd, else returns 0.
pub open spec fn odd_or_zero(x: u32) -> u32
{
    if x % 2 == 0 { x } else { 0 }
}

/// Sum of all even elements at odd indices in the list.
pub open spec fn add_odd_evens(lst: Seq<u32>) -> int
    decreases lst.len()
{
    if (lst.len() < 2) {
        0
    } else {
        odd_or_zero(lst[1]) + add_odd_evens(lst.skip(2))
    }
}

/// Implementation:
/// Needed to change from (signed) integer to unsigned integer: Verus doesn't yet support % for signed integers.
/// Original definition is underspecified when list has no applicable elements: assume that the desired return value is 0 for lists with no even integers at odd indices.
fn add(lst: Vec<u32>) -> (sum: u64)
    requires 
        0 < lst.len() < u32::MAX
    ensures
        sum == add_odd_evens(lst@)
{
    let mut sum: u64 = 0;
    let mut i = 1;
    proof {
        assert(lst@ =~= lst@.skip(0));
    }
    while (i < lst.len())
        invariant
            1 <= i <= lst.len() + 1,
            0 < lst.len() < u32::MAX,
            sum <= (u32::MAX) * i,
            sum == add_odd_evens(lst@) - add_odd_evens(lst@.skip(i - 1 as int)),
    {
        if (lst[i] % 2 == 0) {
            sum += lst[i] as u64;
        }
        proof {
            // proves: add_odd_evens(lst@.skip(i - 1)) == odd_or_zero(lst[i]) + add_odd_evens(lst@.skip(i + 1))
            assert(lst@.skip(i - 1 as int).skip(2) =~= lst@.skip(i + 1 as int));
        }
        i += 2;
    }
    return sum;
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def add(lst):
    """Given a non-empty list of integers lst. add the even elements that are at odd indices..


    Examples:
        add([4, 2, 6, 7]) ==> 2
    """

*/

/*
### ENTRY POINT
add
*/

/*
### CANONICAL SOLUTION
    return sum([lst[i] for i in range(1, len(lst), 2) if lst[i]%2 == 0])

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([4, 88]) == 88
    assert candidate([4, 5, 6, 7, 2, 122]) == 122
    assert candidate([4, 0, 6, 7]) == 0
    assert candidate([4, 4, 6, 8]) == 12

    # Check some edge cases that are easy to work out by hand.


*/
