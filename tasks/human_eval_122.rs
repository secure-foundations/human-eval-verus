/*
### ID
HumanEval/122
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

/// Specification for taking the sum of the elements with at most
/// two digits from the first k elements of a sequence
pub open spec fn add_elements_spec(arr: Seq<i32>, k: nat) -> int {
    arr.take(k as int).fold_left(
        0,
        |acc: int, x: i32|
            {
                if -99 <= x <= 99 {
                    acc + x
                } else {
                    acc
                }
            },
    )
}

/// Implementation of add_elements
fn add_elements(arr: Vec<i32>, k: u32) -> (result: i64)
    requires
        1 <= arr.len() <= 100,
        1 <= k <= arr.len(),
    ensures
        result as int == add_elements_spec(arr@, k as nat),
{
    let mut res: i64 = 0;
    for i in 0..k
        invariant
            k <= arr.len(),
            i32::MIN * i <= res,
            res <= i32::MAX * i,
            res == add_elements_spec(arr@, i as nat),
    {
        assert(arr@.take(i as int + 1).drop_last() =~= arr@.take(i as int));
        if -99 <= arr[i as usize] && arr[i as usize] <= 99 {
            res += arr[i as usize] as i64;
        }
    }
    res
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def add_elements(arr, k):
    """
    Given a non-empty array of integers arr and an integer k, return
    the sum of the elements with at most two digits from the first k elements of arr.

    Example:

        Input: arr = [111,21,3,4000,5,6,7,8,9], k = 4
        Output: 24 # sum of 21 + 3

    Constraints:
        1. 1 <= len(arr) <= 100
        2. 1 <= k <= len(arr)
    """

*/

/*
### ENTRY POINT
add_elements
*/

/*
### CANONICAL SOLUTION
    return sum(elem for elem in arr[:k] if len(str(elem)) <= 2)

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([1,-2,-3,41,57,76,87,88,99], 3) == -4
    assert candidate([111,121,3,4000,5,6], 2) == 0
    assert candidate([11,21,3,90,5,6,7,8,9], 4) == 125
    assert candidate([111,21,3,4000,5,6,7,8,9], 4) == 24, "This prints if this assert fails 1 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate([1], 1) == 1, "This prints if this assert fails 2 (also good for debugging!)"


*/
