/*
### ID
HumanEval/43
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn pairs_sum_to_zero(nums: &[i32], target: i32) -> (found: bool)
    requires
        nums.len() >= 2,
        forall|i: int, j: int|
            0 <= i < j < nums.len() ==> nums[i] + nums[j] <= i32::MAX && nums[i] + nums[j]
                >= i32::MIN,
    ensures
        found <==> exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
{
    let mut i = 0;

    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall|u: int, v: int| 0 <= u < v < nums.len() && u < i ==> nums[u] + nums[v] != target,
        decreases nums.len() - i,
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                0 <= i < j <= nums.len(),
                forall|u: int, v: int|
                    0 <= u < v < nums.len() && u < i ==> nums[u] + nums[v] != target,
                forall|u: int| i < u < j ==> nums[i as int] + nums[u] != target,
            decreases nums.len() - j,
        {
            if nums[i] + nums[j] == target {
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def pairs_sum_to_zero(l):
    """
    pairs_sum_to_zero takes a list of integers as an input.
    it returns True if there are two distinct elements in the list that
    sum to zero, and False otherwise.
    >>> pairs_sum_to_zero([1, 3, 5, 0])
    False
    >>> pairs_sum_to_zero([1, 3, -2, 1])
    False
    >>> pairs_sum_to_zero([1, 2, 3, 7])
    False
    >>> pairs_sum_to_zero([2, 4, -5, 3, 5, 7])
    True
    >>> pairs_sum_to_zero([1])
    False
    """

*/

/*
### ENTRY POINT
pairs_sum_to_zero
*/

/*
### CANONICAL SOLUTION
    for i, l1 in enumerate(l):
        for j in range(i + 1, len(l)):
            if l1 + l[j] == 0:
                return True
    return False

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate([1, 3, 5, 0]) == False
    assert candidate([1, 3, -2, 1]) == False
    assert candidate([1, 2, 3, 7]) == False
    assert candidate([2, 4, -5, 3, 5, 7]) == True
    assert candidate([1]) == False

    assert candidate([-3, 9, -1, 3, 2, 30]) == True
    assert candidate([-3, 9, -1, 3, 2, 31]) == True
    assert candidate([-3, 9, -1, 4, 2, 30]) == False
    assert candidate([-3, 9, -1, 4, 2, 31]) == False


*/
