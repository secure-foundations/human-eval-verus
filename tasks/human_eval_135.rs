/*
### ID
HumanEval/135
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn can_arrange(arr: &Vec<i32>) -> (pos: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j],
        arr.len() + 1 < i32::MAX,
    ensures
        pos == -1 ==> forall|i: int| #![trigger arr[i]] 1 <= i < arr.len() ==> arr[i] >= arr[i - 1],
        pos >= 0 ==> 1 <= pos < arr.len() && arr[pos as int] < arr[pos - 1],
        pos >= 0 ==> forall|i: int| #![trigger arr[i]] pos < i < arr.len() ==> arr[i] >= arr[i - 1],
{
    if arr.len() == 0 {
        return -1;
    }
    let mut pos = -1;
    for i in 1..arr.len()
        invariant
            pos == -1 ==> forall|j: int| #![trigger arr[j]] 1 <= j < i ==> arr[j] >= arr[j - 1],
            pos >= 0 ==> 1 <= pos < i && arr[pos as int] < arr[pos - 1],
            pos >= 0 ==> forall|j: int| #![trigger arr[j]] pos < j < i ==> arr[j] >= arr[j - 1],
    {
        if arr[i] < arr[i - 1] {
            pos = i as i32;
        }
    }
    pos
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def can_arrange(arr):
    """Create a function which returns the largest index of an element which
    is not greater than or equal to the element immediately preceding it. If
    no such element exists then return -1. The given array will not contain
    duplicate values.

    Examples:
    can_arrange([1,2,4,3,5]) = 3
    can_arrange([1,2,3]) = -1
    """

*/

/*
### ENTRY POINT
can_arrange
*/

/*
### CANONICAL SOLUTION
    ind=-1
    i=1
    while i<len(arr):
      if arr[i]<arr[i-1]:
        ind=i
      i+=1
    return ind

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([1,2,4,3,5])==3
    assert candidate([1,2,4,5])==-1
    assert candidate([1,4,2,5,6,7,8,9,10])==2
    assert candidate([4,8,5,7,3])==4

    # Check some edge cases that are easy to work out by hand.
    assert candidate([])==-1


*/
