/*
### ID
HumanEval/136
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn largest_smallest_integers(arr: &Vec<i32>) -> (res: (Option<i32>, Option<i32>))
    ensures
        ({
            let a = res.0;
            let b = res.1;
            &&& a.is_none() ==> forall|i: int| 0 <= i < arr@.len() ==> arr@[i] >= 0
            &&& a.is_some() ==> arr@.contains(a.unwrap()) && a.unwrap() < 0
            &&& a.is_some() ==> forall|i: int|
                0 <= i < arr@.len() && arr@[i] < 0 ==> arr@[i] <= a.unwrap()
            &&& b.is_none() ==> forall|i: int| 0 <= i < arr@.len() ==> arr@[i] <= 0
            &&& b.is_some() ==> arr@.contains(b.unwrap()) && b.unwrap() > 0
            &&& b.is_some() ==> forall|i: int|
                0 <= i < arr@.len() && arr@[i] > 0 ==> arr@[i] >= b.unwrap()
        }),
{
    let mut i: usize = 0;
    let mut a = None;
    let mut b = None;

    while i < arr.len()
        invariant
            0 <= i <= arr@.len(),
            a.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] >= 0,
            a.is_some() ==> arr@.contains(a.unwrap()) && a.unwrap() < 0,
            a.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] < 0 ==> arr@[j] <= a.unwrap(),
            b.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] <= 0,
            b.is_some() ==> arr@.contains(b.unwrap()) && b.unwrap() > 0,
            b.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] > 0 ==> arr@[j] >= b.unwrap(),
        decreases arr.len() - i,
    {
        if arr[i] < 0 && (a.is_none() || arr[i] >= a.unwrap()) {
            a = Some(arr[i]);
        }
        if arr[i] > 0 && (b.is_none() || arr[i] <= b.unwrap()) {
            b = Some(arr[i]);
        }
        i = i + 1;
    }
    (a, b)
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def largest_smallest_integers(lst):
    '''
    Create a function that returns a tuple (a, b), where 'a' is
    the largest of negative integers, and 'b' is the smallest
    of positive integers in a list.
    If there is no negative or positive integers, return them as None.

    Examples:
    largest_smallest_integers([2, 4, 1, 3, 5, 7]) == (None, 1)
    largest_smallest_integers([]) == (None, None)
    largest_smallest_integers([0]) == (None, None)
    '''

*/

/*
### ENTRY POINT
largest_smallest_integers
*/

/*
### CANONICAL SOLUTION
    smallest = list(filter(lambda x: x < 0, lst))
    largest = list(filter(lambda x: x > 0, lst))
    return (max(smallest) if smallest else None, min(largest) if largest else None)

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([2, 4, 1, 3, 5, 7]) == (None, 1)
    assert candidate([2, 4, 1, 3, 5, 7, 0]) == (None, 1)
    assert candidate([1, 3, 2, 4, 5, 6, -2]) == (-2, 1)
    assert candidate([4, 5, 3, 6, 2, 7, -7]) == (-7, 2)
    assert candidate([7, 3, 8, 4, 9, 2, 5, -9]) == (-9, 2)
    assert candidate([]) == (None, None)
    assert candidate([0]) == (None, None)
    assert candidate([-1, -3, -5, -6]) == (-1, None)
    assert candidate([-1, -3, -5, -6, 0]) == (-1, None)
    assert candidate([-6, -4, -4, -3, 1]) == (-3, 1)
    assert candidate([-6, -4, -4, -3, -100, 1]) == (-3, 1)

    # Check some edge cases that are easy to work out by hand.
    assert True

*/
