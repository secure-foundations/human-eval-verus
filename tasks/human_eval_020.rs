/*
### ID
HumanEval/20
*/
/*
### VERUS BEGIN
*/
use vstd::math::abs;
use vstd::prelude::*;

verus! {

// TODO: Put your solution (the specification, implementation, and proof) to the task here
// Implementation
fn closest_pair(numbers: Vec<i32>) -> (res: (i32, i32))
    requires
        numbers.len() >= 2,
    ensures
        res.0 <= res.1,
        exists|i: int, j: int|
            (0 <= i < numbers.len()) && (0 <= j < numbers.len()) && (i != j) && (res.0 == numbers[i]
                && res.1 == numbers[j]),
        forall|i: int, j: int|
            (0 <= i < numbers.len()) && (0 <= j < numbers.len()) && (i != j) ==> (abs(
                numbers[i] - numbers[j],
            ) >= abs(res.0 - res.1)),
{
    let mut closest_pair_high = numbers[0];
    let mut closest_pair_low = numbers[1];
    if closest_pair_high < closest_pair_low {
        let temp = closest_pair_high;
        closest_pair_high = closest_pair_low;
        closest_pair_low = temp;
    }
    let mut min_diff = closest_pair_high as i64 - closest_pair_low as i64;

    let mut i = 1;
    while i < numbers.len()
        invariant
            1 <= i <= numbers.len(),
            closest_pair_low <= closest_pair_high,
            min_diff == closest_pair_high - closest_pair_low,
            exists|ii: int, jj: int|
                (0 <= ii < numbers.len()) && (0 <= jj < numbers.len()) && (ii != jj) && (
                closest_pair_low == numbers[ii] && closest_pair_high == numbers[jj]),
            forall|k: int, l: int|
                (0 <= k < i) && (0 <= l < i) && (k != l) ==> (abs(numbers[k] - numbers[l])
                    >= min_diff),
        decreases numbers.len() - i,
    {
        assert(0 <= i < numbers.len());
        let mut j = 0;
        while j < i
            invariant
                0 <= j < numbers.len(),
                0 <= i < numbers.len(),
                closest_pair_low <= closest_pair_high,
                min_diff == closest_pair_high - closest_pair_low,
                exists|ii: int, jj: int|
                    (0 <= ii < numbers.len()) && (0 <= jj < numbers.len()) && (ii != jj) && (
                    closest_pair_low == numbers[ii] && closest_pair_high == numbers[jj]),
                forall|k: int| (0 <= k < j) ==> (abs(numbers[k] - numbers[i as int]) >= min_diff),
                forall|k: int, l: int|
                    (0 <= k < i) && (0 <= l < i) && (k != l) ==> (abs(numbers[k] - numbers[l])
                        >= min_diff),
            decreases i - j,
        {
            let diff = if numbers[i] < numbers[j] {
                numbers[j] as i64 - numbers[i] as i64
            } else {
                numbers[i] as i64 - numbers[j] as i64
            };
            if diff < min_diff {
                closest_pair_low =
                if numbers[i] < numbers[j] {
                    numbers[i]
                } else {
                    numbers[j]
                };
                closest_pair_high =
                if numbers[i] > numbers[j] {
                    numbers[i]
                } else {
                    numbers[j]
                };
                min_diff = closest_pair_high as i64 - closest_pair_low as i64;
            }
            j += 1;
        }
        i += 1;
    }

    return (closest_pair_low, closest_pair_high);
}

} // verus!
fn main() {
    print!("{:?}", closest_pair(vec![1, 2, 3, 4, 5, 2]));
    print!("{:?}", closest_pair(vec![1, 10, 7]));
}

/*
### VERUS END
*/

/*
### PROMPT
from typing import List, Tuple


def find_closest_elements(numbers: List[float]) -> Tuple[float, float]:
    """ From a supplied list of numbers (of length at least two) select and return two that are the closest to each
    other and return them in order (smaller number, larger number).
    >>> find_closest_elements([1.0, 2.0, 3.0, 4.0, 5.0, 2.2])
    (2.0, 2.2)
    >>> find_closest_elements([1.0, 2.0, 3.0, 4.0, 5.0, 2.0])
    (2.0, 2.0)
    """

*/

/*
### ENTRY POINT
find_closest_elements
*/

/*
### CANONICAL SOLUTION
    closest_pair = None
    distance = None

    for idx, elem in enumerate(numbers):
        for idx2, elem2 in enumerate(numbers):
            if idx != idx2:
                if distance is None:
                    distance = abs(elem - elem2)
                    closest_pair = tuple(sorted([elem, elem2]))
                else:
                    new_distance = abs(elem - elem2)
                    if new_distance < distance:
                        distance = new_distance
                        closest_pair = tuple(sorted([elem, elem2]))

    return closest_pair

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([1.0, 2.0, 3.9, 4.0, 5.0, 2.2]) == (3.9, 4.0)
    assert candidate([1.0, 2.0, 5.9, 4.0, 5.0]) == (5.0, 5.9)
    assert candidate([1.0, 2.0, 3.0, 4.0, 5.0, 2.2]) == (2.0, 2.2)
    assert candidate([1.0, 2.0, 3.0, 4.0, 5.0, 2.0]) == (2.0, 2.0)
    assert candidate([1.1, 2.2, 3.1, 4.1, 5.1]) == (2.2, 3.1)


*/
