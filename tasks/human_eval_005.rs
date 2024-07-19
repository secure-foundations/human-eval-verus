/*
### ID
HumanEval/5
*/
/*
### VERUS BEGIN
*/
use vstd::assert_seqs_equal;
use vstd::prelude::*;

verus! {

/// Specification for inserting a number 'delimiter' between every two consecutive elements
/// of input sequence `numbers'
pub open spec fn intersperse_spec(numbers: Seq<u64>, delimiter: u64) -> Seq<u64>
    decreases numbers.len(),
{
    if numbers.len() <= 1 {
        numbers
    } else {
        intersperse_spec(numbers.drop_last(), delimiter) + seq![delimiter, numbers.last()]
    }
}

// We use these two functions to provide valid triggers for the quantifiers in intersperse_quantified
spec fn even(i: int) -> int {
    2 * i
}

spec fn odd(i: int) -> int {
    2 * i + 1
}

// This quantified formulation of intersperse is easier to reason about in the implementation's loop
spec fn intersperse_quantified(numbers: Seq<u64>, delimiter: u64, interspersed: Seq<u64>) -> bool {
    (if numbers.len() == 0 {
        interspersed.len() == 0
    } else {
        interspersed.len() == 2 * numbers.len() - 1
    }) && (forall|i: int| 0 <= i < numbers.len() ==> #[trigger] interspersed[even(i)] == numbers[i])
        && (forall|i: int|
        0 <= i < numbers.len() - 1 ==> #[trigger] interspersed[odd(i)] == delimiter)
}

proof fn intersperse_spec_len(numbers: Seq<u64>, delimiter: u64)
    ensures
        numbers.len() > 0 ==> intersperse_spec(numbers, delimiter).len() == 2 * numbers.len() - 1,
    decreases numbers.len(),
{
    if numbers.len() > 0 {
        intersperse_spec_len(numbers.drop_last(), delimiter);
    }
}

// Show that the two descriptions of intersperse are equivalent
proof fn intersperse_quantified_is_spec(numbers: Seq<u64>, delimiter: u64, interspersed: Seq<u64>)
    requires
        intersperse_quantified(numbers, delimiter, interspersed),
    ensures
        interspersed == intersperse_spec(numbers, delimiter),
    decreases numbers.len(),
{
    let is = intersperse_spec(numbers, delimiter);
    if numbers.len() == 0 {
    } else if numbers.len() == 1 {
        assert(interspersed.len() == 1);
        assert(interspersed[even(0)] == numbers[0]);
    } else {
        intersperse_quantified_is_spec(
            numbers.drop_last(),
            delimiter,
            interspersed.take(interspersed.len() - 2),
        );
        intersperse_spec_len(numbers, delimiter);
        assert_seqs_equal!(is == interspersed, i => {
            if i < is.len() - 2 {
            } else {
                if i % 2 == 0 {
                    assert(is[i] == numbers.last());
                    assert(interspersed[even(i/2)] == numbers[i / 2]);
                    assert(i / 2 == numbers.len() - 1);
                } else {
                    assert(is[i] == delimiter);
                    assert(interspersed[odd((i-1)/2)] == delimiter);
                }
            }
        });
    }
    assert(interspersed =~= intersperse_spec(numbers, delimiter));
}

/// Implementation of intersperse
pub fn intersperse(numbers: Vec<u64>, delimiter: u64) -> (result: Vec<u64>)
    ensures
        result@ == intersperse_spec(numbers@, delimiter),
{
    if numbers.len() <= 1 {
        numbers
    } else {
        let mut result = Vec::new();
        let mut index = 0;
        while index < numbers.len() - 1
            invariant
                numbers.len() > 1,
                0 <= index < numbers.len(),
                result.len() == 2 * index,
                forall|i: int| 0 <= i < index ==> #[trigger] result[even(i)] == numbers[i],
                forall|i: int| 0 <= i < index ==> #[trigger] result[odd(i)] == delimiter,
        {
            result.push(numbers[index]);
            result.push(delimiter);
            index += 1;
            //assert(numbers@.subrange(0, index as int).drop_last() =~= numbers@.subrange(0, index as int - 1));
        }
        result.push(numbers[numbers.len() - 1]);
        proof {
            intersperse_quantified_is_spec(numbers@, delimiter, result@);
        }
        result
    }
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT
from typing import List


def intersperse(numbers: List[int], delimiter: int) -> List[int]:
    """ Insert a number 'delimiter' between every two consecutive elements of input list `numbers'
    >>> intersperse([], 4)
    []
    >>> intersperse([1, 2, 3], 4)
    [1, 4, 2, 4, 3]
    """

*/

/*
### ENTRY POINT
intersperse
*/

/*
### CANONICAL SOLUTION
    if not numbers:
        return []

    result = []

    for n in numbers[:-1]:
        result.append(n)
        result.append(delimiter)

    result.append(numbers[-1])

    return result

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([], 7) == []
    assert candidate([5, 6, 3, 2], 8) == [5, 8, 6, 8, 3, 8, 2]
    assert candidate([2, 2, 2], 2) == [2, 2, 2, 2, 2]

*/
