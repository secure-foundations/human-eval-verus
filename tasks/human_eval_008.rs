/*
### ID
HumanEval/8
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

/// Specification for what it means to sum a sequence of numbers
pub open spec fn sum(numbers: Seq<u32>) -> int {
    numbers.fold_left(0, |acc: int, x| acc + x)
}

/// Specification for taking the product of a sequence of numbers
pub open spec fn product(numbers: Seq<u32>) -> int {
    numbers.fold_left(1, |acc: int, x| acc * x)
}

/// Show that the sum won't grow too large
proof fn sum_bound(numbers: Seq<u32>)
    ensures
        sum(numbers) <= numbers.len() * u32::MAX,
    decreases numbers.len(),
{
    if numbers.len() == 0 {
    } else {
        sum_bound(numbers.drop_last());
    }
}

/// Implementation.  We leave the consequences of an intermediate
/// overflow during the product calculation underspecified.
fn sum_product(numbers: Vec<u32>) -> (result: (u64, Option<u32>))
    requires
        numbers.len() < u32::MAX,
    ensures
        result.0 == sum(numbers@),
        match result.1 {
            None =>   // Computing the product overflowed at some point
            exists|i|
                #![auto]
                0 <= i < numbers.len() && product(numbers@.subrange(0, i)) * numbers[i] as int
                    > u32::MAX,
            Some(v) => v == product(numbers@),
        },
{
    let mut sum_value: u64 = 0;
    let mut prod_value: Option<u32> = Some(1);
    for index in 0..numbers.len()
        invariant
            numbers.len() < u32::MAX,
            sum_value == sum(numbers@.take(index as int)),
            prod_value matches Some(v) ==> v == product(numbers@.take(index as int)),
            match prod_value {
                None =>   // Computing the product overflowed at some point
                exists|i|
                    #![auto]
                    0 <= i < index && product(numbers@.subrange(0, i)) * numbers[i] as int
                        > u32::MAX,
                Some(v) => v == product(numbers@.take(index as int)),
            },
            index <= numbers.len(),
            index >= 0,
    {
        proof {
            sum_bound(numbers@.take(index as int));
            assert(sum_value <= index * u32::MAX);
        }
        assert(numbers@.take(index as int + 1).drop_last() =~= numbers@.take(index as int));
        assert(numbers[index as int] == numbers@.take(index as int + 1).last());
        sum_value += numbers[index] as u64;
        prod_value =
        match prod_value {
            Some(v) => v.checked_mul(numbers[index]),
            None => None,
        };
    }
    assert(numbers@.take(numbers@.len() as int) =~= numbers@);
    (sum_value, prod_value)
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT
from typing import List, Tuple


def sum_product(numbers: List[int]) -> Tuple[int, int]:
    """ For a given list of integers, return a tuple consisting of a sum and a product of all the integers in a list.
    Empty sum should be equal to 0 and empty product should be equal to 1.
    >>> sum_product([])
    (0, 1)
    >>> sum_product([1, 2, 3, 4])
    (10, 24)
    """

*/

/*
### ENTRY POINT
sum_product
*/

/*
### CANONICAL SOLUTION
    sum_value = 0
    prod_value = 1

    for n in numbers:
        sum_value += n
        prod_value *= n
    return sum_value, prod_value

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([]) == (0, 1)
    assert candidate([1, 1, 1]) == (3, 1)
    assert candidate([100, 0]) == (100, 0)
    assert candidate([3, 5, 7]) == (3 + 5 + 7, 3 * 5 * 7)
    assert candidate([10]) == (10, 10)

*/
