/*
### ID
HumanEval/26
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

// This spec function recursively computes the frequency of an element in a given sequence.
pub open spec fn count_frequency_spec(seq: Seq<i64>, key: i64) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_spec(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}

// This auxilary exe function computes the frequency of an element in a given sequence
fn count_frequency(elements: &Vec<i64>, key: i64) -> (frequency: usize)
    ensures
        count_frequency_spec(elements@, key) == frequency,
{
    let ghost elements_length = elements.len();
    let mut counter = 0;
    let mut index = 0;
    while index < elements.len()
        invariant
            0 <= index <= elements.len(),
            0 <= counter <= index,
            count_frequency_spec(elements@.subrange(0, index as int), key) == counter,
        decreases elements.len() - index,
    {
        if (elements[index] == key) {
            counter += 1;
        }
        index += 1;
        assert(elements@.subrange(0, index - 1 as int) == elements@.subrange(
            0,
            index as int,
        ).drop_last());
    }
    assert(elements@ == elements@.subrange(0, elements_length as int));
    counter
}

//This function removes all elements that occur more than once
// Implementation following the ground-truth
fn remove_duplicates(numbers: &Vec<i64>) -> (unique_numbers: Vec<i64>)
    ensures
        unique_numbers@ == numbers@.filter(|x: i64| count_frequency_spec(numbers@, x) == 1),
{
    let ghost numbers_length = numbers.len();
    let mut unique_numbers: Vec<i64> = Vec::new();
    assert(numbers@.take(0int).filter(|x: i64| count_frequency_spec(numbers@, x) == 1) == Seq::<
        i64,
    >::empty());

    for index in 0..numbers.len()
        invariant
            0 <= index <= numbers.len(),
            unique_numbers@ == numbers@.take(index as int).filter(
                |x: i64| count_frequency_spec(numbers@, x) == 1,
            ),
    {
        if count_frequency(&numbers, numbers[index]) == 1 {
            unique_numbers.push(numbers[index]);
        }
        assert(numbers@.take((index + 1) as int).drop_last() == numbers@.take(index as int));
        reveal(Seq::filter);
    }
    assert(numbers@ == numbers@.take(numbers_length as int));
    unique_numbers
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT
from typing import List


def remove_duplicates(numbers: List[int]) -> List[int]:
    """ From a list of integers, remove all elements that occur more than once.
    Keep order of elements left the same as in the input.
    >>> remove_duplicates([1, 2, 3, 2, 4])
    [1, 3, 4]
    """

*/

/*
### ENTRY POINT
remove_duplicates
*/

/*
### CANONICAL SOLUTION
    import collections
    c = collections.Counter(numbers)
    return [n for n in numbers if c[n] <= 1]

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([]) == []
    assert candidate([1, 2, 3, 4]) == [1, 2, 3, 4]
    assert candidate([1, 2, 3, 2, 4, 3, 5]) == [1, 4, 5]

*/
