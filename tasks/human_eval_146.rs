/*
### ID
HumanEval/146
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

// This spec function extracts the first digit of an integer
spec fn extract_first_digit_spec(n: int) -> int
    decreases n,
{
    if n < 10 {
        n
    } else {
        extract_first_digit_spec(n / 10)
    }
}

fn extract_first_digit(n: u32) -> (res: u32)
    ensures
        res == extract_first_digit_spec(n as int),
{
    if n < 10 {
        n
    } else {
        extract_first_digit(n / 10)
    }
}

// This spec function extracts the last digit of an integer
spec fn extract_last_digit_spec(n: int) -> int {
    n % 10
}

fn extract_last_digit(n: u32) -> (res: u32)
    ensures
        res == extract_last_digit_spec(n as int),
{
    n % 10
}

spec fn is_odd(n: int) -> bool {
    (n % 2) != 0
}

//This spec function determines a valid integer according to the problem description
spec fn is_valid_element_spec(n: int) -> bool {
    &&& (n > 10)
    &&& is_odd(extract_first_digit_spec(n))
    &&& is_odd(extract_last_digit_spec(n))
}

fn is_valid_element(n: i32) -> (res: bool)
    ensures
        res == is_valid_element_spec(n as int),
{
    ((n > 10) && (extract_first_digit(n as u32) % 2 != 0) && (extract_last_digit(n as u32) % 2
        != 0))
}

//This spec function specifies the postcondition according to the problem description
spec fn special_filter_spec(seq: Seq<i32>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        special_filter_spec(seq.drop_last()) + if (is_valid_element_spec(seq.last() as int)) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn special_filter(numbers: &Vec<i32>) -> (count: usize)
    ensures
        count == special_filter_spec(numbers@),
{
    let ghost numbers_length = numbers.len();
    let mut counter: usize = 0;
    let mut index = 0;
    while index < numbers.len()
        invariant
            0 <= index <= numbers.len(),
            0 <= counter <= index,
            counter == special_filter_spec(numbers@.subrange(0, index as int)),
    {
        if (is_valid_element(numbers[index])) {
            counter += 1;
        }
        index += 1;
        assert(numbers@.subrange(0, index - 1 as int) == numbers@.subrange(
            0,
            index as int,
        ).drop_last());
    }
    assert(numbers@ == numbers@.subrange(0, numbers_length as int));
    counter
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def specialFilter(nums):
    """Write a function that takes an array of numbers as input and returns
    the number of elements in the array that are greater than 10 and both
    first and last digits of a number are odd (1, 3, 5, 7, 9).
    For example:
    specialFilter([15, -73, 14, -15]) => 1
    specialFilter([33, -2, -3, 45, 21, 109]) => 2
    """

*/

/*
### ENTRY POINT
specialFilter
*/

/*
### CANONICAL SOLUTION

    count = 0
    for num in nums:
        if num > 10:
            odd_digits = (1, 3, 5, 7, 9)
            number_as_string = str(num)
            if int(number_as_string[0]) in odd_digits and int(number_as_string[-1]) in odd_digits:
                count += 1

    return count

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([5, -2, 1, -5]) == 0
    assert candidate([15, -73, 14, -15]) == 1
    assert candidate([33, -2, -3, 45, 21, 109]) == 2
    assert candidate([43, -12, 93, 125, 121, 109]) == 4
    assert candidate([71, -2, -33, 75, 21, 19]) == 3


    # Check some edge cases that are easy to work out by hand.
    assert candidate([1]) == 0
    assert candidate([]) == 0


*/
