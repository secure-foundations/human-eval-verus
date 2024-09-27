/*
### ID
HumanEval/66
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> bool {
    c >= 'A' && c <= 'Z'
}

// This spec function computes uppercase character (i.e, ASCII code) sum.
spec fn count_uppercase_sum(seq: Seq<char>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_uppercase_sum(seq.drop_last()) + if is_upper_case(seq.last()) {
            seq.last() as int
        } else {
            0 as int
        }
    }
}

// This function takes a string as input and returns the sum of the upper characters only'
fn digit_sum(text: &[char]) -> (sum: u128)
    ensures
        count_uppercase_sum(text@) == sum,
{
    let mut index = 0;
    let mut sum = 0u128;

    while index < text.len()
        invariant
            0 <= index <= text.len(),
            count_uppercase_sum(text@.subrange(0, index as int)) == sum,
            forall|j: int|
                0 <= j <= index ==> (u64::MIN * index <= (count_uppercase_sum(
                    #[trigger] text@.subrange(0, j),
                )) <= u64::MAX * index),
            u64::MIN * index <= sum <= u64::MAX * index,
    {
        if (text[index] >= 'A' && text[index] <= 'Z') {
            assert(text@.subrange(0, index as int) =~= text@.subrange(
                0,
                (index + 1) as int,
            ).drop_last());
            sum = sum + text[index] as u128;
        }
        index += 1;
        assert(text@.subrange(0, index - 1 as int) == text@.subrange(0, index as int).drop_last());

    }
    assert(index == text@.len());
    assert(text@ == text@.subrange(0, index as int));
    sum
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def digitSum(s):
    """Task
    Write a function that takes a string as input and returns the sum of the upper characters only'
    ASCII codes.

    Examples:
        digitSum("") => 0
        digitSum("abAB") => 131
        digitSum("abcCd") => 67
        digitSum("helloE") => 69
        digitSum("woArBld") => 131
        digitSum("aAaaaXa") => 153
    """

*/

/*
### ENTRY POINT
digitSum
*/

/*
### CANONICAL SOLUTION
    if s == "": return 0
    return sum(ord(char) if char.isupper() else 0 for char in s)

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate("") == 0, "Error"
    assert candidate("abAB") == 131, "Error"
    assert candidate("abcCd") == 67, "Error"
    assert candidate("helloE") == 69, "Error"
    assert candidate("woArBld") == 131, "Error"
    assert candidate("aAaaaXa") == 153, "Error"

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate(" How are yOu?") == 151, "Error"
    assert candidate("You arE Very Smart") == 327, "Error"


*/
