/*
### ID
HumanEval/82
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

pub open spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}

// Implementation following the ground-truth
// This function determines if a given string length is prime or not
fn prime_length(str: &[char]) -> (result: bool)
    ensures
        result == if str.len() < 2 {
            false
        } else {
            (forall|k: int| 2 <= k < str.len() ==> !is_divisible(str.len() as int, k))
        },
{
    if str.len() < 2 {
        return false;
    }
    for index in 2..str.len()
        invariant
            2 <= index <= str.len(),
            forall|k: int| 2 <= k < index ==> !is_divisible(str.len() as int, k),
    {
        if ((str.len() % index) == 0) {
            assert(is_divisible(str.len() as int, index as int));
            return false;
        }
    }
    true
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def prime_length(string):
    """Write a function that takes a string and returns True if the string
    length is a prime number or False otherwise
    Examples
    prime_length('Hello') == True
    prime_length('abcdcba') == True
    prime_length('kittens') == True
    prime_length('orange') == False
    """

*/

/*
### ENTRY POINT
prime_length
*/

/*
### CANONICAL SOLUTION
    l = len(string)
    if l == 0 or l == 1:
        return False
    for i in range(2, l):
        if l % i == 0:
            return False
    return True

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate('Hello') == True
    assert candidate('abcdcba') == True
    assert candidate('kittens') == True
    assert candidate('orange') == False
    assert candidate('wow') == True
    assert candidate('world') == True
    assert candidate('MadaM') == True
    assert candidate('Wow') == True
    assert candidate('') == False
    assert candidate('HI') == True
    assert candidate('go') == True
    assert candidate('gogo') == False
    assert candidate('aaaaaaaaaaaaaaa') == False

    # Check some edge cases that are easy to work out by hand.
    assert candidate('Madam') == True
    assert candidate('M') == False
    assert candidate('0') == False


*/
