
/*
### ID
HumanEval/11
*/

/*
### VERUS BEGIN
*/
use vstd::prelude::*;
use vstd::slice::*;

verus! {

/// helper function to check if a character is '0' or '1'
spec fn is_binary_digit(c: char) -> bool {
    c == '0' || c == '1'
}

/// helper function to perform XOR on two binary characters
spec fn xor_char(a: char, b: char) -> (result: char)
    recommends
        is_binary_digit(a),
        is_binary_digit(b),
{
    if a == b { '0' } else { '1' }
}

fn string_xor(a: &[char], b: &[char]) -> (result: Vec<char>)
    requires
        a@.len() == b@.len(), // both strings must be of equal length
        forall |i: int| 0 <= i < a@.len() as int ==> is_binary_digit(#[trigger] a[i]),
        forall |i: int| 0 <= i < b@.len() as int ==> is_binary_digit(#[trigger] b[i]),
    ensures
        result.len() == a@.len(),
        forall |i: int| 0 <= i < result.len() as int ==> #[trigger] result[i] == xor_char(a[i], b[i]),
{
    let a_len = a.len();
    let mut result = Vec::with_capacity(a_len);

    #[verifier::loop_isolation(false)]
    for pos in 0..a_len
        invariant
            result.len() == pos,
            forall |i: int| 0 <= i < pos ==> #[trigger] result[i] == xor_char(a[i], b[i]),
    {
        if *slice_index_get(a, pos) == *slice_index_get(b, pos) {
            result.push('0');
        }
        else {
            result.push('1');
        }
    }

    result
}

} // verus!

fn main() {}

/*
### VERUS END
*/

/*
### PROMPT
from typing import List


def string_xor(a: str, b: str) -> str:
    """ Input are two strings a and b consisting only of 1s and 0s.
    Perform binary XOR on these inputs and return result also as a string.
    >>> string_xor('010', '110')
    '100'
    """

*/

/*
### ENTRY POINT
string_xor
*/

/*
### CANONICAL SOLUTION
    def xor(i, j):
        if i == j:
            return '0'
        else:
            return '1'

    return ''.join(xor(x, y) for x, y in zip(a, b))

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('111000', '101010') == '010010'
    assert candidate('1', '1') == '0'
    assert candidate('0101', '0000') == '0101'

*/

