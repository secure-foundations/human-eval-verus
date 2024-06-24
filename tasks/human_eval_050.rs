
/*
### ID
HumanEval/50
*/

/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

    // TODO: Put your solution (the specification, implementation, and proof) to the task here
 

} // verus!

fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def encode_shift(s: str):
    """
    returns encoded string by shifting every character by 5 in the alphabet.
    """
    return "".join([chr(((ord(ch) + 5 - ord("a")) % 26) + ord("a")) for ch in s])


def decode_shift(s: str):
    """
    takes as input string encoded with encode_shift function. Returns decoded string.
    """

*/

/*
### ENTRY POINT
decode_shift
*/

/*
### CANONICAL SOLUTION
    return "".join([chr(((ord(ch) - 5 - ord("a")) % 26) + ord("a")) for ch in s])

*/

/*
### TEST


METADATA = {}


def check(candidate):
    from random import randint, choice
    import copy
    import string

    letters = string.ascii_lowercase
    for _ in range(100):
        str = ''.join(choice(letters) for i in range(randint(10, 20)))
        encoded_str = encode_shift(str)
        assert candidate(copy.deepcopy(encoded_str)) == str


*/

