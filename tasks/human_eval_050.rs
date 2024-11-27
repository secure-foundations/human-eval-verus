/*
### ID
HumanEval/50
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn encode_char_spec(c: int) -> int
    recommends
        65 <= c <= 90,
{
    (c - 65 + 5) % 26 + 65
}

fn encode_char(c: u8) -> (r: u8)
    requires
        65 <= c <= 90,
    ensures
        r == encode_char_spec(c as int),
        65 <= r <= 90,
{
    (c - 65 + 5) % 26 + 65
}

spec fn decode_char_spec(c: int) -> int
    recommends
        65 <= c <= 90,
{
    (c - 65 + 26 - 5) % 26 + 65
}

fn decode_char(c: u8) -> (r: u8)
    requires
        65 <= c <= 90,
    ensures
        r == decode_char_spec(c as int),
        65 <= r <= 90,
{
    (c - 65 + 26 - 5) % 26 + 65
}

proof fn opposite_encode_decode(c: int)
    requires
        65 <= c <= 90,
    ensures
        encode_char_spec(decode_char_spec(c)) == c,
        decode_char_spec(encode_char_spec(c)) == c,
{
}

#[verifier::loop_isolation(false)]
fn encode_shift(s: &Vec<u8>) -> (t: Vec<u8>)
    requires
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> 65 <= s[i] <= 90,
    ensures
        s.len() == t.len(),
        forall|i: int| #![auto] 0 <= i < t.len() ==> t[i] == encode_char_spec(s[i] as int),
        forall|i: int| #![auto] 0 <= i < t.len() ==> decode_char_spec(t[i] as int) == s[i],
{
    let mut t: Vec<u8> = vec![];
    for i in 0..s.len()
        invariant
            t.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> t[j] == encode_char_spec(s[j] as int),
            forall|j: int| #![auto] 0 <= j < i ==> decode_char_spec(t[j] as int) == s[j],
    {
        t.push(encode_char(s[i]));
        proof {
            opposite_encode_decode(s[i as int] as int);
        }
    }
    t
}

#[verifier::loop_isolation(false)]
fn decode_shift(s: &Vec<u8>) -> (t: Vec<u8>)
    requires
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> 65 <= s[i] <= 90,
    ensures
        s.len() == t.len(),
        forall|i: int| #![auto] 0 <= i < t.len() ==> t[i] == decode_char_spec(s[i] as int),
        forall|i: int| #![auto] 0 <= i < t.len() ==> encode_char_spec(t[i] as int) == s[i],
{
    let mut t: Vec<u8> = vec![];
    for i in 0..s.len()
        invariant
            t.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> t[j] == decode_char_spec(s[j] as int),
            forall|j: int| #![auto] 0 <= j < i ==> encode_char_spec(t[j] as int) == s[j],
    {
        t.push(decode_char(s[i]));
        proof {
            opposite_encode_decode(s[i as int] as int);
        }
    }
    t
}

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
