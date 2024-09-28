/*
### ID
HumanEval/51
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

// This spec function checks whether a character is vowel
pub open spec fn is_vowel_spec(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}

// This auxilary exe function checks whether a character is vowel
fn is_vowel(c: char) -> (is_vowel: bool)
    ensures
        is_vowel == is_vowel_spec(c),
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}

// Implementation following the ground-truth
// This function removes vowels from a given string
fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)
    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
{
    let ghost str_length = str.len();
    let mut str_without_vowels: Vec<char> = Vec::new();
    assert(str@.take(0int).filter(|x: char| !is_vowel_spec(x)) == Seq::<char>::empty());

    for index in 0..str.len()
        invariant
            str_without_vowels@ == str@.take(index as int).filter(|x: char| !is_vowel_spec(x)),
    {
        if !is_vowel(str[index]) {
            str_without_vowels.push(str[index]);
        }
        assert(str@.take((index + 1) as int).drop_last() == str@.take(index as int));
        reveal(Seq::filter);
    }
    assert(str@ == str@.take(str_length as int));
    str_without_vowels
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def remove_vowels(text):
    """
    remove_vowels is a function that takes string and returns string without vowels.
    >>> remove_vowels('')
    ''
    >>> remove_vowels("abcdef\nghijklm")
    'bcdf\nghjklm'
    >>> remove_vowels('abcdef')
    'bcdf'
    >>> remove_vowels('aaaaa')
    ''
    >>> remove_vowels('aaBAA')
    'B'
    >>> remove_vowels('zbcd')
    'zbcd'
    """

*/

/*
### ENTRY POINT
remove_vowels
*/

/*
### CANONICAL SOLUTION
    return "".join([s for s in text if s.lower() not in ["a", "e", "i", "o", "u"]])

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate('') == ''
    assert candidate("abcdef\nghijklm") == 'bcdf\nghjklm'
    assert candidate('fedcba') == 'fdcb'
    assert candidate('eeeee') == ''
    assert candidate('acBAA') == 'cB'
    assert candidate('EcBOO') == 'cB'
    assert candidate('ybcd') == 'ybcd'


*/
