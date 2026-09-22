/*
### ID
HumanEval/10
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

spec fn spec_is_palindrome(string: Seq<char>) -> bool {
    string == string.reverse()
}

fn is_palindrome(string: &[char]) -> (result: bool)
    ensures
        result <==> spec_is_palindrome(string@),
{
    let len: usize = string.len();
    let mut i: usize = 0;
    while i < len
        invariant
            len == string.len(),
            0 <= i <= len,
            forall|j: int| 0 <= j < i ==> #[trigger] string[j] == string[len - 1 - j],
        decreases len - i,
    {
        if string[i] != string[len - 1 - i] {
            return false;
        }
        i += 1;
    }
    assert(string@ =~= string@.reverse());
    true
}

proof fn palidrome_sandwich(a: Seq<char>, b: Seq<char>)
    requires
        spec_is_palindrome(b),
    ensures
        spec_is_palindrome((a + b) + a.reverse()),
{
    assert(((a + b) + a.reverse()).reverse() == a + b + a.reverse());
}

proof fn palidrome_sandwich_reverse(a: Seq<char>, i: int)
    requires
        spec_is_palindrome(a),
        0 <= i <= a.len() - i,
    ensures
        spec_is_palindrome(a.subrange(i, a.len() - i)),
{
    assert(a.subrange(i, a.len() - i) =~= a.subrange(i, a.len() - i).reverse());
}

fn reverse(string: &[char]) -> (result: Vec<char>)
    ensures
        result.len() == string.len(),
        forall|i: int| 0 <= i < string.len() ==> result[i] == string[string.len() - 1 - i],
{
    let mut reversed = Vec::new();
    let mut i = string.len();
    while i > 0
        invariant
            0 <= i <= string.len(),
            reversed.len() == string.len() - i,
            forall|j: int| 0 <= j < reversed.len() ==> reversed[j] == string[string.len() - 1 - j],
        decreases i,
    {
        i -= 1;
        reversed.push(string[i].clone());
    }
    reversed
}

fn make_palindrome(string: Vec<char>) -> (result: Vec<char>)
    ensures
        result.len() >= string.len(),
        result@.subrange(0, string@.len() as int) == string@,
        spec_is_palindrome(result@),
        forall|s: Seq<char>|
            #![auto]
            spec_is_palindrome(s) && s.len() >= string.len() as int && s.subrange(
                0,
                string@.len() as int,
            ) == string@ ==> result@.len() <= s.len(),
{
    let len = string.len();
    let mut beginning_of_suffix = 0;

    while beginning_of_suffix < len && !is_palindrome(
        slice_subrange(string.as_slice(), beginning_of_suffix, len),
    )
        invariant
            len == string.len(),
            0 <= beginning_of_suffix <= len,
            forall|bos: int|
                #![auto]
                0 <= bos < beginning_of_suffix ==> !spec_is_palindrome(
                    string@.subrange(bos, len as int),
                ),
        decreases len - beginning_of_suffix,
    {
        beginning_of_suffix += 1;
    }

    if !(beginning_of_suffix < len) {
        assert(string@.subrange(len as int, len as int) =~= Seq::<char>::empty());
    }
    let mut ret = string.clone();
    let mut app = reverse(slice_subrange(&string, 0, beginning_of_suffix));
    ret.append(&mut app);

    assert(ret@ == (string@.subrange(0, beginning_of_suffix as int) + string@.subrange(
        beginning_of_suffix as int,
        len as int,
    )) + string@.subrange(0, beginning_of_suffix as int).reverse());
    proof {
        palidrome_sandwich(
            string@.subrange(0, beginning_of_suffix as int),
            string@.subrange(beginning_of_suffix as int, len as int),
        );
    }
    assert forall|s: Seq<char>|
        #![auto]
        spec_is_palindrome(s) && s.len() >= len as int && s.subrange(0, string@.len() as int)
            == string@ implies ret@.len() <= s.len() by {
        if (ret@.len() > s.len()) {
            palidrome_sandwich_reverse(s, s.len() - len);
            assert(s.subrange(s.len() - len, len as int) == s.subrange(
                0,
                string@.len() as int,
            ).subrange(s.len() - len, len as int));
            // contradicts with the instantialization of (0 <= bos < beginning_of_suffix ==> !spec_is_palindrome(string@.subrange(bos, len as int)))
            // by taking bos = s.len() - len
        }
    }
    ret
}

} // verus!
/*
### VERUS END
*/
pub fn main() {
    assert_eq!(
        make_palindrome(vec!['c', 'a', 't']),
        vec!['c', 'a', 't', 'a', 'c']
    );
    assert_eq!(
        make_palindrome(vec!['c', 'a', 't', 'a']),
        vec!['c', 'a', 't', 'a', 'c']
    );
    assert_eq!(make_palindrome(vec![]), vec![]);
    assert_eq!(make_palindrome(vec!['x']), vec!['x']);
    assert_eq!(
        make_palindrome(vec!['x', 'y', 'z']),
        vec!['x', 'y', 'z', 'y', 'x']
    );
    assert_eq!(make_palindrome(vec!['x', 'y', 'x']), vec!['x', 'y', 'x']);
    assert_eq!(
        make_palindrome(vec!['j', 'e', 'r', 'r', 'y']),
        vec!['j', 'e', 'r', 'r', 'y', 'r', 'r', 'e', 'j']
    );
    println!("All tests passed!");
}

/*
### PROMPT


def is_palindrome(string: str) -> bool:
    """ Test if given string is a palindrome """
    return string == string[::-1]


def make_palindrome(string: str) -> str:
    """ Find the shortest palindrome that begins with a supplied string.
    Algorithm idea is simple:
    - Find the longest postfix of supplied string that is a palindrome.
    - Append to the end of the string reverse of a string prefix that comes before the palindromic suffix.
    >>> make_palindrome('')
    ''
    >>> make_palindrome('cat')
    'catac'
    >>> make_palindrome('cata')
    'catac'
    """

*/

/*
### ENTRY POINT
make_palindrome
*/

/*
### CANONICAL SOLUTION
    if not string:
        return ''

    beginning_of_suffix = 0

    while not is_palindrome(string[beginning_of_suffix:]):
        beginning_of_suffix += 1

    return string + string[:beginning_of_suffix][::-1]

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('') == ''
    assert candidate('x') == 'x'
    assert candidate('xyz') == 'xyzyx'
    assert candidate('xyx') == 'xyx'
    assert candidate('jerry') == 'jerryrrej'

*/
