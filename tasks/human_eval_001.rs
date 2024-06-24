
/*
### ID
HumanEval/1
*/

/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

/// This function computes the net nesting level at the end of a particular `input`,
/// where a left parenthesis increments the net nesting level and a right parenthesis
/// decrements it.
pub open spec fn nesting_level(input: Seq<char>) -> int
    decreases
        input.len()
{
    if input.len() == 0 {
        0
    }
    else {
        let prev_nesting_level = nesting_level(input.drop_last());
        let c = input.last();
        if c == '(' {
            prev_nesting_level + 1
        }
        else if c == ')' {
            prev_nesting_level - 1
        }
        else {
            prev_nesting_level
        }
    }
}

pub open spec fn is_paren_char(c: char) -> bool
{
    c == '(' || c == ')'
}

/// A sequence of characters is a balanced group of parentheses if
/// it's non-empty, it only consists of parentheses, its nesting level
/// is zero, and any nonempty strict prefix has a positive nesting
/// level.
pub open spec fn is_balanced_group(input: Seq<char>) -> bool
{
    &&& input.len() > 0
    &&& nesting_level(input) == 0
    &&& forall |i| 0 <= i < input.len() ==> is_paren_char(#[trigger] input[i])
    &&& forall |i| 0 < i < input.len() ==> nesting_level(#[trigger] input.take(i)) > 0
}

/// A sequence of characters is a sequence of balanced groups of
/// parentheses if its nesting level is zero and any prefix has
/// a non-negative nesting level.
pub open spec fn is_sequence_of_balanced_groups(input: Seq<char>) -> bool
{
    &&& nesting_level(input) == 0
    &&& forall |i| 0 < i < input.len() ==> nesting_level(#[trigger] input.take(i)) >= 0
}

pub open spec fn vecs_to_seqs<T>(s: Seq<Vec<T>>) -> Seq<Seq<T>>
{
    s.map(|_i, ss: Vec<T>| ss@)
}

pub open spec fn remove_nonparens(s: Seq<char>) -> Seq<char>
{
    s.filter(|c| is_paren_char(c))
}

/// This proof specifies the relationship between `remove_nonparens(s.take(pos + 1))`
/// and `remove_nonparens(s.take(pos))`.
proof fn lemma_remove_nonparens_maintained_by_push(s: Seq<char>, pos: int)
    requires
        0 <= pos < s.len(),
    ensures
        ({
            let s1 = remove_nonparens(s.take(pos as int));
            let s2 = remove_nonparens(s.take((pos + 1) as int));
            if is_paren_char(s[pos]) { s2 == s1.push(s[pos]) } else { s2 == s1 }
        })
    decreases
        pos
{
    reveal(Seq::filter);
    assert(s.take((pos + 1) as int).drop_last() =~= s.take(pos as int));
    if pos != 0 {
        lemma_remove_nonparens_maintained_by_push(s, pos - 1);
    }
}

/// This is the function specified at the top of the file.
fn separate_paren_groups(input: &Vec<char>) -> (groups: Vec<Vec<char>>)
    requires
        is_sequence_of_balanced_groups(input@),
    ensures
        // All groups in the result are balanced and non-nested
        forall |i: int| #![trigger groups[i]] 0 <= i < groups.len() ==> is_balanced_group(groups[i]@),
        // The concatenation of all groups in the result equals the input string without spaces
        vecs_to_seqs(groups@).flatten() == remove_nonparens(input@),
{
    // Loop through the input one character at a time, keeping track of:
    //
    // `groups`: A vector of complete balanced groups found so far.
    // `current_group`: The current, incomplete balanced group found since then.

    let mut groups: Vec<Vec<char>> = Vec::new();
    let mut current_group: Vec<char> = Vec::new();
    let input_len = input.len();

    // For proof purposes, we also keep track of some ghost state that
    // lets us more readily reason about
    // `vecs_to_seqs(groups@)`. Specifically, we'll maintain
    // the invariant that `ghost_groups == vecs_to_seqs(groups@)`.

    let ghost mut ghost_groups: Seq<Seq<char>> = Seq::empty();
    
    proof {
        assert(vecs_to_seqs(groups@) =~= ghost_groups);
        assert(remove_nonparens(input@.take(0)) =~= Seq::<char>::empty());
        assert(ghost_groups.flatten() + current_group@ =~= Seq::<char>::empty());
    }
    let mut current_nesting_level: usize = 0;
    for pos in 0..input_len
        invariant
            input_len == input.len(),
            ghost_groups == vecs_to_seqs(groups@),
            ghost_groups.flatten() + current_group@ == remove_nonparens(input@.take(pos as int)),
            forall |i: int| #![trigger groups[i]] 0 <= i < ghost_groups.len() ==> is_balanced_group(ghost_groups[i]),
            current_nesting_level == nesting_level(input@.take(pos as int)),
            current_nesting_level == nesting_level(current_group@),
            current_nesting_level <= pos, // this bound lets us prove that increments can't overflow a `usize`
            current_group@.len() == 0 <==> current_nesting_level == 0,
            forall |i| 0 <= i < current_group@.len() ==> is_paren_char(#[trigger] current_group@[i]),
            forall |i| 0 < i < current_group@.len() ==> nesting_level(#[trigger] current_group@.take(i)) > 0,
            is_sequence_of_balanced_groups(input@),
    {
        let ghost prev_group = current_group@;
        let ghost prev_groups = ghost_groups;
        let c = input[pos];

        proof {
            assert(input@.take((pos + 1) as int) == input@.take(pos as int).push(c));
            assert(input@.take((pos + 1) as int).drop_last() == input@.take(pos as int));
            lemma_remove_nonparens_maintained_by_push(input@, pos as int);
        }

        if c == '(' {
            current_nesting_level = current_nesting_level + 1;
            current_group.push('(');
            assert(current_group@.drop_last() == prev_group);
            assert(ghost_groups.flatten() + current_group@ =~= (ghost_groups.flatten() + prev_group).push('('));
            assert(forall |i| 0 < i < prev_group.len() ==> #[trigger] current_group@.take(i) == prev_group.take(i));
        }
        else if c == ')' {
            current_nesting_level = current_nesting_level - 1;
            current_group.push(')');
            assert(current_group@.drop_last() == prev_group);
            assert(ghost_groups.flatten() + current_group@ =~= (ghost_groups.flatten() + prev_group).push(')'));
            assert(forall |i| 0 < i < prev_group.len() ==> #[trigger] current_group@.take(i) == prev_group.take(i));

            // We can tell whether the current group we just assembled is balanced
            // by checking whether `current_nesting_level` is zero. In that case,
            // it's done and we can add it to `groups`.
            
            if current_nesting_level == 0 {
                proof {
                    ghost_groups = ghost_groups.push(current_group@);

                    assert(vecs_to_seqs(groups@.push(current_group)) =~= vecs_to_seqs(groups@).push(current_group@));
                    assert(ghost_groups.drop_last() == prev_groups);
                    assert(ghost_groups.flatten() =~= prev_groups.flatten() + current_group@) by {
                        prev_groups.lemma_flatten_and_flatten_alt_are_equivalent();
                        ghost_groups.lemma_flatten_and_flatten_alt_are_equivalent();
                    }
                }
                
                groups.push(current_group);
                current_group = Vec::<char>::new();
                assert(ghost_groups.flatten() + current_group@ =~= remove_nonparens(input@.take((pos + 1) as int)));
            }
        }
    }

    assert(input@.take(input_len as int) =~= input@);
    assert(ghost_groups.flatten() + current_group@ == ghost_groups.flatten());
    groups
}

} // verus!

fn main() {}

/*
### VERUS END
*/

/*
### PROMPT
from typing import List


def separate_paren_groups(paren_string: str) -> List[str]:
    """ Input to this function is a string containing multiple groups of nested parentheses. Your goal is to
    separate those group into separate strings and return the list of those.
    Separate groups are balanced (each open brace is properly closed) and not nested within each other
    Ignore any spaces in the input string.
    >>> separate_paren_groups('( ) (( )) (( )( ))')
    ['()', '(())', '(()())']
    """

*/

/*
### ENTRY POINT
separate_paren_groups
*/

/*
### CANONICAL SOLUTION
    result = []
    current_string = []
    current_depth = 0

    for c in paren_string:
        if c == '(':
            current_depth += 1
            current_string.append(c)
        elif c == ')':
            current_depth -= 1
            current_string.append(c)

            if current_depth == 0:
                result.append(''.join(current_string))
                current_string.clear()

    return result

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('(()()) ((())) () ((())()())') == [
        '(()())', '((()))', '()', '((())()())'
    ]
    assert candidate('() (()) ((())) (((())))') == [
        '()', '(())', '((()))', '(((())))'
    ]
    assert candidate('(()(())((())))') == [
        '(()(())((())))'
    ]
    assert candidate('( ) (( )) (( )( ))') == ['()', '(())', '(()())']

*/

