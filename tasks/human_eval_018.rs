/*
### ID
HumanEval/18
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

    // spec
    pub closed spec fn how_many_times(string : Seq<char>, substring : Seq<char>) -> nat 
        decreases string.len()
    {
        if (string.len() == 0) {
            0
        } else if substring.is_prefix_of(string) {
            1 + how_many_times(string.skip(1), substring)
        } else {
            how_many_times(string.skip(1), substring)
        }
    }

    // implementation

    proof fn lemma_step_subrange (substring : Seq<char>, string : Seq<char>)
        requires 
            substring.len() > 0,
            string.len() >= substring.len(),
        ensures
            (substring[0] == string.subrange(0, substring.len() as int)[0] 
            && (substring.skip(1) =~= string.skip(1).subrange(0, substring.skip(1).len() as int)))
            ==> (substring =~= string.subrange(0, substring.len() as int))
        decreases
            substring.len()
    {
        if (substring[0] == string.subrange(0, substring.len() as int)[0] && (substring.skip(1) =~= string.skip(1).subrange(0, substring.skip(1).len() as int))) {
            assert forall |i:int| 0 <=i < substring.len() implies #[trigger] substring[i] == string.subrange(0, substring.len() as int)[i] by {
                if i == 0 {} else {
                    assert (forall |j : int|  (0 <= #[trigger] (j + 0) < substring.len() - 1) ==> substring.skip(1)[j] == string.skip(1).subrange(0, substring.skip(1).len() as int)[j]);
                    assert (0 <= #[trigger] (i - 1 + 0) < substring.len() - 1);
                }
            }
        } else {}
    }

    fn is_prefix (substring : Vec<char>, string : Vec<char>) -> (b : bool)
        ensures b == substring@.is_prefix_of(string@)
    {
        let mut current_substring = substring.clone();
        let mut current_string = string.clone();

        if substring.len() > string.len() {
            return false
        }
        while (current_substring.len() > 0)
            invariant 
                0 <= current_substring.len() <= current_string.len(),
                substring.len() <= string.len(),
                (substring@ =~= string@.subrange(0, substring@.len() as int)) == (current_substring@ =~= current_string@.subrange(0, current_substring@.len() as int))
            decreases 
                current_substring.len()
        {   
            if (current_substring[0] != current_string[0]) {
                return false;
            }

            let old_substring = current_substring.clone();
            let old_string = current_string.clone();

            let substring_first = current_substring.remove(0);
            let string_first = current_string.remove(0);
            assert ((old_substring@ =~= old_string@.subrange(0, old_substring@.len() as int)) <== (old_substring@[0] == old_string@.subrange(0, old_substring@.len() as int)[0] && (old_substring@.skip(1) =~= old_string@.skip(1).subrange(0, old_substring@.skip(1).len() as int)))) by {lemma_step_subrange(old_substring@, old_string@)};
        }
        return true;
    }

    proof fn lemma_how_many_times_zero(string : Seq<char>, substring : Seq<char>) 
        requires
            string.len() < substring.len(),
        ensures 
            how_many_times(string, substring) == 0,
        decreases 
            string.len()
    {
        if string.len() == 0 {} else {
            lemma_how_many_times_zero(string.skip(1), substring)
        }
    }

    fn how_many_times_impl(string : Vec<char>, substring : Vec<char>) -> (opt_k : Option<u32>)
        requires 
            substring.len() >= 1
        ensures 
            match opt_k {
                Some(k) => k as nat == how_many_times(string@, substring@),
                None => how_many_times(string@, substring@) > u32::MAX
            }
    {
        let mut k = 0u64;
        let mut current_string = string;
        while current_string.len() >= substring.len() 
            invariant 
                how_many_times(string@, substring@) == k + how_many_times(current_string@, substring@),
                k <= u32::MAX as u64,
                substring.len() >= 1
            decreases current_string.len(),
        {
            if (is_prefix(substring.clone(), current_string.clone())) {
                if (k >= u32::MAX as u64) {
                    current_string = current_string.split_off(1);
                    assert (how_many_times(string@, substring@) == k + 1 + how_many_times(current_string@, substring@));
                    return None;
                }
                k = k + 1;
            }
            current_string = current_string.split_off(1);
        }
        assert (how_many_times(current_string@, substring@) == 0) by {lemma_how_many_times_zero(current_string@, substring@)};
        return Some(k as u32);
    }
} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def how_many_times(string: str, substring: str) -> int:
    """ Find how many times a given substring can be found in the original string. Count overlaping cases.
    >>> how_many_times('', 'a')
    0
    >>> how_many_times('aaa', 'a')
    3
    >>> how_many_times('aaaa', 'aa')
    3
    """

*/

/*
### ENTRY POINT
how_many_times
*/

/*
### CANONICAL SOLUTION
    times = 0

    for i in range(len(string) - len(substring) + 1):
        if string[i:i+len(substring)] == substring:
            times += 1

    return times

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('', 'x') == 0
    assert candidate('xyxyxyx', 'x') == 4
    assert candidate('cacacacac', 'cac') == 4
    assert candidate('john doe', 'john') == 1

*/
