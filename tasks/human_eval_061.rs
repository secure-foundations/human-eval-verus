/*
### ID
HumanEval/61
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

// say the return value is (x, b), x = number of '(' - number of ')', b = whether x ever dipped below 0
spec fn spec_bracketing_helper(brackets: Seq<char>) -> (int, bool) {
    brackets.fold_left(
        (0, true),
        |p: (int, bool), c|
            {
                let (x, b) = p;
                match (c) {
                    '(' => (x + 1, b),
                    ')' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
    )
}

spec fn spec_bracketing(brackets: Seq<char>) -> bool {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}

fn correct_bracketing(brackets: &str) -> (ret: bool)
    requires
        brackets@.len() <= i32::MAX,
        -brackets@.len() >= i32::MIN,
    ensures
        ret <==> spec_bracketing(brackets@),
{
    let mut i = 0;
    let mut b = true;
    let mut stack_size: i32 = 0;

    while i < brackets.unicode_len()
        invariant
            (stack_size as int, b) == spec_bracketing_helper(brackets@.subrange(0, i as int)),
            stack_size <= i <= brackets@.len() <= i32::MAX,
            stack_size >= -i >= -brackets@.len() >= i32::MIN,
        decreases brackets@.len() - i,
    {
        let c = brackets.get_char(i);
        let ghost prev = spec_bracketing_helper(brackets@.subrange(0, i as int));
        if (c == '(') {
            stack_size += 1;
        } else if (c == ')') {
            b = b && stack_size > 0;
            stack_size -= 1;
        }
        assert(brackets@.subrange(0, i + 1 as int).drop_last() =~= brackets@.subrange(0, i as int));
        i += 1;
    }
    assert(brackets@ =~= brackets@.subrange(0, i as int));
    b && stack_size == 0
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def correct_bracketing(brackets: str):
    """ brackets is a string of "(" and ")".
    return True if every opening bracket has a corresponding closing bracket.

    >>> correct_bracketing("(")
    False
    >>> correct_bracketing("()")
    True
    >>> correct_bracketing("(()())")
    True
    >>> correct_bracketing(")(()")
    False
    """

*/

/*
### ENTRY POINT
correct_bracketing
*/

/*
### CANONICAL SOLUTION
    depth = 0
    for b in brackets:
        if b == "(":
            depth += 1
        else:
            depth -= 1
        if depth < 0:
            return False
    return depth == 0

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate("()")
    assert candidate("(()())")
    assert candidate("()()(()())()")
    assert candidate("()()((()()())())(()()(()))")
    assert not candidate("((()())))")
    assert not candidate(")(()")
    assert not candidate("(")
    assert not candidate("((((")
    assert not candidate(")")
    assert not candidate("(()")
    assert not candidate("()()(()())())(()")
    assert not candidate("()()(()())()))()")


*/
