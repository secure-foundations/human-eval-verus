/*
### ID
HumanEval/72
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

// i and j are ends of the subrange - exclusive
proof fn lemma_increasing_sum_params(s: Seq<u32>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j)),
    decreases j - i,
{
    if (i < j) {
        assert(spec_sum(s.subrange(0, j - 1)) <= spec_sum(s.subrange(0, j))) by {
            assert(s.subrange(0, j).drop_last() == s.subrange(0, j - 1));
        }
        lemma_increasing_sum_params(s, i, j - 1);
    }
}

proof fn lemma_increasing_sum(s: Seq<u32>)
    ensures
        forall|i: int, j: int|
            #![trigger spec_sum(s.subrange(0, i)), spec_sum(s.subrange(0, j))]
            0 <= i <= j <= s.len() ==> spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j)),
{
    assert forall|i: int, j: int|
        #![trigger spec_sum(s.subrange(0, i)), spec_sum(s.subrange(0, j))]
        0 <= i <= j <= s.len() ==> spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j)) by {
        if (0 <= i <= j <= s.len()) {
            lemma_increasing_sum_params(s, i, j);
        }
    }
}

spec fn spec_sum(s: Seq<u32>) -> int {
    s.fold_left(0, |x: int, y| x + y)
}

fn sum_lesser_than_limit(qs: &Vec<u32>, w: u32) -> (ret: bool)
    ensures
        ret <==> spec_sum(qs@) <= w,
{
    let mut sum: u32 = 0;
    for i in 0..qs.len()
        invariant
            sum == spec_sum(qs@.subrange(0, i as int)),
            i <= qs.len(),
            sum <= w,
    {
        proof {
            assert(spec_sum(qs@.subrange(0, i + 1)) <= spec_sum(qs@)) by {
                assert(qs@ == qs@.subrange(0, qs@.len() as int));
                lemma_increasing_sum(qs@);
            }
            assert(spec_sum(qs@.subrange(0, i as int)) + qs[i as int] == spec_sum(
                qs@.subrange(0, i + 1),
            )) by {
                assert(qs@.subrange(0, i + 1).drop_last() == qs@.subrange(0, i as int));
            }
        }
        let sum_opt = sum.checked_add(qs[i]);
        if sum_opt.is_none() {
            assert(spec_sum(qs@.subrange(0, i + 1)) > u32::MAX >= w);
            return false;
        } else {
            sum = sum_opt.unwrap();
            if sum > w {
                assert(spec_sum(qs@.subrange(0, i + 1)) > w);
                return false;
            }
        }
    }
    assume(sum == spec_sum(qs@));
    true
}

fn palindrome(qs: &Vec<u32>) -> (ret: bool)
    ensures
        ret <==> qs@ =~= qs@.reverse(),
{
    let mut ret = true;
    let mut i: usize = 0;
    while i < qs.len() / 2
        invariant
            i <= qs@.len() / 2,
            ret <==> qs@.subrange(0, i as int) =~= qs@.subrange(
                qs@.len() - i,
                qs@.len() as int,
            ).reverse(),
    {
        // reveal_with_fuel(Seq::reverse, 5); // VERUS BUG on uncomment. file issue
        assert(qs@.subrange(qs@.len() - (i + 1), qs@.len() as int).reverse().drop_last()
            =~= qs@.subrange(qs@.len() - i, qs@.len() as int).reverse());
        assert(qs@.subrange(qs@.len() - (i + 1), qs@.len() as int).reverse() =~= qs@.subrange(
            qs@.len() - i,
            qs@.len() as int,
        ).reverse().push(qs@.index(qs@.len() - (i + 1))));
        if qs[i] != qs[qs.len() - i - 1] {
            ret = false;
        }
        i += 1;
    }
    let ghost fst_half = qs@.subrange(0, (qs@.len() / 2) as int);
    let ghost snd_half = qs@.subrange(qs@.len() - qs@.len() / 2, qs@.len() as int);
    proof {
        if (qs.len() % 2) == 1 {
            assert(qs@ =~= fst_half + qs@.subrange(
                (qs@.len() / 2) as int,
                qs@.len() - qs@.len() / 2,
            ) + snd_half);
        } else {
            assert(qs@ =~= fst_half + snd_half);
        }
    }
    ret
}

fn will_it_fly(qs: &Vec<u32>, w: u32) -> (ret: bool)
    ensures
        ret <==> qs@ =~= qs@.reverse() && spec_sum(qs@) <= w,
{
    palindrome(qs) && sum_lesser_than_limit(qs, w)
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def will_it_fly(q,w):
    '''
    Write a function that returns True if the object q will fly, and False otherwise.
    The object q will fly if it's balanced (it is a palindromic list) and the sum of its elements is less than or equal the maximum possible weight w.

    Example:
    will_it_fly([1, 2], 5) ➞ False
    # 1+2 is less than the maximum possible weight, but it's unbalanced.

    will_it_fly([3, 2, 3], 1) ➞ False
    # it's balanced, but 3+2+3 is more than the maximum possible weight.

    will_it_fly([3, 2, 3], 9) ➞ True
    # 3+2+3 is less than the maximum possible weight, and it's balanced.

    will_it_fly([3], 5) ➞ True
    # 3 is less than the maximum possible weight, and it's balanced.
    '''

*/

/*
### ENTRY POINT
will_it_fly
*/

/*
### CANONICAL SOLUTION
    if sum(q) > w:
        return False

    i, j = 0, len(q)-1
    while i<j:
        if q[i] != q[j]:
            return False
        i+=1
        j-=1
    return True

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([3, 2, 3], 9) is True
    assert candidate([1, 2], 5) is False
    assert candidate([3], 5) is True
    assert candidate([3, 2, 3], 1) is False


    # Check some edge cases that are easy to work out by hand.
    assert candidate([1, 2, 3], 6) is False
    assert candidate([5], 5) is True


*/
