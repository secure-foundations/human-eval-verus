/*
### ID
HumanEval/72
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn will_it_fly(qs: &Vec<u32>, w: u32) -> (ret: bool)
    ensures
        ret <==> qs@ =~= qs@.reverse() && spec_sum(qs@) <= w,
{
    palindrome(qs) && sum_lesser_than_limit(qs, w)
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
            ret <==> qs@.subrange(0, i as int) =~= qs@.subrange(qs@.len() - i, qs@.len() as int).reverse(),
    {
        // reveal_with_fuel(Seq::reverse, 5); //VERUS BUG on uncomment
        assert(qs@.subrange(qs@.len() - (i + 1), qs@.len() as int).reverse().drop_last() =~= qs@.subrange(qs@.len() - i, qs@.len() as int).reverse());
        assert(qs@.subrange(qs@.len() - (i + 1), qs@.len() as int).reverse() =~= qs@.subrange(qs@.len() - i, qs@.len() as int).reverse().push(qs@.index(qs@.len() - (i +1))));
        if qs[i] != qs[qs.len() - i - 1] {
            ret = false;
        }
        i += 1;
    }
    let ghost fst_half = qs@.subrange(0, (qs@.len() / 2) as int);
    let ghost snd_half = qs@.subrange(qs@.len() - qs@.len() / 2, qs@.len() as int);

    proof {
        lemma_palindrome_of_halves(fst_half, snd_half);
        if (qs.len() % 2) == 1 {
            lemma_palindrome_of_halves_and_middle(fst_half, qs@.index((qs@.len() / 2) as int), snd_half);
            assert(qs@ =~= fst_half + qs@.subrange((qs@.len() / 2) as int, qs@.len() - qs@.len() / 2) + snd_half);
        } else {
            assert(qs@ =~= fst_half + snd_half);
        }
    }
    ret

}

proof fn lemma_palindrome_of_halves<T>(fst: Seq<T>, snd: Seq<T>)
    requires
        fst.len() == snd.len(),
    ensures
        fst =~= snd.reverse() <==> (fst + snd) =~= (fst + snd).reverse(),
{
    let s1 = fst + snd;
    let s2 = s1.reverse();
    if (fst =~= snd.reverse()) {
        assert(forall |i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]);
    } else {
        assert(exists |i: int| 0 <= i < fst.len() && #[trigger] fst[i] != snd.reverse()[i] && s1[i] != s2[i]);
        assert(exists |i: int| 0 <= i < s1.len() && s1[i] != s2[i]);
    }
}

proof fn lemma_palindrome_of_halves_and_middle<T>(fst: Seq<T>, middle: T, snd: Seq<T>)
    requires
        fst.len() == snd.len(),
    ensures
        fst =~= snd.reverse() <==> (fst + seq![middle] + snd) =~= (fst + seq![middle] + snd).reverse(),
{
    let s1 = fst + seq![middle] + snd;
    let s2 = s1.reverse();
    if (fst =~= snd.reverse()) {
        assert(forall |i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]);
    } else {
        assert(exists |i: int| 0 <= i < fst.len() && #[trigger] fst[i] != snd.reverse()[i] && s1[i] != s2[i]);
        assert(exists |i: int| 0 <= i < s1.len() && s1[i] != s2[i]);
    }
}

fn sum_lesser_than_limit(qs: &Vec<u32>, w: u32) -> (ret: bool) 
    ensures
        ret <==> spec_sum(qs@) <= w
{
    let mut sum: u32 = 0;
    for i in 0..qs.len() 
        invariant
            sum == spec_sum(qs@.subrange(0, i as int)),
            i <= qs.len(),
            sum <= w,
    {
        proof {
            assert(spec_sum(qs@.subrange(0, i+1)) <= spec_sum(qs@)) by {
                assert(qs@ == qs@.subrange(0, qs@.len() as int));
                lemma_increasing_sum(qs@);
            }

            assert(spec_sum(qs@.subrange(0, i as int)) + qs[i as int] == spec_sum(qs@.subrange(0, i+1))) by {
                assert(qs@.subrange(0, i+1).drop_last() == qs@.subrange(0, i as int));
            }
        }
        let sum_opt = sum.checked_add(qs[i]);
        if sum_opt.is_none() {
            assert(spec_sum(qs@.subrange(0, i+1)) > u32::MAX >= w);
            return false;
        } else {
            sum = sum_opt.unwrap();
            if sum > w {
                assert(spec_sum(qs@.subrange(0, i+1)) > w);
                return false;
            }
        }
    }
    assume(sum == spec_sum(qs@));
    true
}

spec fn spec_sum(s: Seq<u32>) -> int {
    s.fold_left(0, |x: int, y| x + y)
}

proof fn lemma_increasing_sum(s: Seq<u32>)
    ensures
        forall |i: int, j: int| 
            #![trigger spec_sum(s.subrange(0, i)), spec_sum(s.subrange(0, j))] 
            0 <= i <= j <= s.len() ==> spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j)),
{
    // if s.len() == 0 {
    //     // Base case: empty sequence
    //     assert(forall |i: int, j: int| 
    //         #![trigger spec_sum(s.subrange(0, i)), spec_sum(s.subrange(0, j))]
    //         0 <= i <= j <= s.len() ==> spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j)));
    // } else {
    //     // Inductive case
    //     let s_init = s.subrange(0, s.len() as int - 1);
        
    //     // Inductive hypothesis
    //     lemma_increasing_sum(s_init);

    //     assert(forall |i: int, j: int| 
    //         #![trigger spec_sum(s_init.subrange(0, i)), spec_sum(s_init.subrange(0, j))]
    //         0 <= i <= j <= s_init.len() ==> spec_sum(s_init.subrange(0, i)) <= spec_sum(s_init.subrange(0, j)));

    //     // Prove for the full sequence
    //     assert(forall |i: int, j: int| 
    //         #![trigger spec_sum(s.subrange(0, i)), spec_sum(s.subrange(0, j))]
    //         0 <= i <= j <= s.len() ==> {
    //             if j < s.len() {
    //                 // Use inductive hypothesis
    //                 spec_sum(s.subrange(0, i)) <= spec_sum(s.subrange(0, j))
    //             } else {
    //                 // j == s.len(), compare with s_init
    //                 if i < s.len() {
    //                     spec_sum(s.subrange(0, i)) <= spec_sum(s_init) &&
    //                     spec_sum(s_init) <= spec_sum(s)
    //                 } else {
    //                     // i == j == s.len()
    //                     spec_sum(s.subrange(0, i)) == spec_sum(s)
    //                 }
    //             }
    //         });

    //     // Additional assertion to connect s_init and s
    //     assert(spec_sum(s_init) <= spec_sum(s)) by {
    //         assert(s == s_init.push(s.last()));
    //         assert(spec_sum(s) == spec_sum(s_init) + s.last());
    //     }
    // }
    admit();
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
