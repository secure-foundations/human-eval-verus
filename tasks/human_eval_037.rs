/*
### ID
HumanEval/37
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

// code taken from sort_third (033)
spec fn count<T>(s: Seq<T>, x: T) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count(s.skip(1), x) + if s[0] == x {
            1int
        } else {
            0int
        }
    }
}

// This function defines what it means for two sequences to be
// permutations of each other: for every value `x`, each of the two
// sequences has the same number of instances of `x`.
spec fn permutes<T>(s1: Seq<T>, s2: Seq<T>) -> bool {
    forall|x: T| count(s1, x) == count(s2, x)
}

// This lemma establishes the effect of an `update` operation on the
// result of a `count`. That is, it gives a closed-form
// (non-recursive) description of what happens to `count(s, x)` when
// `s` is updated to `s.update(i, v)`.
proof fn lemma_update_effect_on_count<T>(s: Seq<T>, i: int, v: T, x: T)
    requires
        0 <= i < s.len(),
    ensures
        count(s.update(i, v), x) == if v == x && s[i] != x {
            count(s, x) + 1
        } else if v != x && s[i] == x {
            count(s, x) - 1
        } else {
            count(s, x)
        },
    decreases s.len(),
{
    if s.len() == 0 {
        return ;
    }
    if i == 0 {
        assert(s.update(i, v) =~= seq![v] + s.skip(1));
        assert(s.update(i, v).skip(1) =~= s.skip(1));
    } else {
        assert(s.update(i, v) =~= seq![s[0]] + s.skip(1).update(i - 1, v));
        assert(s.update(i, v).skip(1) =~= s.skip(1).update(i - 1, v));
        lemma_update_effect_on_count(s.skip(1), i - 1, v, x);
    }
}

// This lemma proves that if you swap elements `i` and `j` of sequence `s`,
// you get a permutation of `s`.
proof fn lemma_swapping_produces_a_permutation<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        permutes(s.update(i, s[j]).update(j, s[i]), s),
{
    assert forall|x: T| #[trigger] count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x) by {
        lemma_update_effect_on_count(s, i, s[j], x);
        lemma_update_effect_on_count(s.update(i, s[j]), j, s[i], x);
    }
}

#[verifier::loop_isolation(false)]
fn sort_pred(l: Vec<i32>, p: Vec<bool>) -> (l_prime: Vec<i32>)
    requires
        l.len() == p.len(),
    ensures
        l_prime.len() == l.len(),
        forall|i: int| 0 <= i < l.len() && !p[i] ==> l_prime[i] == l[i],
        forall|i: int, j: int|
            #![auto]
            0 <= i < j < l.len() && p[i] && p[j] ==> l_prime[i] <= l_prime[j],
        permutes(l_prime@, l@),
{
    let ghost old_l = l@;
    let l_len = l.len();
    let mut pos_replace: usize = 0;
    let mut l_prime: Vec<i32> = l;
    while pos_replace < l_len
        invariant
            l_len == l.len() == l_prime.len(),
            forall|i: int| 0 <= i < l_len && !p[i] ==> l_prime[i] == l[i],
            permutes(l_prime@, l@),
            forall|i: int, j: int|
                #![auto]
                0 <= i < pos_replace && i < j < l_len && p[i] && p[j] ==> l_prime[i] <= l_prime[j],
    {
        if p[pos_replace] {
            let mut pos_cur: usize = pos_replace;
            let mut pos: usize = pos_replace;
            while pos < l_len
                invariant
                    l_len == l.len() == l_prime.len(),
                    pos_replace <= pos,
                    pos_replace <= pos_cur < l_len,
                    p[pos_replace as int],
                    p[pos_cur as int],
                    forall|i: int| 0 <= i < l_len && !p[i] ==> l_prime[i] == l[i],
                    permutes(l_prime@, l@),
                    forall|i: int|
                        #![auto]
                        pos_replace <= i < pos && p[i] ==> l_prime[pos_cur as int] <= l_prime[i],
                    forall|i: int, j: int|
                        #![auto]
                        0 <= i < pos_replace && i < j < l_len && p[i] && p[j] ==> l_prime[i]
                            <= l_prime[j],
            {
                if p[pos] && l_prime[pos] < l_prime[pos_cur] {
                    pos_cur = pos;
                }
                pos = pos + 1;
            }
            proof {
                lemma_swapping_produces_a_permutation(l_prime@, pos_replace as int, pos_cur as int);
            }
            let v1 = l_prime[pos_replace];
            let v2 = l_prime[pos_cur];
            l_prime.set(pos_replace, v2);
            l_prime.set(pos_cur, v1);
        }
        pos_replace = pos_replace + 1;
    }
    l_prime
}

#[verifier::loop_isolation(false)]
fn sort_even(l: Vec<i32>) -> (result: Vec<i32>)
    ensures
        l.len() == result.len(),
        permutes(result@, l@),
        forall|i: int| 0 <= i < l.len() && i % 2 == 1 ==> result[i] == l[i],
        forall|i: int, j: int|
            #![auto]
            0 <= i < j < l.len() && i % 2 == 0 && j % 2 == 0 ==> result[i] <= result[j],
{
    let mut p: Vec<bool> = vec![];
    for i in 0..l.len()
        invariant
            p.len() == i,
            forall|j: int| 0 <= j < i ==> p[j] == (j % 2 == 0),
    {
        p.push(i % 2 == 0);
    }
    assert(forall|i: int, j: int|
        #![auto]
        0 <= i < j < l.len() && i % 2 == 0 && j % 2 == 0 ==> p[i] && p[j]);
    sort_pred(l, p)
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def sort_even(l: list):
    """This function takes a list l and returns a list l' such that
    l' is identical to l in the odd indicies, while its values at the even indicies are equal
    to the values of the even indicies of l, but sorted.
    >>> sort_even([1, 2, 3])
    [1, 2, 3]
    >>> sort_even([5, 6, 3, 4])
    [3, 6, 5, 4]
    """

*/

/*
### ENTRY POINT
sort_even
*/

/*
### CANONICAL SOLUTION
    evens = l[::2]
    odds = l[1::2]
    evens.sort()
    ans = []
    for e, o in zip(evens, odds):
        ans.extend([e, o])
    if len(evens) > len(odds):
        ans.append(evens[-1])
    return ans

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert tuple(candidate([1, 2, 3])) == tuple([1, 2, 3])
    assert tuple(candidate([5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10])) == tuple([-10, 3, -5, 2, -3, 3, 5, 0, 9, 1, 123])
    assert tuple(candidate([5, 8, -12, 4, 23, 2, 3, 11, 12, -10])) == tuple([-12, 8, 3, 4, 5, 2, 12, 11, 23, -10])


*/
