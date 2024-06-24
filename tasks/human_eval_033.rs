
/*
### ID
HumanEval/33
*/

/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

// This function counts the number of elements of `s` that are equal to `x`.
spec fn count<T>(s: Seq<T>, x: T) -> int
    decreases
        s.len()
{
    if s.len() == 0 {
        0
    }
    else {
        count(s.skip(1), x) + if s[0] == x { 1int } else { 0int }
    }
}

// This function defines what it means for two sequences to be
// permutations of each other: for every value `x`, each of the two
// sequences has the same number of instances of `x`.
spec fn permutes<T>(s1: Seq<T>, s2: Seq<T>) -> bool
{
    forall |x: T| count(s1, x) == count(s2, x)
}

// This lemma establishes the effect of an `update` operation on the
// result of a `count`. That is, it gives a closed-form
// (non-recursive) description of what happens to `count(s, x)` when
// `s` is updated to `s.update(i, v)`.
proof fn lemma_update_effect_on_count<T>(s: Seq<T>, i: int, v: T, x: T)
    requires
        0 <= i < s.len(),
    ensures
        count(s.update(i, v), x) ==
            if v == x && s[i] != x {
                count(s, x) + 1
            }
            else if v != x && s[i] == x {
                count(s, x) - 1
            }
            else {
                count(s, x)
            }
    decreases
        s.len()
{
    if s.len() == 0 {
        return;
    }
    if i == 0 {
        assert(s.update(i, v) =~= seq![v] + s.skip(1));
        assert(s.update(i, v).skip(1) =~= s.skip(1));
    }
    else {
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
    assert forall |x: T| #[trigger] count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x) by {
        lemma_update_effect_on_count(s, i, s[j], x);
        lemma_update_effect_on_count(s.update(i, s[j]), j, s[i], x);
    }
}

// This is the function we were asked to write.
fn sort_third(l: Vec<i32>) -> (l_prime: Vec<i32>)
    ensures
        l_prime.len() == l.len(),
        forall |i: int| 0 <= i < l.len() && i % 3 != 0 ==> l_prime[i] == l[i], // unchanged if index not divisible by three
        forall |i: int, j: int| 0 <= i < j < l.len() && i % 3 == 0 && j % 3 == 0 ==> l_prime[i] <= l_prime[j],
                                                                     // indexes divisible by three are ordered
        permutes(l_prime@, l@),                                      // new vec is a permutation of old vec
{
    let ghost old_l = l@;
    let l_len = l.len();
    let mut pos_being_set_to_smallest: usize = 0;
    let mut l_prime: Vec<i32> = l;

    // Iterate `pos_being_set_to_smallest` by 3 from 0 to `l_len`. Each time,
    // look for the smallest element at a position divisible by three in the
    // part of the vector at or past `pos_being_set_to_smallest`. Swap that
    // element with the one at `pos_being_set_to_smallest`.
    
    while pos_being_set_to_smallest < l_len
        invariant
            l_len == l.len() == l_prime.len(),
            pos_being_set_to_smallest % 3 == 0,
            forall |i: int| 0 <= i < l_len && i % 3 != 0 ==> l_prime[i] == l[i],
            permutes(l_prime@, l@),
            forall |i: int, j: int| 0 <= i < pos_being_set_to_smallest && i < j < l_len && i % 3 == 0 && j % 3 == 0
                ==> l_prime[i] <= l_prime[j],
    {
        // Iterate `pos_during_scan_for_smallest` by 3 from `pos_being_set_to_smallest`
        // to `l_len`. Keep track of the position of the smallest element found so far
        // in `pos_of_smallest_found_so_far`.
        
        let mut pos_of_smallest_found_so_far: usize = pos_being_set_to_smallest;
        let mut pos_during_scan_for_smallest: usize = pos_being_set_to_smallest;
        while pos_during_scan_for_smallest < l_len
            invariant
                l_len == l.len() == l_prime.len(),
                pos_being_set_to_smallest % 3 == 0,
                pos_during_scan_for_smallest % 3 == 0,
                pos_of_smallest_found_so_far % 3 == 0,
                pos_being_set_to_smallest <= pos_during_scan_for_smallest,
                pos_being_set_to_smallest <= pos_of_smallest_found_so_far < l_len,
                forall |i: int| 0 <= i < l_len && i % 3 != 0 ==> l_prime[i] == l[i],
                permutes(l_prime@, l@),
                forall |i: int| pos_being_set_to_smallest <= i < pos_during_scan_for_smallest && i % 3 == 0
                    ==> l_prime[pos_of_smallest_found_so_far as int] <= l_prime[i],
                forall |i: int, j: int| 0 <= i < pos_being_set_to_smallest && i < j < l_len && i % 3 == 0 && j % 3 == 0
                    ==> l_prime[i] <= l_prime[j],
        {
            if l_prime[pos_during_scan_for_smallest] < l_prime[pos_of_smallest_found_so_far] {
                pos_of_smallest_found_so_far = pos_during_scan_for_smallest;
            }
            pos_during_scan_for_smallest = pos_during_scan_for_smallest + 3;
        }

        // Invoke a lemma to show that swapping two elements, as we're
        // about to do, doesn't change the count of each element.

        proof {
            lemma_swapping_produces_a_permutation(l_prime@, pos_being_set_to_smallest as int,
                                                  pos_of_smallest_found_so_far as int);
        }

        // Swap the elements at positions `pos_being_set_to_smallest`
        // and `pos_of_smallest_found_so_far`.

        let v1 = l_prime[pos_being_set_to_smallest];
        let v2 = l_prime[pos_of_smallest_found_so_far];
        l_prime.set(pos_being_set_to_smallest, v2);
        l_prime.set(pos_of_smallest_found_so_far, v1);

        pos_being_set_to_smallest = pos_being_set_to_smallest + 3;
    }
    l_prime
}

} // verus!

fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def sort_third(l: list):
    """This function takes a list l and returns a list l' such that
    l' is identical to l in the indicies that are not divisible by three, while its values at the indicies that are divisible by three are equal
    to the values of the corresponding indicies of l, but sorted.
    >>> sort_third([1, 2, 3])
    [1, 2, 3]
    >>> sort_third([5, 6, 3, 4, 8, 9, 2])
    [2, 6, 3, 4, 8, 9, 5]
    """

*/

/*
### ENTRY POINT
sort_third
*/

/*
### CANONICAL SOLUTION
    l = list(l)
    l[::3] = sorted(l[::3])
    return l

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert tuple(candidate([1, 2, 3])) == tuple(sort_third([1, 2, 3]))
    assert tuple(candidate([5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10])) == tuple(sort_third([5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]))
    assert tuple(candidate([5, 8, -12, 4, 23, 2, 3, 11, 12, -10])) == tuple(sort_third([5, 8, -12, 4, 23, 2, 3, 11, 12, -10]))
    assert tuple(candidate([5, 6, 3, 4, 8, 9, 2])) == tuple([2, 6, 3, 4, 8, 9, 5])
    assert tuple(candidate([5, 8, 3, 4, 6, 9, 2])) == tuple([2, 8, 3, 4, 6, 9, 5])
    assert tuple(candidate([5, 6, 9, 4, 8, 3, 2])) == tuple([2, 6, 9, 4, 8, 3, 5])
    assert tuple(candidate([5, 6, 3, 4, 8, 9, 2, 1])) == tuple([2, 6, 3, 4, 8, 9, 5, 1])


*/

