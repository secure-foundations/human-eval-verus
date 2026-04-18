/*
### ID
HumanEval/120
*/
/*
### VERUS BEGIN
*/
use vstd::arithmetic::div_mod::*;
use vstd::calc;
use vstd::multiset::{lemma_update_same, Multiset};
use vstd::prelude::*;
use vstd::prelude::*;
use vstd::seq_lib::{lemma_multiset_commutative, to_multiset_remove};

verus! {

proof fn swap_preserves_multiset_helper(s: Seq<i32>, i: int, j: int)
    requires
        0 <= i < j < s.len(),
    ensures
        (s.take(j + 1)).to_multiset() =~= s.take(i).to_multiset().add(
            s.subrange(i + 1, j).to_multiset(),
        ).insert(s.index(j)).insert(s.index(i)),
{
    let fst = s.take(i);
    let snd = s.subrange(i + 1, j);

    assert((s.take(j + 1)).to_multiset() =~= fst.to_multiset().insert(s.index(i)).add(
        snd.to_multiset().insert(s.index(j)),
    )) by {
        assert(s.take(i + 1).to_multiset() =~= fst.to_multiset().insert(s.index(i))) by {
            fst.to_multiset_ensures();
            assert(fst.push(s.index(i)) =~= s.take(i + 1));
        }
        assert(s.subrange(i + 1, j + 1).to_multiset() =~= snd.to_multiset().insert(s.index(j))) by {
            snd.to_multiset_ensures();
            assert(snd.push(s.index(j)) =~= s.subrange(i + 1, j + 1));
        }
        lemma_multiset_commutative(s.take(i + 1), s.subrange(i + 1, j + 1));
        assert(s.take(i + 1) + s.subrange(i + 1, j + 1) =~= s.take(j + 1));
    }
}

proof fn swap_preserves_multiset(s1: Seq<i32>, s2: Seq<i32>, i: int, j: int)
    requires
        0 <= i < j < s1.len() == s2.len(),
        forall|x: int| 0 <= x < s1.len() && x != i && x != j ==> s1.index(x) == s2.index(x),
        s1.index(i) == s2.index(j),
        s1.index(j) == s2.index(i),
    ensures
        s1.to_multiset() == s2.to_multiset(),
{
    calc! {
        (==)
        s1.to_multiset(); {
            lemma_multiset_commutative(s1.take(j + 1), s1.skip(j + 1));
            assert(s1 =~= s1.take(j + 1) + s1.skip(j + 1));
        }
        s1.take(j + 1).to_multiset().add(s1.skip(j + 1).to_multiset()); {
            assert(s1.take(j + 1).to_multiset() =~= s2.take(j + 1).to_multiset()) by {
                assert(s1.take(i) == s2.take(i));
                assert(s1.subrange(i + 1, j) =~= (s2.subrange(i + 1, j)));
                swap_preserves_multiset_helper(s1, i, j);
                swap_preserves_multiset_helper(s2, i, j);
            }
            assert(s1.skip(j + 1).to_multiset() =~= s2.skip(j + 1).to_multiset()) by {
                assert(s1.skip(j + 1) =~= s2.skip(j + 1));
            }
        }
        s2.take(j + 1).to_multiset().add(s2.skip(j + 1).to_multiset()); {
            lemma_multiset_commutative(s2.take(j + 1), s2.skip(j + 1));
            assert(s2 =~= s2.take(j + 1) + s2.skip(j + 1));
        }
        s2.to_multiset();
    }
}

fn sort_seq(s: &Vec<i32>) -> (ret: Vec<i32>)
    ensures
//forall|i: int, j: int| 0 <= i < j < ret@.len() ==> ret@.index(i) <= ret@.index(j),

        sorted(ret@),
        ret@.len() == s@.len(),
        s@.to_multiset() == ret@.to_multiset(),
{
    let mut sorted = s.clone();
    let mut i: usize = 0;
    while i < sorted.len()
        invariant
            i <= sorted.len(),
            forall|j: int, k: int| 0 <= j < k < i ==> sorted@.index(j) <= sorted@.index(k),
            s@.to_multiset() == sorted@.to_multiset(),
            forall|j: int, k: int|
                0 <= j < i <= k < sorted@.len() ==> sorted@.index(j) <= sorted@.index(k),
            sorted@.len() == s@.len(),
        decreases sorted.len() - i,
    {
        let mut min_index: usize = i;
        let mut j: usize = i + 1;
        while j < sorted.len()
            invariant
                i <= min_index < j <= sorted.len(),
                forall|k: int| i <= k < j ==> sorted@.index(min_index as int) <= sorted@.index(k),
            decreases sorted.len() - j,
        {
            if sorted[j] < sorted[min_index] {
                min_index = j;
            }
            j += 1;
        }
        if min_index != i {
            let ghost old_sorted = sorted@;
            let curr_val = sorted[i];
            let min_val = sorted[min_index];
            sorted.set(i, min_val);

            sorted.set(min_index, curr_val);
            proof {
                swap_preserves_multiset(old_sorted, sorted@, i as int, min_index as int);
                assert(old_sorted.to_multiset() =~= sorted@.to_multiset());
            }
        }
        i += 1;
    }
    sorted
}

spec fn sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s.index(i) <= s.index(j)
}

spec fn is_sorted_from_base_seq(b: Seq<i32>, s: Seq<i32>) -> bool {
    sorted(s) && b.len() == s.len() && b.to_multiset() == s.to_multiset()
}

proof fn first_element_sorted_array_is_minimum(s: Seq<i32>)
    requires
        s.len() > 0,
        sorted(s),
    ensures
        forall|i: int| 0 <= i < s.len() ==> s[0] <= #[trigger] s[i],
{
}

proof fn lemma_exist_index_seq_multiset_contains(s: Seq<i32>, el: i32)
    ensures
        s.contains(el) == (exists|i: int| (0 <= i < s.len()) && (#[trigger] s[i] == el)),
{
}

proof fn lemma_remove_first_element_removes_from_multiset(s1: Seq<i32>)
    requires
        s1.len() > 0,
    ensures
        (s1.drop_first().to_multiset() == s1.to_multiset().remove(s1[0])),
{
    to_multiset_remove(s1, 0);
    assert(s1.remove(0) =~= s1.drop_first());
}

proof fn lemma_if_two_seqs_same_muiltisets_and_one_contain_one_element_the_other_also(
    s1: Seq<i32>,
    s2: Seq<i32>,
    el: i32,
)
    requires
        s1.to_multiset() == s2.to_multiset(),
    ensures
        s1.contains(el) == s2.contains(el),
{
    assert(s1.to_multiset().count(el) == s2.to_multiset().count(el));
    assert(s1.contains(el) <==> s1.to_multiset().count(el) > 0) by {
        s1.to_multiset_ensures();
    }
    assert(s2.contains(el) <==> s2.to_multiset().count(el) > 0) by {
        s2.to_multiset_ensures();
    }
}

proof fn sorted_unique_lemma(s1: Seq<i32>, s2: Seq<i32>)
    requires
        sorted(s1),
        sorted(s2),
        s1.len() == s2.len(),
        s1.to_multiset() == s2.to_multiset(),
    ensures
        s1 == s2,
    decreases s1.len(),
{
    if s1.len() == 0 {
        return ;
    }
    assert(s2.len() > 0);

    let t1 = s1.drop_first();
    let t2 = s2.drop_first();
    let t1h = s1.subrange(0, 1);
    let t2h = s2.subrange(0, 1);

    assert(s1[0] == t1h[0]);
    assert(s2[0] == t2h[0]);

    first_element_sorted_array_is_minimum(s1);
    first_element_sorted_array_is_minimum(s2);

    if (s1[0] < s2[0]) {
        assert(forall|i: int| 0 <= i < s2.len() ==> s2[0] <= #[trigger] s2[i]);
        assert(forall|i: int| 0 <= i < s2.len() ==> s1[0] < #[trigger] s2[i]);
        assert(s1.contains(s1[0]));
        assert(s2.contains(s2[0]));
        lemma_if_two_seqs_same_muiltisets_and_one_contain_one_element_the_other_also(s1, s2, s1[0]);
        lemma_if_two_seqs_same_muiltisets_and_one_contain_one_element_the_other_also(s1, s2, s2[0]);
        assert(exists|i: int| 0 <= i < s2.len() ==> s2[i] == s1[0]);
        assert(false);
    }
    if (s2[0] < s1[0]) {
        assert(forall|i: int| 0 <= i < s1.len() ==> s1[0] <= #[trigger] s1[i]);
        assert(forall|i: int| 0 <= i < s1.len() ==> s2[0] < #[trigger] s1[i]);
        assert(s1.contains(s1[0]));
        assert(s2.contains(s2[0]));
        lemma_if_two_seqs_same_muiltisets_and_one_contain_one_element_the_other_also(s1, s2, s1[0]);
        lemma_if_two_seqs_same_muiltisets_and_one_contain_one_element_the_other_also(s1, s2, s2[0]);
        assert(exists|i: int| 0 <= i < s1.len() ==> s1[i] == s2[0]);
        assert(false);
    }
    assert(s1[0] == s2[0]);
    assert(sorted(t1));
    assert(sorted(t2));

    lemma_remove_first_element_removes_from_multiset(s1);
    lemma_remove_first_element_removes_from_multiset(s2);
    assert(t1.to_multiset() == s1.to_multiset().remove(s1[0]));
    assert(t2.to_multiset() == s2.to_multiset().remove(s2[0]));
    assert(t1.to_multiset() == t2.to_multiset());

    sorted_unique_lemma(t1, t2);
    assert(t1 == t2);
    assert(s1 == t1h + t1);
    assert(s2 == t2h + t2);
    assert(s1 == s2);
}

fn maximum(v: Vec<i32>, k: usize) -> (o: Vec<i32>)
    requires
        k <= v.len(),
    ensures
        sorted(o@),
        (o@.len() == k as int),
        exists|vs: Seq<i32>|
            {
                &&& #[trigger] is_sorted_from_base_seq(v@, vs)
                &&& o@ == vs.subrange(vs.len() - k, vs.len() as int)
            },
{
    let vs = sort_seq(&v);
    assert(is_sorted_from_base_seq(v@, vs@));

    let mut r: Vec<i32> = Vec::with_capacity(k);
    let mut ind = vs.len() - k;
    while (ind < vs.len())
        invariant
            0 <= vs.len() - k <= ind <= vs.len(),
            sorted(vs@),
            sorted(r@),
            r@.len() == ind - (vs.len() - k),
            r@ == vs@.subrange(vs.len() - k, ind as int),
        decreases vs.len() - ind,
    {
        r.push(vs[ind]);
        ind += 1;
    }
    r
}

fn static_checks() {
    let v = vec![-3, -4, 5];
    let m2 = maximum(v, 2);
    let e2 = vec![-3, 5];
    let e3 = vec![-4, -3, 5];

    assert(m2@ == e2@) by {
        assert(sorted(e3@));
        assert(v.len() == e3.len());
        assert(v[0] == e3[1]);
        assert(v[1] == e3[0]);
        swap_preserves_multiset(v@, e3@, 0, 1);
        assert(v@.to_multiset() == e3@.to_multiset());
        assert(is_sorted_from_base_seq(v@, e3@));

        let s = choose|vs: Seq<i32>|
            {
                &&& #[trigger] is_sorted_from_base_seq(v@, vs)
                &&& m2@ == vs.subrange(vs.len() - 2, vs.len() as int)
            };
        assert(is_sorted_from_base_seq(v@, s));
        sorted_unique_lemma(e3@, s);
        assert(e3@ == s);
        assert(m2@ == s.subrange(s.len() - 2, s.len() as int));
        assert(m2@ == e3@.subrange(e3@.len() - 2, e3@.len() as int));
        assert(e3@.subrange(1, 3) == e2@);
        assert(m2@ == e2@);
    }

}

} // verus!
fn main() {
    assert!(maximum(vec![-3, -4, 5], 3) == vec![-4, -3, 5]);
    assert!(maximum(vec![-3, -4, 5], 2) == vec![-3, 5]);
    assert!(maximum(vec![4, -4, 4], 2) == vec![4, 4]);
    assert!(maximum(vec![-3, 2, 1, 2, -1, -2, 1], 1) == vec![2]);
    assert!(maximum(vec![123, -123, 20, 0, 1, 2, -3], 3) == vec![2, 20, 123]);
    assert!(maximum(vec![-123, 20, 0, 1, 2, -3], 4) == vec![0, 1, 2, 20]);
    assert!(maximum(vec![5, 15, 0, 3, -13, -8, 0], 7) == vec![-13, -8, 0, 0, 3, 5, 15]);
    assert!(maximum(vec![-1, 0, 2, 5, 3, -10], 2) == vec![3, 5]);
    assert!(maximum(vec![1, 0, 5, -7], 1) == vec![5]);
    assert!(maximum(vec![4, -4], 2) == vec![-4, 4]);
    assert!(maximum(vec![-10, 10], 2) == vec![-10, 10]);
    assert!(maximum(vec![1, 2, 3, -23, 243, -400, 0], 0) == vec![]);
}

/*
### VERUS END
*/

/*
### PROMPT

def maximum(arr, k):
    """
    Given an array arr of integers and a positive integer k, return a sorted list
    of length k with the maximum k numbers in arr.

    Example 1:

        Input: arr = [-3, -4, 5], k = 3
        Output: [-4, -3, 5]

    Example 2:

        Input: arr = [4, -4, 4], k = 2
        Output: [4, 4]

    Example 3:

        Input: arr = [-3, 2, 1, 2, -1, -2, 1], k = 1
        Output: [2]

    Note:
        1. The length of the array will be in the range of [1, 1000].
        2. The elements in the array will be in the range of [-1000, 1000].
        3. 0 <= k <= len(arr)
    """

*/

/*
### ENTRY POINT
maximum
*/

/*
### CANONICAL SOLUTION
    if k == 0:
        return []
    arr.sort()
    ans = arr[-k:]
    return ans

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([-3, -4, 5], 3) == [-4, -3, 5]
    assert candidate([4, -4, 4], 2) == [4, 4]
    assert candidate([-3, 2, 1, 2, -1, -2, 1], 1) == [2]
    assert candidate([123, -123, 20, 0 , 1, 2, -3], 3) == [2, 20, 123]
    assert candidate([-123, 20, 0 , 1, 2, -3], 4) == [0, 1, 2, 20]
    assert candidate([5, 15, 0, 3, -13, -8, 0], 7) == [-13, -8, 0, 0, 3, 5, 15]
    assert candidate([-1, 0, 2, 5, 3, -10], 2) == [3, 5]
    assert candidate([1, 0, 5, -7], 1) == [5]
    assert candidate([4, -4], 2) == [-4, 4]
    assert candidate([-10, 10], 2) == [-10, 10]

    # Check some edge cases that are easy to work out by hand.
    assert candidate([1, 2, 3, -23, 243, -400, 0], 0) == []


*/
