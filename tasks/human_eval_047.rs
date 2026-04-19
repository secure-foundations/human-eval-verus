use std::ops::Mul;

/*
HumanEval/47
*/
/*
### VERUS BEGIN
*/
use vstd::arithmetic::div_mod::*;
use vstd::calc;
use vstd::multiset::{lemma_update_same, Multiset};
use vstd::prelude::*;
use vstd::seq_lib::{lemma_multiset_commutative, to_multiset_remove};

verus! {

// From human_eval_070
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

proof fn lemma_remove_first_element_removes_from_multiset(s1: Seq<i32>)
    requires
        s1.len() > 0,
    ensures
        (s1.drop_first().to_multiset() == s1.to_multiset().remove(s1[0])),
{
    to_multiset_remove(s1, 0);
    assert(s1.remove(0) =~= s1.drop_first());
}

proof fn lemma_seq_to_multiset_implies_containment(s1: Seq<i32>, s2: Seq<i32>, el: i32)
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
        lemma_seq_to_multiset_implies_containment(s1, s2, s1[0]);
        lemma_seq_to_multiset_implies_containment(s1, s2, s2[0]);
        assert(exists|i: int| 0 <= i < s2.len() ==> s2[i] == s1[0]);
        assert(false);
    }
    if (s2[0] < s1[0]) {
        assert(forall|i: int| 0 <= i < s1.len() ==> s1[0] <= #[trigger] s1[i]);
        assert(forall|i: int| 0 <= i < s1.len() ==> s2[0] < #[trigger] s1[i]);
        assert(s1.contains(s1[0]));
        assert(s2.contains(s2[0]));
        lemma_seq_to_multiset_implies_containment(s1, s2, s1[0]);
        lemma_seq_to_multiset_implies_containment(s1, s2, s2[0]);
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

proof fn all_medians_on_sorted_are_equal(b: Seq<i32>, s1: Seq<i32>, s2: Seq<i32>)
    requires
        is_sorted_from_base_seq(b, s1),
        is_sorted_from_base_seq(b, s2),
    ensures
        double_median_sorted(s1) == double_median_sorted(s2),
{
    sorted_unique_lemma(s1, s2);
}

spec fn double_median_sorted(c: Seq<i32>) -> Option<i64>
    recommends
        sorted(c),
{
    if c.len() == 0 {
        None
    } else if c.len() % 2 == 1 {
        Some((c[(c.len() - 1) / 2] * 2) as i64)
    } else {
        let l: i32 = c[((c.len() - 1) / 2) as int];
        let r: i32 = c[(c.len() / 2) as int];
        Some((l as i64 + r as i64) as i64)
    }
}

spec fn get_sorted(c: Seq<i32>) -> (v: Seq<i32>) {
    choose|v: Seq<i32>| is_sorted_from_base_seq(c, v)
}

spec fn double_median(c: Seq<i32>) -> Option<i64> {
    if c.len() == 0 {
        None
    } else {
        let v = get_sorted(c);
        double_median_sorted(v)
    }
}

//This solution has a few important design considerations:
//- The median of a sequence of integers is generally a float value when the number of elements is even.
//- Since floating-point numbers are not supported, this implementation returns twice the median, which is always an integer.
//The median is computed as follows:
//- If the length is odd: the median is the middle element of the sorted sequence (this function returns twice that value).
//- If the length is even: the median is the average of the two middle elements (this function returns their sum, i.e., twice the median).
fn compute_double_median(v: Vec<i32>) -> (o: Option<i64>)
    ensures
        o == double_median(v@),
{
    let mut o: Option<i64> = None;
    if v.len() == 0 {
        return None;
    }
    let s = sort_seq(&v);
    proof {
        assert(sorted(s@));
        assert(is_sorted_from_base_seq(v@, s@));
        assert(s.len() != 0);
        let proof_sorted = get_sorted(v@);
        all_medians_on_sorted_are_equal(v@, proof_sorted, s@);
    }
    if s.len() % 2 == 1 {
        let val = Some((s[(s.len() - 1) / 2] as i64 * 2) as i64);
        return val
    } else {
        let l = s[((s.len() - 1) / 2)] as i64;
        let r = s[(s.len() / 2)] as i64;
        let sum = l + r;
        let val = Some(sum);
        return val;
    }
}

fn static_checks() {
    let v = vec![1,2,3];
    let m = compute_double_median(v);
    assert(m == Some(4i64)) by {
        assert(sorted(v@));
        let vp = v@;
        assert(is_sorted_from_base_seq(vp, vp));  // This proves that it is possible to chose a get_sorted element as at least 1 exists
        let vs = get_sorted(vp);
        assert(is_sorted_from_base_seq(vp, vs));
        assert(sorted(vs));
        sorted_unique_lemma(vp, vs);
        assert(vp == vs);
    }

    let v = vec![3,2];
    let m = compute_double_median(v);
    let vh = vec![2,3];
    assert(m == Some(5i64)) by {
        // Rational need a vh that is v already sorted to be able to construct the proof
        let vp = v@;
        let vhp = vh@;
        let vpm = vp.to_multiset();
        let vhpm = vhp.to_multiset();
        vp.to_multiset_ensures();
        vhp.to_multiset_ensures();
        assert(sorted(vh@));
        assert(vp.len() == vh.len());
        assert(vp[0] == vhp[1]);
        assert(vp[1] == vhp[0]);
        swap_preserves_multiset(vp, vhp, 0, 1);
        assert(vhp.to_multiset() == vp.to_multiset());
        assert(is_sorted_from_base_seq(vp, vhp));
        let vs = get_sorted(vp);
        assert(is_sorted_from_base_seq(vp, vs));
        assert(sorted(vs));
        sorted_unique_lemma(vhp, vs);
        assert(vhp == vs);
    }
}

} // verus!
fn main() {
    assert!(compute_double_median(vec![3, 1, 2, 4, 5]) == Some(6));
    assert!(compute_double_median(vec![-10, 4, 6, 1000, 10, 20]) == Some(16));
    assert!(compute_double_median(vec![5]) == Some(10));
    assert!(compute_double_median(vec![6, 5]) == Some(11));
    assert!(compute_double_median(vec![8, 1, 3, 9, 9, 2, 7]) == Some(14));
}

/*
### VERUS END
*/
/*
### PROMPT


def median(l: list):
    """Return median of elements in the list l.
    >>> median([3, 1, 2, 4, 5])
    3
    >>> median([-10, 4, 6, 1000, 10, 20])
    15.0
    """

*/

/*
### ENTRY POINT
median
*/

/*
### CANONICAL SOLUTION
    l = sorted(l)
    if len(l) % 2 == 1:
        return l[len(l) // 2]
    else:
        return (l[len(l) // 2 - 1] + l[len(l) // 2]) / 2.0

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate([3, 1, 2, 4, 5]) == 3
    assert candidate([-10, 4, 6, 1000, 10, 20]) == 8.0
    assert candidate([5]) == 5
    assert candidate([6, 5]) == 5.5
    assert candidate([8, 1, 3, 9, 9, 2, 7]) == 7


*/
