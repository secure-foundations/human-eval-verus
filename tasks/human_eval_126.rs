/*
### ID
HumanEval/126
*/
/*
### VERUS BEGIN
*/
use vstd::{invariant, prelude::*};

verus! {

// TODO: Put your solution (the specification, implementation, and proof) to the task here
spec fn count(s: Seq<int>, k: int) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (s[0] == k) as nat + count(s.drop_first(), k)
    }
}

proof fn lemma_count_concat(a: Seq<int>, b: Seq<int>, k: int)
    ensures
        count(a + b, k) == count(a, k) + count(b, k),
    decreases a.len(),
{
    reveal_with_fuel(count, 2);
    if a.len() == 0 {
    } else {
        lemma_count_concat(a.drop_first(), b, k);
        assert((a + b).drop_first() == a.drop_first() + b);
    }
}

proof fn lemma_3eq_row_count_eq_greater_3(v: Seq<int>, i: int)
    requires
        v[i - 2] == v[i - 1] && v[i - 1] == v[i],
        2 <= i < v.len(),
    ensures
        count(v, v[i]) >= 3,
{
    // decomposiiotn array in two 3 parts vp3 (until the 3 equal ) v3 (three equal) vsf (the final part)
    // after proving count on v3 is 3, it follows that for all is 3 or greater (with concatenations lemmas)
    let val = v[i as int];
    let vsn = v.subrange(0, (i + 1) as int);
    let vsf = v.subrange((i + 1) as int, v.len() as int);
    let v3 = v.subrange((i - 2) as int, (i + 1) as int);
    let vp3 = v.subrange(0, (i - 2) as int);
    assert(count(v3, val as int) == 3) by {
        reveal_with_fuel(count, 4);
    };
    assert(count(vsn, val as int) >= 3) by {
        assert(vp3 + v3 == vsn);
        lemma_count_concat(vp3, v3, val as int);
    };
    assert(count(v, val as int) >= 3) by {
        assert(vsn + vsf == v);
        lemma_count_concat(vsn, vsf, val as int);
    }

}

proof fn lemma_not_contains_eq_count_0(v: Seq<int>, val: int)
    ensures
        (forall|p: int| 0 <= p < v.len() ==> v[p] != val) == (count(v, val) == 0),
    decreases v.len(),
{
    reveal_with_fuel(count, 4);
    if (v.len() == 0) {
    } else {
        let tail = v.drop_first();
        let head = seq![v[0]];
        assert(v == head + tail);
        lemma_not_contains_eq_count_0(tail, val);
    }
}

proof fn lemma_first_part_count_0(v: Seq<int>, w: int)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        forall|i: int| 0 <= i < v.len() ==> v[i] < w,
    ensures
        count(v, w) == 0,
{
    if (v.len() == 0) {
    } else {
        let tail = v.subrange(1 as int, v.len() as int);
        let head = seq![v[0]];
        assert(v == head + tail);
        lemma_not_contains_eq_count_0(tail, w);
    }
}

proof fn lemma_last_part_count_0(v: Seq<int>, w: int)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        forall|i: int| 0 <= i < v.len() ==> w < v[i],
    ensures
        count(v, w) == 0,
{
    if (v.len() == 0) {
    } else {
        let tail = v.subrange(1 as int, v.len() as int);
        let head = seq![v[0]];
        assert(v == head + tail);
        lemma_not_contains_eq_count_0(tail, w);
    }
}

spec fn less_part(v: Seq<int>, w: int) -> (r: Seq<int>)
    decreases v.len(),
{
    if (v.len() == 0) {
        Seq::empty()
    } else if (v[0] < w) {
        seq![v[0]] + less_part(v.drop_first(), w)
    } else {
        less_part(v.drop_first(), w)
    }
}

proof fn lemma_less_part_all_less(v: Seq<int>, w: int)
    ensures
        forall|i: int| 0 <= i < less_part(v, w).len() ==> less_part(v, w)[i] < w,
    decreases v.len(),
{
    reveal_with_fuel(less_part, 1);
    if (v.len() == 0) {
    } else if (v[0] < w) {
        assert(seq![v[0]] + less_part(v.drop_first(), w) == less_part(v, w));
        lemma_less_part_all_less(v.drop_first(), w);
    } else {
        assert(less_part(v.drop_first(), w) == less_part(v, w));
        lemma_less_part_all_less(v.drop_first(), w);
    }
}

spec fn eq_part(v: Seq<int>, w: int) -> (r: Seq<int>)
    decreases v.len(),
{
    if (v.len() == 0) {
        Seq::empty()
    } else if (v[0] == w) {
        seq![v[0]] + eq_part(v.drop_first(), w)
    } else {
        eq_part(v.drop_first(), w)
    }
}

proof fn lemma_eq_part_all_equal(v: Seq<int>, w: int)
    ensures
        forall|i: int| 0 <= i < eq_part(v, w).len() ==> eq_part(v, w)[i] == w,
    decreases v.len(),
{
    reveal_with_fuel(eq_part, 1);
    if (v.len() == 0) {
    } else if (v[0] == w) {
        assert(seq![v[0]] + eq_part(v.drop_first(), w) == eq_part(v, w));
        lemma_eq_part_all_equal(v.drop_first(), w);
    } else {
        assert(eq_part(v.drop_first(), w) == eq_part(v, w));
        lemma_eq_part_all_equal(v.drop_first(), w);
    }
}

spec fn big_part(v: Seq<int>, w: int) -> (r: Seq<int>)
    decreases v.len(),
{
    if (v.len() == 0) {
        Seq::empty()
    } else if (v[0] > w) {
        seq![v[0]] + big_part(v.drop_first(), w)
    } else {
        big_part(v.drop_first(), w)
    }
}

proof fn lemma_big_part_all_big(v: Seq<int>, w: int)
    ensures
        forall|i: int| 0 <= i < big_part(v, w).len() ==> big_part(v, w)[i] > w,
    decreases v.len(),
{
    reveal_with_fuel(big_part, 1);
    if (v.len() == 0) {
    } else if (v[0] > w) {
        assert(seq![v[0]] + big_part(v.drop_first(), w) == big_part(v, w));
        lemma_big_part_all_big(v.drop_first(), w);
    } else {
        assert(big_part(v.drop_first(), w) == big_part(v, w));
        lemma_big_part_all_big(v.drop_first(), w);
    }
}

proof fn lemma_less_w_is_0_if_first_eq_or_superior(v: Seq<int>, w: int)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        v.len() > 0,
        v[0] >= w,
    ensures
        less_part(v, w).len() == 0,
    decreases v.len(),
{
    if (v.len() == 0 || v.len() == 1) {
        reveal_with_fuel(less_part, 2);
    } else {
        let tail = v.drop_first();
        let head = seq![v[0]];
        assert(v == head + tail);
        lemma_subseq_sorted_are_sorted(v, head, tail);
        lemma_less_w_is_0_if_first_eq_or_superior(tail, w);
    }
}

proof fn lemma_eq_w_is_0_if_first_superior(v: Seq<int>, w: int)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        v.len() > 0,
        v[0] > w,
    ensures
        eq_part(v, w).len() == 0,
    decreases v.len(),
{
    if (v.len() == 0 || v.len() == 1) {
        reveal_with_fuel(eq_part, 2);
    } else {
        let tail = v.drop_first();
        let head = seq![v[0]];
        assert(v == head + tail);
        lemma_subseq_sorted_are_sorted(v, head, tail);
        lemma_eq_w_is_0_if_first_superior(tail, w);
    }
}

proof fn lemma_les_eq_big_concat_eq_original_seq(v: Seq<int>, w: int)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
    ensures
        less_part(v, w) + eq_part(v, w) + big_part(v, w) == v,
    decreases v.len(),
{
    if v.len() == 0 {
    } else {
        let tail = v.drop_first();
        assert(v == seq![v[0]] + tail);
        lemma_les_eq_big_concat_eq_original_seq(tail, w);
        if (v[0] < w) {
        } else if (v[0] == w) {
            lemma_less_w_is_0_if_first_eq_or_superior(v, w);
        } else {
            lemma_less_w_is_0_if_first_eq_or_superior(v, w);
            lemma_eq_w_is_0_if_first_superior(v, w);
        }
    }

}

proof fn lemma_subseq_sorted_are_sorted(v: Seq<int>, v1: Seq<int>, v2: Seq<int>)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        v == v1 + v2,
    ensures
        forall|i: int, j: int| 0 <= i <= j < v1.len() ==> v1[i] <= v1[j],
        forall|i: int, j: int| 0 <= i <= j < v2.len() ==> v2[i] <= v2[j],
{
    assert forall|i: int, j: int| 0 <= i <= j < v1.len() implies v1[i] <= v1[j] by {
        assert(v1[i] == v[i]);
        assert(v1[j] == v[j]);
    };
    assert forall|i: int, j: int| 0 <= i <= j < v2.len() implies v2[i] <= v2[j] by {
        let offset = v1.len() as int;
        assert(v2[i] == v[i + offset]);
        assert(v2[j] == v[j + offset]);
    };
}

proof fn lemma_can_divide_3_parts(v: Seq<int>, w: int)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
    ensures
        exists|v0: Seq<int>, v1: Seq<int>, v2: Seq<int>|
            v0 + v1 + v2 == v && (forall|i: int| 0 <= i < v0.len() ==> v0[i] < w) && (forall|i: int|

                0 <= i < v1.len() ==> v1[i] == w) && (forall|i: int|
                0 <= i < v2.len() ==> v2[i] > w),
    decreases v.len(),
{
    let v0 = less_part(v, w);
    let v1 = eq_part(v, w);
    let v2 = big_part(v, w);

    assert(forall|i: int| 0 <= i < v0.len() ==> v0[i] < w) by {
        lemma_less_part_all_less(v, w);
    }
    assert(forall|i: int| 0 <= i < v1.len() ==> v1[i] == w) by {
        lemma_eq_part_all_equal(v, w);
    }
    assert(forall|i: int| 0 <= i < v2.len() ==> v2[i] > w) by {
        lemma_big_part_all_big(v, w);
    }

    assert(v0 + v1 + v2 == v) by {
        lemma_les_eq_big_concat_eq_original_seq(v, w);
    }
}

proof fn lemma_count_can_be_focus_on_middle(v: Seq<int>, w: int)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        0 <= w < v.len(),
    ensures
        exists|v1: Seq<int>, v2: Seq<int>, v3: Seq<int>|
            v1 + v2 + v3 =~= v && (forall|i: int| 0 <= i < v1.len() ==> v1[i] < v[w]) && (forall|
                i: int,
            |
                0 <= i < v2.len() ==> v2[i] == v[w]) && (forall|i: int|
                0 <= i < v3.len() ==> v3[i] > v[w]) && count(v, v[w]) == count(v2, v[w]),
{
    lemma_can_divide_3_parts(v, v[w]);
    let t = choose|v1: Seq<int>, v2: Seq<int>, v3: Seq<int>|
        v1 + v2 + v3 == v && (forall|i: int| 0 <= i < v1.len() ==> v1[i] < v[w]) && (forall|i: int|
            0 <= i < v2.len() ==> v2[i] == v[w]) && (forall|i: int|
            0 <= i < v3.len() ==> v3[i] > v[w]);

    assert(count(t.0, v[w]) == 0) by {
        lemma_subseq_sorted_are_sorted(v, t.0 + t.1, t.2);
        lemma_subseq_sorted_are_sorted(t.0 + t.1, t.0, t.1);
        lemma_first_part_count_0(t.0, v[w]);
    }

    assert(count(t.2, v[w]) == 0) by {
        lemma_subseq_sorted_are_sorted(v, t.0 + t.1, t.2);
        lemma_subseq_sorted_are_sorted(t.0 + t.1, t.0, t.1);
        lemma_last_part_count_0(t.2, v[w]);
    }

    assert(count(t.0 + t.1 + t.2, v[w]) == count(t.1, v[w])) by {
        lemma_count_concat(t.0, t.1, v[w]);
        let th = t.0 + t.1;
        lemma_count_concat(th, t.2, v[w]);
    }

}

proof fn lemma_all_elements_eq_count_is_size(v: Seq<int>, w: int)
    requires
        (forall|i: int| 0 <= i < v.len() ==> v[i] == w),
    ensures
        count(v, w) == v.len(),
    decreases v.len(),
{
    if (v.len() == 0) {
    } else {
        lemma_all_elements_eq_count_is_size(v.drop_first(), w);
    }

}

proof fn lemma_prop_holds_on_sub_seq(v: Seq<int>, v1: Seq<int>, v2: Seq<int>)
    requires
        v == v1 + v2,
        forall|i: int| 2 <= i < v.len() ==> !(v[i - 2] == v[i - 1] && v[i - 1] == #[trigger] v[i]),
    ensures
        forall|i: int|
            2 <= i < v1.len() ==> !(v1[i - 2] == v1[i - 1] && v1[i - 1] == #[trigger] v1[i]),
        forall|i: int|
            2 <= i < v2.len() ==> !(v2[i - 2] == v2[i - 1] && v2[i - 1] == #[trigger] v2[i]),
    decreases v1.len(),
{
    assert forall|i: int| 2 <= i < v1.len() implies !(v1[i - 2] == v1[i - 1] && v1[i - 1]
        == #[trigger] v1[i]) by {
        assert(v1[i] == v[i]);
        assert(v1[i - 1] == v[i - 1]);
        assert(v1[i - 2] == v[i - 2]);
    };
    assert forall|i: int| 2 <= i < v2.len() implies !(v2[i - 2] == v2[i - 1] && v2[i - 1]
        == #[trigger] v2[i]) by {
        let offset = v1.len() as int;
        assert(v2[i] == v[i + offset]);
        assert(v2[i - 1] == v[i - 1 + offset]);
        assert(v2[i - 2] == v[i - 2 + offset]);
    };
}

proof fn lemma_repeated_eq_imply_count(v: Seq<int>, w: int)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        forall|i: int| 2 <= i < v.len() ==> !(v[i - 2] == v[i - 1] && v[i - 1] == #[trigger] v[i]),
        0 <= w < v.len(),
    ensures
        count(v, v[w]) <= 2,
{
    lemma_count_can_be_focus_on_middle(v, w);
    let t = choose|v1: Seq<int>, v2: Seq<int>, v3: Seq<int>|
        v1 + v2 + v3 =~= v && (forall|i: int| 0 <= i < v1.len() ==> v1[i] < v[w]) && (forall|i: int|

            0 <= i < v2.len() ==> v2[i] == v[w]) && (forall|i: int|
            0 <= i < v3.len() ==> v3[i] > v[w]) && count(v, v[w]) == count(v2, v[w]);

    let v2 = t.1;
    assert(count(v, v[w]) == count(v2, v[w]));
    assert(count(v2, v[w]) == v2.len()) by {
        lemma_all_elements_eq_count_is_size(v2, v[w]);
    }
    assert(count(v, v[w]) == v2.len());

    let v1 = t.0;
    let v3 = t.2;

    lemma_prop_holds_on_sub_seq(v, v1 + v2, v3);
    lemma_prop_holds_on_sub_seq(v1 + v2, v1, v2);
    assert(forall|i: int|
        2 <= i < v2.len() ==> !(v2[i - 2] == v2[i - 1] && v2[i - 1] == #[trigger] v2[i]));

    if (v2.len() > 2) {
        assert(v2[0] == v[w]);
        assert(v2[1] == v[w]);
        assert(v2[2] == v[w]);
        assert(false);
    }
    assert(v2.len() <= 2);
    assert(count(v, v[w]) <= 2);
}

fn is_sorted(v: Vec<i32>) -> (ret: bool)
    requires
        v.len() <= i32::MAX,
    ensures
        ret == ((forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j]) && (forall|i: int|
            0 <= i < v.len() ==> count(v@.map_values(|x| x as int), v@[i] as int) <= 2)),
{
    let mut ind = 0;
    if (v.len() == 0 || v.len() == 1) {
        proof {
            assert(forall|i: int|
                0 <= i < v.len() ==> count(v@.map_values(|x| x as int), v@[i] as int) <= 2) by {
                reveal_with_fuel(count, 3);
            }
        }
        return true;
    }
    // Handle sorting

    while (ind < v.len() - 1)
        invariant
            0 <= ind < v.len(),
            (forall|i: int, j: int| 0 <= i <= j <= ind ==> v[i] <= v[j]),
        decreases v.len() - ind,
    {
        if (v[ind] > v[ind + 1]) {
            return false;
        }
        ind += 1;
    }
    assert(forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j]);

    if (v.len() == 2) {
        proof {
            assert(forall|i: int|
                0 <= i < v.len() ==> count(v@.map_values(|x| x as int), v@[i] as int) <= 2) by {
                reveal_with_fuel(count, 3);
            }
        }
        return true;
    }
    ind = 2;

    // Handle counting
    while (ind < v.len())
        invariant
            2 <= ind <= v.len(),
            (forall|i: int|
                2 <= i < ind ==> !(v[i - 2] == v[i - 1] && v[i - 1] == #[trigger] v[i])),
        decreases v.len() - ind,
    {
        if (v[ind - 2] == v[ind - 1] && v[ind - 1] == v[ind]) {
            proof {
                assert(!(forall|i: int|
                    0 <= i < v.len() ==> count(v@.map_values(|x| x as int), v@[i] as int) <= 2))
                    by {
                    let vs = v@.map_values(|x| x as int);
                    lemma_3eq_row_count_eq_greater_3(vs, ind as int);
                }
            }
            return false;
        }
        ind += 1;
    }

    assert forall|i: int| #![auto] 0 <= i < v.len() implies count(
        v@.map_values(|x| x as int),
        v@[i] as int,
    ) <= 2 by {
        lemma_repeated_eq_imply_count(v@.map_values(|x| x as int), i);
    }
    true
}

fn static_checks() {
    reveal_with_fuel(count, 6);
    let x = is_sorted(vec![5]);
    assert(x);

    let x = is_sorted(vec![1, 2, 3]);
    assert(x);

    let x = is_sorted(vec![1, 3, 2, 4]);
    assert(!x);

    let x = is_sorted(vec![1, 2,2]);
    assert(x);

    let x = is_sorted(vec![1, 3, 4, 6]);
    assert(x);

    let x = is_sorted(vec![1, 2, 2, 2]);
    assert(!x);
}

} // verus!
fn main() {
    assert!(is_sorted(vec![5]));
    assert!(!is_sorted(vec![1, 3, 2, 4, 5]));
    assert!(is_sorted(vec![1, 2, 3, 4, 5, 6]));
    assert!(is_sorted(vec![1, 2, 3, 4, 5, 6, 7]));
    assert!(!is_sorted(vec![1, 3, 2, 4, 5, 6, 7]));
    assert!(is_sorted(vec![1, 2, 2, 3, 3, 4]));
    assert!(!is_sorted(vec![1, 2, 2, 2, 3, 4]));
    println!("All tests passed!");
}

/*
### VERUS END
*/

/*
### PROMPT

def is_sorted(lst):
    '''
    Given a list of numbers, return whether or not they are sorted
    in ascending order. If list has more than 1 duplicate of the same
    number, return False. Assume no negative numbers and only integers.

    Examples
    is_sorted([5]) ➞ True
    is_sorted([1, 2, 3, 4, 5]) ➞ True
    is_sorted([1, 3, 2, 4, 5]) ➞ False
    is_sorted([1, 2, 3, 4, 5, 6]) ➞ True
    is_sorted([1, 2, 3, 4, 5, 6, 7]) ➞ True
    is_sorted([1, 3, 2, 4, 5, 6, 7]) ➞ False
    is_sorted([1, 2, 2, 3, 3, 4]) ➞ True
    is_sorted([1, 2, 2, 2, 3, 4]) ➞ False
    '''

*/

/*
### ENTRY POINT
is_sorted
*/

/*
### CANONICAL SOLUTION
    count_digit = dict([(i, 0) for i in lst])
    for i in lst:
        count_digit[i]+=1
    if any(count_digit[i] > 2 for i in lst):
        return False
    if all(lst[i-1] <= lst[i] for i in range(1, len(lst))):
        return True
    else:
        return False



*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([5]) == True
    assert candidate([1, 2, 3, 4, 5]) == True
    assert candidate([1, 3, 2, 4, 5]) == False
    assert candidate([1, 2, 3, 4, 5, 6]) == True
    assert candidate([1, 2, 3, 4, 5, 6, 7]) == True
    assert candidate([1, 3, 2, 4, 5, 6, 7]) == False, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([]) == True, "This prints if this assert fails 2 (good for debugging!)"
    assert candidate([1]) == True, "This prints if this assert fails 3 (good for debugging!)"
    assert candidate([3, 2, 1]) == False, "This prints if this assert fails 4 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate([1, 2, 2, 2, 3, 4]) == False, "This prints if this assert fails 5 (good for debugging!)"
    assert candidate([1, 2, 3, 3, 3, 4]) == False, "This prints if this assert fails 6 (good for debugging!)"
    assert candidate([1, 2, 2, 3, 3, 4]) == True, "This prints if this assert fails 7 (good for debugging!)"
    assert candidate([1, 2, 3, 4]) == True, "This prints if this assert fails 8 (good for debugging!)"


*/
