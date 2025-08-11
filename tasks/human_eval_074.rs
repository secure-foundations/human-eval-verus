/*
### ID
HumanEval/74
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn spec_sum(s: Seq<nat>) -> int {
    s.fold_left(0, |x: int, y| x + y)
}

// i and j are ends of the subrange - exclusive
proof fn lemma_increasing_sum(s: Seq<nat>, i: int, j: int)
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
        lemma_increasing_sum(s, i, j - 1);
    }
}

spec fn total_str_len(strings: Seq<&str>) -> int {
    spec_sum(strings.map_values(|s: &str| s@.len()))
}

fn checked_total_str_len(lst: &Vec<&str>) -> (ret: Option<usize>)
    ensures
        ret.is_some() <==> total_str_len(lst@) <= usize::MAX,
        ret.is_some() <==> ret.unwrap() == total_str_len(lst@),
{
    let ghost lens = Seq::<nat>::empty();
    let mut sum: usize = 0;
    for i in 0..lst.len()
        invariant
            sum == lst@.subrange(0, i as int).map_values(|s: &str| s@.len()).fold_left(
                0,
                |x: int, y| x + y,
            ),
            spec_sum(lens) == sum,
            lens =~= lst@.map_values(|s: &str| s@.len()).take(i as int),
            lens =~= lst@.take(i as int).map_values(|s: &str| s@.len()),
    {
        let x = lst[i].unicode_len();
        proof {
            assert(lens.push(x as nat).drop_last() == lens);
            lens = lens.push(x as nat);
            assert(lens =~= lst@.map_values(|s: &str| s@.len()).take(i + 1));

            lemma_increasing_sum(lst@.map_values(|s: &str| s@.len()), i + 1, lst@.len() as int);
            assert(total_str_len(lst@) >= spec_sum(lens)) by {
                assert(lst@.map_values(|s: &str| s@.len()) =~= lst@.map_values(
                    |s: &str| s@.len(),
                ).take(lst@.len() as int));
            }
            if x + sum > usize::MAX {
                assert(sum.checked_add(x).is_none());
                assert(total_str_len(lst@) > usize::MAX);
            }
        }
        sum = sum.checked_add(x)?;
        assert(lst@.take(i + 1).map_values(|s: &str| s@.len()).drop_last() == lst@.take(
            i as int,
        ).map_values(|s: &str| s@.len()));
    }
    assert(lst@ == lst@.subrange(0, lst.len() as int));
    return Some(sum);
}

fn total_match<'a>(lst1: Vec<&'a str>, lst2: Vec<&'a str>) -> (ret: Option<Vec<&'a str>>)
    ensures
        ret.is_some() <== total_str_len(lst1@) <= usize::MAX && total_str_len(lst2@) <= usize::MAX,
        ret.is_some() ==> ret.unwrap() == if total_str_len(lst1@) <= total_str_len(lst2@) {
            lst1
        } else {
            lst2
        },
{
    if checked_total_str_len(&lst1)? <= checked_total_str_len(&lst2)? {
        Some(lst1)
    } else {
        Some(lst2)
    }
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def total_match(lst1, lst2):
    '''
    Write a function that accepts two lists of strings and returns the list that has
    total number of chars in the all strings of the list less than the other list.

    if the two lists have the same number of chars, return the first list.

    Examples
    total_match([], []) ➞ []
    total_match(['hi', 'admin'], ['hI', 'Hi']) ➞ ['hI', 'Hi']
    total_match(['hi', 'admin'], ['hi', 'hi', 'admin', 'project']) ➞ ['hi', 'admin']
    total_match(['hi', 'admin'], ['hI', 'hi', 'hi']) ➞ ['hI', 'hi', 'hi']
    total_match(['4'], ['1', '2', '3', '4', '5']) ➞ ['4']
    '''

*/

/*
### ENTRY POINT
total_match
*/

/*
### CANONICAL SOLUTION
    l1 = 0
    for st in lst1:
        l1 += len(st)

    l2 = 0
    for st in lst2:
        l2 += len(st)

    if l1 <= l2:
        return lst1
    else:
        return lst2

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([], []) == []
    assert candidate(['hi', 'admin'], ['hi', 'hi']) == ['hi', 'hi']
    assert candidate(['hi', 'admin'], ['hi', 'hi', 'admin', 'project']) == ['hi', 'admin']
    assert candidate(['4'], ['1', '2', '3', '4', '5']) == ['4']
    assert candidate(['hi', 'admin'], ['hI', 'Hi']) == ['hI', 'Hi']
    assert candidate(['hi', 'admin'], ['hI', 'hi', 'hi']) == ['hI', 'hi', 'hi']
    assert candidate(['hi', 'admin'], ['hI', 'hi', 'hii']) == ['hi', 'admin']


    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate([], ['this']) == []
    assert candidate(['this'], []) == []


*/
