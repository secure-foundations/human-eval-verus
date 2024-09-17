/*
### ID
HumanEval/74
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn total_match<'a>(lst1: Vec<&'a str>, lst2: Vec<&'a str>) -> (ret: Option<Vec<&'a str>>)
    ensures
        ret.is_some() ==> ret.unwrap() == if lst1@.map_values(|s: &str| s@.len()).fold_left(
            0,
            |x: int, y| x + y,
        ) <= lst2@.map_values(|s: &str| s@.len()).fold_left(0, |x: int, y| x + y) {
            lst1
        } else {
            lst2
        },
{
    let mut l1: usize = 0;
    for i in 0..lst1.len()
        invariant
            l1 == lst1@.subrange(0, i as int).map_values(|s: &str| s@.len()).fold_left(
                0,
                |x: int, y| x + y,
            ),
    // i <= lst1.len(),
    {
        l1 = l1.checked_add(lst1[i].unicode_len())?;
        assert(lst1@.subrange(0, i + 1).map_values(|s: &str| s@.len()).drop_last()
            == lst1@.subrange(0, i as int).map_values(|s: &str| s@.len()));
    }
    assert(lst1@ == lst1@.subrange(0, lst1.len() as int));

    let mut l2: usize = 0;
    for i in 0..lst2.len()
        invariant
            l2 == lst2@.subrange(0, i as int).map_values(|s: &str| s@.len()).fold_left(
                0,
                |x: int, y| x + y,
            ),
    {
        let x = lst2[i].unicode_len();
        assert(x == lst2[i as int]@.len());
        l2 = l2.checked_add(x)?;
        assert(lst2@.subrange(0, i + 1).map_values(|s: &str| s@.len()).drop_last()
            == lst2@.subrange(0, i as int).map_values(|s: &str| s@.len()));
    }
    assert(lst2@ == lst2@.subrange(0, lst2.len() as int));

    if l1 <= l2 {
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
