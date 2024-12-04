/*
### ID
HumanEval/87
*/
/*
### VERUS BEGIN
*/
use std::vec::Vec;
use vstd::prelude::*;

verus! {

/// coords is sorted by row in ascending order.
pub open spec fn row_sorted_asc(coords: Seq<(usize, usize)>) -> bool {
    forall|i: usize, j: usize|
        0 <= i < j < coords.len() ==> #[trigger] coords[i as int].0 <= #[trigger] coords[j as int].0
}

/// In coords, the coordinates of same row are sorted by column in descending order.
pub open spec fn row_col_sorted_desc(coords: Seq<(usize, usize)>) -> bool {
    forall|i: usize, j: usize|
        0 <= i < j < coords.len() && #[trigger] coords[i as int].0 == #[trigger] coords[j as int].0
            ==> coords[i as int].1 > coords[j as int].1
}

/// coords contains all coordinates matching x in lst within the given row and at or after the given column.
pub open spec fn coords_complete_for_row_until_col(
    lst: Seq<Seq<i32>>,
    x: i32,
    coords: Seq<(usize, usize)>,
    row: usize,
    col: usize,
) -> bool
    recommends
        0 <= row < lst.len(),
{
    forall|j: usize|
        #![trigger lst[row as int][j as int]]
        0 <= j < lst[row as int].len() && col <= j && lst[row as int][j as int] == x ==> exists|
            k: int,
        |
            #![trigger coords[k]]
            0 <= k < coords.len() && coords[k] == (row, j)
}

/// coords contains all coordinates matching x in lst before the given row.
pub open spec fn coords_complete_until_row(
    lst: Seq<Seq<i32>>,
    x: i32,
    coords: Seq<(usize, usize)>,
    row: usize,
) -> bool {
    forall|i: usize|
        #![trigger lst[i as int]]
        0 <= i < lst.len() && i < row ==> coords_complete_for_row_until_col(lst, x, coords, i, 0)
}

/// coords contains all coordinates matching x in lst.
pub open spec fn coords_complete(lst: Seq<Seq<i32>>, x: i32, coords: Seq<(usize, usize)>) -> bool {
    coords_complete_until_row(lst, x, coords, lst.len() as usize)
}

/// All points in coords represent occurrences of x in lst.
pub open spec fn coords_sound(lst: Seq<Seq<i32>>, x: i32, coords: Seq<(usize, usize)>) -> bool {
    forall|i: usize, j: usize|
        #![trigger lst[i as int][j as int]]
        #![trigger coords.contains((i,j))]
        0 <= i < lst.len() && 0 <= j < lst[i as int].len() && coords.contains((i, j))
            ==> lst[i as int][j as int] == x
}

/// coords exactly matches all of the occurrences of x in lst.
pub open spec fn coords_matches_lst(
    lst: Seq<Seq<i32>>,
    x: i32,
    coords: Seq<(usize, usize)>,
) -> bool {
    &&& coords_complete(lst, x, coords)
    &&& coords_sound(lst, x, coords)
}

/// Returns lst as a Seq.
pub open spec fn lst_seq_refl(lst: Vec<Vec<i32>>) -> Seq<Seq<i32>> {
    lst@.map_values(|v: Vec<i32>| v@)
}

/// Returns coords as a Seq.
pub open spec fn coords_seq_refl(coords: Vec<(usize, usize)>) -> Seq<(usize, usize)> {
    coords@
}

/// Returns list of all points in lst whose value is x, sorted by row in ascending order and then by column in descending order.
fn get_row(lst: Vec<Vec<i32>>, x: i32) -> (coords: Vec<(usize, usize)>)
    ensures
        coords_matches_lst(lst_seq_refl(lst), x, coords@),
        row_sorted_asc(coords@),
        row_col_sorted_desc(coords@),
{
    let mut coords: Vec<(usize, usize)> = Vec::new();
    let mut i = 0;
    let ghost ghost_seq: Seq<Seq<i32>> = lst_seq_refl(lst);
    let ghost ghost_coords: Seq<(usize, usize)> = coords_seq_refl(coords);
    for i in 0..lst.len()
        invariant
            ghost_seq == lst_seq_refl(lst),
            ghost_coords == coords_seq_refl(coords),
            forall|k: int| 0 <= k < coords.len() ==> #[trigger] coords@[k].0 < i,
            row_sorted_asc(coords@),
            row_col_sorted_desc(coords@),
            coords_sound(ghost_seq, x, coords@),
            coords_complete_until_row(ghost_seq, x, coords@, i),
    {
        let n = lst[i].len();
        // construct list of coordinates for row in descending column order
        for j in 0..n
            invariant
                ghost_seq == lst_seq_refl(lst),
                ghost_coords == coords_seq_refl(coords),
                0 <= i < lst.len(),
                n == lst[i as int].len(),
                forall|k: int| 0 <= k < coords.len() ==> #[trigger] coords@[k].0 <= i,
                forall|k: int|
                    0 <= k < coords.len() && #[trigger] coords@[k].0 == i ==> coords@[k].1 > n - 1
                        - j,
                row_sorted_asc(coords@),
                row_col_sorted_desc(coords@),
                coords_sound(ghost_seq, x, coords@),
                coords_complete_until_row(ghost_seq, x, coords@, i),
                coords_complete_for_row_until_col(ghost_seq, x, coords@, i, (n - j) as usize),
        {
            if (lst[i][n - 1 - j] == x) {
                coords.push((i, n - 1 - j));

                proof {
                    // todo - is there a better way to do this?
                    // seems inefficient to use a ghost variable to assert that the list has only mutated by adding an element to the end
                    assert(coords_complete_until_row(ghost_seq, x, coords@, i)) by {
                        assert(coords@.drop_last() =~= ghost_coords);
                    }

                    // same todo as above
                    assert(coords_complete_for_row_until_col(
                        ghost_seq,
                        x,
                        coords@.drop_last(),
                        i,
                        (n - j) as usize,
                    )) by {
                        assert(coords@.drop_last() =~= ghost_coords);
                    }

                    ghost_coords = ghost_coords.push((i, (n - 1 - j) as usize));

                    assert(coords_complete_for_row_until_col(
                        ghost_seq,
                        x,
                        coords@,
                        i,
                        (n - j - 1) as usize,
                    )) by {
                        assert(coords[coords.len() - 1] == (i, (n - j - 1) as usize));
                    }
                }
            }
        }
    }
    return coords;
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def get_row(lst, x):
    """
    You are given a 2 dimensional data, as a nested lists,
    which is similar to matrix, however, unlike matrices,
    each row may contain a different number of columns.
    Given lst, and integer x, find integers x in the list,
    and return list of tuples, [(x1, y1), (x2, y2) ...] such that
    each tuple is a coordinate - (row, columns), starting with 0.
    Sort coordinates initially by rows in ascending order.
    Also, sort coordinates of the row by columns in descending order.

    Examples:
    get_row([
      [1,2,3,4,5,6],
      [1,2,3,4,1,6],
      [1,2,3,4,5,1]
    ], 1) == [(0, 0), (1, 4), (1, 0), (2, 5), (2, 0)]
    get_row([], 1) == []
    get_row([[], [1], [1, 2, 3]], 3) == [(2, 2)]
    """

*/

/*
### ENTRY POINT
get_row
*/

/*
### CANONICAL SOLUTION
    coords = [(i, j) for i in range(len(lst)) for j in range(len(lst[i])) if lst[i][j] == x]
    return sorted(sorted(coords, key=lambda x: x[1], reverse=True), key=lambda x: x[0])

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([
        [1,2,3,4,5,6],
        [1,2,3,4,1,6],
        [1,2,3,4,5,1]
    ], 1) == [(0, 0), (1, 4), (1, 0), (2, 5), (2, 0)]
    assert candidate([
        [1,2,3,4,5,6],
        [1,2,3,4,5,6],
        [1,2,3,4,5,6],
        [1,2,3,4,5,6],
        [1,2,3,4,5,6],
        [1,2,3,4,5,6]
    ], 2) == [(0, 1), (1, 1), (2, 1), (3, 1), (4, 1), (5, 1)]
    assert candidate([
        [1,2,3,4,5,6],
        [1,2,3,4,5,6],
        [1,1,3,4,5,6],
        [1,2,1,4,5,6],
        [1,2,3,1,5,6],
        [1,2,3,4,1,6],
        [1,2,3,4,5,1]
    ], 1) == [(0, 0), (1, 0), (2, 1), (2, 0), (3, 2), (3, 0), (4, 3), (4, 0), (5, 4), (5, 0), (6, 5), (6, 0)]
    assert candidate([], 1) == []
    assert candidate([[1]], 2) == []
    assert candidate([[], [1], [1, 2, 3]], 3) == [(2, 2)]

    # Check some edge cases that are easy to work out by hand.
    assert True


*/
