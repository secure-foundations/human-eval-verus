/*
### ID
HumanEval/129
*/
/*
### VERUS BEGIN
*/
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

// specification
pub open spec fn path_less_than(path1: Seq<int>, path2: Seq<int>) -> bool
    recommends
        path1.len() == path2.len(),
{
    (exists|i: int|
        (0 <= i < path1.len() && path1[i] < path2[i] && (forall|j: int|
            0 <= j < i ==> path1[j] == path2[j])))
}

#[verusfmt::skip]
pub open spec fn is_adjacent<const N: usize>(
    grid: Seq<Seq<int>>,
    m: int,
    n: int,
    coords: (int, int),
) -> bool
    recommends
        grid.len() == N,
        forall|i: int| (0 <= i < N ==> #[trigger] grid[i].len() == N),
{
    &&& (0 <= coords.0 <= N - 1)
    &&& (0 <= coords.1 <= N - 1)
    &&& grid[coords.0][coords.1] == m
    &&& (   (coords.0 < N - 1 && grid[coords.0 + 1][coords.1] == n)
         || (coords.0 > 0 && grid[coords.0 - 1][coords.1] == n)
         || (coords.1 < N - 1 && grid[coords.0][coords.1 + 1] == n)
         || (coords.1 > 0 && grid[coords.0][coords.1 - 1] == n))
}

pub open spec fn adjacent_numbers<const N: usize>(grid: Seq<Seq<int>>, m: int, n: int) -> bool
    recommends
        grid.len() == N,
        forall|i: int| (0 <= i < N ==> #[trigger] grid[i].len() == N),
{
    exists|i: int, j: int| #[trigger] (is_adjacent::<N>(grid, m, n, (i, j)))
}

pub open spec fn exists_a_cell_with_value<const N: usize>(grid: Seq<Seq<int>>, n: int) -> bool
    recommends
        grid.len() == N,
        forall|i: int| (0 <= i < N ==> #[trigger] grid[i].len() == N),
{
    (exists|i: int, j: int| (0 <= i < N && 0 <= j < N) && #[trigger] (grid[i][j]) == n)
}

pub open spec fn no_repeats_in_grid<const N: usize>(grid: Seq<Seq<int>>) -> bool
    recommends
        grid.len() == N,
        forall|i: int| (0 <= i < N ==> #[trigger] grid[i].len() == N),
{
    &&& (forall|i: int, j: int| (0 <= i < N && 0 <= j < N) ==> 1 <= #[trigger] grid[i][j] <= N * N)
    &&& (forall|n: int| 1 <= n <= N * N ==> #[trigger] exists_a_cell_with_value::<N>(grid, n))
    &&& (forall|i1: int, j1: int, i2: int, j2: int|
        (0 <= i1 < N && 0 <= j1 < N && 0 <= i2 < N && 0 <= j2 < N) ==> (#[trigger] grid[i1][j1]
            == #[trigger] grid[i2][j2]) ==> i1 == i2 && j1 == j2)
}

pub open spec fn is_valid_path<const N: usize>(grid: Seq<Seq<int>>, path: Seq<int>) -> bool
    recommends
        grid.len() == N,
        forall|i: int| (0 <= i < N ==> #[trigger] grid[i].len() == N),
{
    &&& forall|i: int|
        (0 <= i < path.len() - 1) ==> adjacent_numbers::<N>(grid, #[trigger] path[i], path[(i + 1)])
    &&& forall|i: int| (0 <= i <= path.len() - 1) ==> 1 <= #[trigger] path[i] <= N * N
}

pub open spec fn is_minpath<const N: usize>(grid: Seq<Seq<int>>, path: Seq<int>) -> bool
    recommends
        grid.len() == N,
        forall|i: int| (0 <= i < N ==> #[trigger] grid[i].len() == N),
{
    &&& (is_valid_path::<N>(grid, path))
    &&& (forall|alternate_path: Seq<int>|
        ((#[trigger] alternate_path.len() == path.len() && is_valid_path::<N>(grid, alternate_path))
            ==> (#[trigger] path_less_than(path, alternate_path) || path == alternate_path)))
}

// implementation
pub fn find_smallest_adjacent_to_one<const N: usize>(grid: [[u8; N]; N]) -> (ret: (
    (usize, usize),
    (usize, usize),
    u8,
))
    requires
        no_repeats_in_grid::<N>(
            grid@.map_values(|row: [u8; N]| row@.map_values(|item: u8| item as int)),
        ),
        N >= 2,
        2 <= N <= u8::MAX,
        N * N <= u8::MAX,
    ensures
        grid[ret.0.0 as int][ret.0.1 as int] == 1,
        grid[ret.1.0 as int][ret.1.1 as int] == ret.2,
        adjacent_numbers::<N>(
            grid@.map_values(|row: [u8; N]| row@.map_values(|item: u8| item as int)),
            ret.2 as int,
            1,
        ),
        0 <= ret.0.0 < N,
        0 <= ret.0.1 < N,
        0 <= ret.1.0 < N,
        0 <= ret.1.1 < N,
        (ret.0.0 < N - 1 && ret.0.0 + 1 == ret.1.0 && ret.0.1 == ret.1.1) || (ret.0.0 > 0 && ret.0.0
            - 1 == ret.1.0 && ret.0.1 == ret.1.1) || (ret.0.1 < N - 1 && ret.0.0 == ret.1.0
            && ret.0.1 + 1 == ret.1.1) || (ret.0.1 > 0 && ret.0.0 == ret.1.0 && ret.0.1 - 1
            == ret.1.1),
        (ret.0.0 < N - 1 ==> grid[ret.0.0 + 1][ret.0.1 as int] >= ret.2) && (ret.0.0 > 0
            ==> grid[ret.0.0 - 1][ret.0.1 as int] >= ret.2) && (ret.0.1 < N - 1
            ==> grid[ret.0.0 as int][ret.0.1 + 1] >= ret.2) && (ret.0.1 > 0
            ==> grid[ret.0.0 as int][ret.0.1 - 1] >= ret.2),
{
    let mut ones_i = 0usize;
    let mut ones_j = 0usize;
    let mut i = 0usize;

    assert(N * N >= 1) by { lemma_mul_strictly_positive(N as int, N as int) };

    assert(exists_a_cell_with_value::<N>(
        grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
        1,
    ));

    while i < N
        invariant
            (grid[ones_i as int][ones_j as int] == 1) || (exists|i0: int, j0: int|
                (i <= i0 < N) && 0 <= j0 < N && grid[i0 as int][j0 as int] == 1),
            (0 <= i <= N),
            N == grid.len(),
            (0 <= ones_i < N),
            N == grid[ones_i as int].len(),
            (0 <= ones_j < N),
        decreases (N - i),
    {
        let mut j = 0usize;
        while j < N
            invariant
                ((grid[ones_i as int][ones_j as int] == 1) || (exists|i0: int, j0: int|
                    ((i < i0 < N && 0 <= j0 < N) || (i0 == i && j <= j0 < N))
                        && grid[i0 as int][j0 as int] == 1)),
                0 <= j <= N,
                0 <= i < N,
                (0 <= ones_i < N),
                (0 <= ones_j < N),
            decreases N - j,
        {
            if grid[i][j] == 1 {
                ones_i = i;
                ones_j = j;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    let mut smallest = (N * N) as u8;
    let mut smallest_i = 0usize;
    let mut smallest_j = 0usize;

    assert(1 <= smallest);

    assert((forall|i: int, j: int|
        (0 <= i < N && 0 <= j < N) ==> 1 <= grid@.map_values(
            |row: [u8; N]| row@.map_values(|item: u8| item as int),
        )[#[trigger] (i + 0)][#[trigger] (j + 0)] <= N * N));
    assert((forall|i: int, j: int|
        (0 <= i < N && 0 <= j < N) ==> 1 <= #[trigger] grid[i + 0][j + 0] <= N * N));

    assert(ones_j > 0 ==> grid[(ones_i + 0) as int][(ones_j - 1) + 0] <= N * N);

    assert(ones_j > 0 ==> grid[(ones_i + 0) as int][(ones_j - 1) + 0] <= smallest);
    assert(ones_j < N - 1 ==> grid[(ones_i + 0) as int][(ones_j + 1) + 0] <= smallest);
    assert(ones_i > 0 ==> grid[(ones_i - 1) + 0][ones_j + 0] <= smallest);
    assert(ones_i < N - 1 ==> grid[(ones_i + 1) + 0][ones_j + 0] <= smallest);

    assert((ones_j > 0 && grid[ones_i as int][ones_j - 1] <= smallest) || (ones_j < N - 1
        && grid[ones_i as int][ones_j + 1] <= smallest) || (ones_i > 0 && grid[ones_i
        - 1][ones_j as int] <= smallest) || (ones_i < N - 1 && grid[ones_i + 1][ones_j as int]
        <= smallest));

    if (ones_j > 0 && grid[ones_i][ones_j - 1] <= smallest) {
        smallest = grid[ones_i][ones_j - 1];
        smallest_i = ones_i;
        smallest_j = ones_j - 1;
    }
    if (ones_j < N - 1 && grid[ones_i][ones_j + 1] <= smallest) {
        smallest = grid[ones_i][ones_j + 1];
        smallest_i = ones_i;
        smallest_j = ones_j + 1;
    }
    if (ones_i > 0 && grid[ones_i - 1][ones_j] <= smallest) {
        smallest = grid[ones_i - 1][ones_j];
        smallest_i = ones_i - 1;
        smallest_j = ones_j;
    }
    if (ones_i < N - 1 && grid[ones_i + 1][ones_j] <= smallest) {
        smallest = grid[ones_i + 1][ones_j];
        smallest_i = ones_i + 1;
        smallest_j = ones_j;
    }
    assert(ones_j > 0 ==> grid@.map_values(
        |row: [u8; N]| row@.map_values(|item| item as int),
    )[ones_i as int][ones_j - 1] >= smallest);

    assert(0 <= (smallest_i + 0) as int <= N - 1);
    assert(0 <= (smallest_j + 0) as int <= N - 1);
    assert(grid[(smallest_i + 0) as int][(smallest_j + 0) as int] == smallest);
    assert((((smallest_i + 0) < (N - 1)) && grid[(smallest_i + 0) as int + 1][(smallest_j
        + 0) as int] == 1) || ((smallest_i + 0) > 0 && grid[(smallest_i + 0) as int][(smallest_j
        + 0) as int] == smallest && grid[(smallest_i + 0) as int - 1][(smallest_j + 0) as int] == 1)
        || ((smallest_j + 0) < N - 1 && grid[(smallest_i + 0) as int][(smallest_j + 0) as int]
        == smallest && grid[(smallest_i + 0) as int][(smallest_j + 0) as int + 1] == 1) || ((
    smallest_j + 0) as int > 0 && grid[(smallest_i + 0) as int][(smallest_j + 0) as int] == smallest
        && grid[(smallest_i + 0) as int][(smallest_j + 0) as int - 1] == 1));

    assert(is_adjacent::<N>(
        grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
        smallest as int,
        1,
        (smallest_i + 0 as int, smallest_j + 0 as int),
    ));
    assert(exists|i: int, j: int|
        (is_adjacent::<N>(
            grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
            smallest as int,
            1,
            (#[trigger] (i + 0), #[trigger] (j + 0)),
        )));

    return ((ones_i, ones_j), (smallest_i, smallest_j), smallest)
}

// basically want a lemma that says if \forall alt_path (path < alt_path)
// then if alt_path' < path + [x]
// we get that alt_path'[:path.len()] == path adn alt_path[path.len()] < x
proof fn lemma_less_than_step_even<const N: usize>(
    path: Seq<int>,
    grid: [[u8; N]; N],
    extra_item: int,
)
    requires
        no_repeats_in_grid::<N>(
            grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
        ),
        forall|alternate_path: Seq<int>|
            ((alternate_path.len() == path.len() && is_valid_path::<N>(
                grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
                alternate_path,
            )) ==> (#[trigger] path_less_than(path, alternate_path) || path == alternate_path)),
        extra_item == 1,
    ensures
        forall|alternate_path_: Seq<int>|
            ((#[trigger] alternate_path_.len() == path.len() + 1 && is_valid_path::<N>(
                grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
                alternate_path_,
            )) ==> (path_less_than(path + seq![extra_item], alternate_path_) || path + seq![
                extra_item,
            ] == alternate_path_)),
{
    assert forall|alternate_path_: Seq<int>|
        ((#[trigger] alternate_path_.len()) == path.len() + 1 && is_valid_path::<N>(
            grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
            alternate_path_,
        )) implies (path_less_than(path + seq![extra_item], alternate_path_) || path + seq![
        extra_item,
    ] == alternate_path_) by {
        if path_less_than(path, alternate_path_.subrange(0, path.len() as int)) {
        } else {
            if (alternate_path_[path.len() as int] > extra_item) {
            } else {
                assert(path + seq![extra_item] =~= alternate_path_);
            }
        }
    }
}

proof fn lemma_less_than_step_odd<const N: usize>(
    path: Seq<int>,
    grid: [[u8; N]; N],
    extra_item: int,
    ones_i: int,
    ones_j: int,
)
    requires
        no_repeats_in_grid::<N>(
            grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
        ),
        forall|alternate_path: Seq<int>|
            ((alternate_path.len() == path.len() && is_valid_path::<N>(
                grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
                alternate_path,
            )) ==> (#[trigger] path_less_than(path, alternate_path) || path == alternate_path)),
        path.len() >= 1,
        path[path.len() - 1] == 1,
        0 <= ones_i <= N - 1,
        0 <= ones_j <= N - 1,
        grid[ones_i][ones_j] == 1,
        ones_i < N - 1 ==> grid[ones_i + 1][ones_j] >= extra_item,
        ones_i > 0 ==> grid[ones_i - 1][ones_j] >= extra_item,
        ones_j < N - 1 ==> grid[ones_i][ones_j + 1] >= extra_item,
        ones_j > 0 ==> grid[ones_i][ones_j - 1] >= extra_item,
        ones_i < N - 1 || ones_i > 0,
        ones_j < N - 1 || ones_j > 0,
    ensures
        forall|alternate_path_: Seq<int>|
            ((#[trigger] alternate_path_.len() == path.len() + 1 && is_valid_path::<N>(
                grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
                alternate_path_,
            )) ==> (path_less_than(path + seq![extra_item], alternate_path_) || path + seq![
                extra_item,
            ] == alternate_path_)),
{
    assert forall|alternate_path_: Seq<int>|
        ((#[trigger] alternate_path_.len()) == path.len() + 1 && is_valid_path::<N>(
            grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
            alternate_path_,
        )) implies (path_less_than(path + seq![extra_item], alternate_path_) || path + seq![
        extra_item,
    ] == alternate_path_) by {
        assert(is_valid_path::<N>(
            grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
            alternate_path_.subrange(0, path.len() as int),
        ));

        if path_less_than(path, alternate_path_.subrange(0, path.len() as int)) {
        } else {
            let m = alternate_path_[(path.len() - 1) as int];
            let n = alternate_path_[(path.len() + 0) as int];

            let pair = choose|pair: (int, int)|
                (is_adjacent::<N>(
                    grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
                    m,
                    n,
                    (#[trigger] pair.0, #[trigger] pair.1),
                ));

            let i = pair.0;
            let j = pair.1;

            assert(1 == grid@.map_values(
                |row: [u8; N]| row@.map_values(|item| item as int),
            )[ones_i][ones_j]);

            if (alternate_path_[path.len() as int] > extra_item) {
            } else {
                assert(path + seq![extra_item] =~= alternate_path_);
            }
        }
    }
}

pub fn min_path<const N: usize>(grid: [[u8; N]; N], k: u8) -> (path: Vec<u8>)
    requires
        no_repeats_in_grid::<N>(
            grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
        ),
        2 <= N <= u8::MAX,
        N * N <= u8::MAX,
    ensures
        path.len() == k,
        is_minpath::<N>(
            grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
            path@.map_values(|item| item as int),
        ),
{
    let (ones_coordinates, smallest_coordinates, smallest) = find_smallest_adjacent_to_one(grid);
    let mut path: Vec<u8> = vec![];
    let mut k_counter = k;
    let mut even = true;

    assert(forall|alternate_path: Seq<int>|
        ((alternate_path.len() == path.len() ==> path@.map_values(|j: u8| j as int)
            == alternate_path)));

    #[verifier::loop_isolation(false)]
    while k_counter > 0
        invariant
            path.len() + k_counter == k,
            // what we are trying to prove
            forall|i: int|
                (0 <= #[trigger] (i + 0) < path@.map_values(|j: u8| j as int).len() - 1)
                    ==> adjacent_numbers::<N>(
                    grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
                    path@.map_values(|j: u8| j as int)[i],
                    path@.map_values(|j: u8| j as int)[(i + 1)],
                ),
            forall|alternate_path: Seq<int>|
                ((#[trigger] alternate_path.len() == path@.map_values(|j: u8| j as int).len()
                    && is_valid_path::<N>(
                    grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
                    alternate_path,
                )) ==> (path_less_than(path@.map_values(|j: u8| j as int), alternate_path)
                    || path@.map_values(|j: u8| j as int) == alternate_path)),
            //remembering the last element
            (path.len() > 0 && even) ==> path[path.len() - 1] == smallest,
            (path.len() > 0 && !even) ==> path[path.len() - 1] == 1u8,
            even || (path.len() >= 1),
        decreases k_counter,
    {
        if (even) {
            let t = path.len();
            let old_path = path.clone();
            let mut next_item = vec![1u8];
            path.append(&mut next_item);
            proof {
                lemma_less_than_step_even(
                    path@.map_values(|j: u8| j as int).subrange(0, path.len() - 1),
                    grid,
                    1 as int,
                );
            }
        } else {
            let mut next_item = vec![smallest];
            path.append(&mut next_item);

            proof {
                lemma_less_than_step_odd(
                    path@.map_values(|j: u8| j as int).subrange(0, path.len() - 1),
                    grid,
                    smallest as int,
                    ones_coordinates.0 as int,
                    ones_coordinates.1 as int,
                );
            }
        }
        even = !even;
        k_counter = k_counter - 1;

        //proving adjacency
        assert(forall|i: int|
            (0 <= #[trigger] (i + 0) < path@.map_values(|j: u8| j as int).len() - 1) ==> (exists|
                i0: int,
                j0: int,
            |
                (is_adjacent::<N>(
                    grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
                    path@.map_values(|j: u8| j as int)[i],
                    path@.map_values(|j: u8| j as int)[(i + 1)],
                    (i0, j0),
                ))));
    }
    assert(forall|i: int|
        (0 <= i + 0 < path@.len() - 1) ==> adjacent_numbers::<N>(
            grid@.map_values(|row: [u8; N]| row@.map_values(|item| item as int)),
            #[trigger] path@[i] as int,
            path@[(i + 1)] as int,
        ));
    return path
}

} // verus!
fn main() {
    println!("{:?}", min_path([[1, 2, 3], [4, 5, 6], [7, 8, 9]], 3));
    // > [1, 2, 1]
    println!("{:?}", min_path([[5, 9, 3], [4, 1, 6], [7, 8, 2]], 7));
    // > [1, 4, 1, 4, 1, 4, 1]
}

/*
### VERUS END
*/

/*
### PROMPT

def min_path(grid, k):
    """
    Given a grid with N rows and N columns (N >= 2) and a positive integer k,
    each cell of the grid contains a value. Every integer in the range [1, N * N]
    inclusive appears exactly once on the cells of the grid.

    You have to find the minimum path of length k in the grid. You can start
    from any cell, and in each step you can move to any of the neighbor cells,
    in other words, you can go to cells which share an edge with you current
    cell.
    Please note that a path of length k means visiting exactly k cells (not
    necessarily distinct).
    You CANNOT go off the grid.
    A path A (of length k) is considered less than a path B (of length k) if
    after making the ordered lists of the values on the cells that A and B go
    through (let's call them lst_A and lst_B), lst_A is lexicographically less
    than lst_B, in other words, there exist an integer index i (1 <= i <= k)
    such that lst_A[i] < lst_B[i] and for any j (1 <= j < i) we have
    lst_A[j] = lst_B[j].
    It is guaranteed that the answer is unique.
    Return an ordered list of the values on the cells that the minimum path go through.

    Examples:

        Input: grid = [ [1,2,3], [4,5,6], [7,8,9]], k = 3
        Output: [1, 2, 1]

        Input: grid = [ [5,9,3], [4,1,6], [7,8,2]], k = 1
        Output: [1]
    """

*/

/*
### ENTRY POINT
min_path
*/

/*
### CANONICAL SOLUTION
    n = len(grid)
    val = n * n + 1
    for i in range(n):
        for j in range(n):
            if grid[i][j] == 1:
                temp = []
                if i != 0:
                    temp.append(grid[i - 1][j])

                if j != 0:
                    temp.append(grid[i][j - 1])

                if i != n - 1:
                    temp.append(grid[i + 1][j])

                if j != n - 1:
                    temp.append(grid[i][j + 1])

                val = min(temp)

    ans = []
    for i in range(k):
        if i % 2 == 0:
            ans.append(1)
        else:
            ans.append(val)
    return ans

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    print
    assert candidate([[1, 2, 3], [4, 5, 6], [7, 8, 9]], 3) == [1, 2, 1]
    assert candidate([[5, 9, 3], [4, 1, 6], [7, 8, 2]], 1) == [1]
    assert candidate([[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12], [13, 14, 15, 16]], 4) == [1, 2, 1, 2]
    assert candidate([[6, 4, 13, 10], [5, 7, 12, 1], [3, 16, 11, 15], [8, 14, 9, 2]], 7) == [1, 10, 1, 10, 1, 10, 1]
    assert candidate([[8, 14, 9, 2], [6, 4, 13, 15], [5, 7, 1, 12], [3, 10, 11, 16]], 5) == [1, 7, 1, 7, 1]
    assert candidate([[11, 8, 7, 2], [5, 16, 14, 4], [9, 3, 15, 6], [12, 13, 10, 1]], 9) == [1, 6, 1, 6, 1, 6, 1, 6, 1]
    assert candidate([[12, 13, 10, 1], [9, 3, 15, 6], [5, 16, 14, 4], [11, 8, 7, 2]], 12) == [1, 6, 1, 6, 1, 6, 1, 6, 1, 6, 1, 6]
    assert candidate([[2, 7, 4], [3, 1, 5], [6, 8, 9]], 8) == [1, 3, 1, 3, 1, 3, 1, 3]
    assert candidate([[6, 1, 5], [3, 8, 9], [2, 7, 4]], 8) == [1, 5, 1, 5, 1, 5, 1, 5]

    # Check some edge cases that are easy to work out by hand.
    assert candidate([[1, 2], [3, 4]], 10) == [1, 2, 1, 2, 1, 2, 1, 2, 1, 2]
    assert candidate([[1, 3], [3, 2]], 10) == [1, 3, 1, 3, 1, 3, 1, 3, 1, 3]


*/
