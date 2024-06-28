/// Given a grid with N rows and N columns (N >= 2) and a positive integer k, 
/// each cell of the grid contains a value. Every integer in the range [1, N * N]
/// inclusive appears exactly once on the cells of the grid.
///
/// You have to find the minimum path of length k in the grid. You can start
/// from any cell, and in each step you can move to any of the neighbor cells,
/// in other words, you can go to cells which share an edge with you current
/// cell.
/// Please note that a path of length k means visiting exactly k cells (not
/// necessarily distinct).
/// You CANNOT go off the grid.
/// A path A (of length k) is considered less than a path B (of length k) if
/// after making the ordered lists of the values on the cells that A and B go
/// through (let's call them lst_A and lst_B), lst_A is lexicographically less
/// than lst_B, in other words, there exist an integer index i (1 <= i <= k)
/// such that lst_A[i] < lst_B[i] and for any j (1 <= j < i) we have
/// lst_A[j] = lst_B[j].
/// It is guaranteed that the answer is unique.
/// Return an ordered list of the values on the cells that the minimum path go through.
///
/// Examples:
///
///     Input: grid = [ [1,2,3], [4,5,6], [7,8,9]], k = 3
///     Output: [1, 2, 1]
///
///     Input: grid = [ [5,9,3], [4,1,6], [7,8,2]], k = 1
///     Output: [1]

use std::collections::BinaryHeap;
use std::cmp::Reverse;

fn min_path(grid: Vec<Vec<i32>>, k: usize) -> Vec<i32> {
    let n = grid.len();
    let mut heap = BinaryHeap::new();
    // Using usize::MAX may lead to underflow, so we use n - 1 to stay within bounds
    let directions = [(0, 1), (1, 0), (n - 1, 0), (0, n - 1)];

    let mut i = 0;
    while i < n {
        let mut j = 0;
        while j < n {
            let mut path = Vec::new();
            path.push(grid[i][j]);
            heap.push((Reverse(grid[i][j]), path, i, j));
            j += 1;
        }
        i += 1;
    }

    while let Some((Reverse(val), mut path, x, y)) = heap.pop() {
        if path.len() == k {
            return path;
        }
        for &(dx, dy) in &directions {
            // Safe addition with bounds checking
            let nx = if dx == n - 1 { x.wrapping_sub(1) } else { x + dx };
            let ny = if dy == n - 1 { y.wrapping_sub(1) } else { y + dy };
            if nx < n && ny < n {
                let mut new_path = path.clone();
                new_path.push(grid[nx][ny]);
                heap.push((Reverse(grid[nx][ny]), new_path, nx, ny));
            }
        }
    }

    Vec::new()
}

fn main() {
    // Example usage:
    let grid = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]];
    let k = 3;
    let path = min_path(grid, k);
    println!("{:?}", path);
}
