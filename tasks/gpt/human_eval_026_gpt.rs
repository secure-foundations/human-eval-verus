/// From a list of integers, remove all elements that occur more than once.
/// Keep order of elements left the same as in the input.
///
/// # Examples
///
/// ```
/// let nums = vec![1, 2, 3, 2, 4];
/// assert_eq!(remove_duplicates(nums), vec![1, 3, 4]);
/// ```

fn remove_duplicates(numbers: Vec<i32>) -> Vec<i32> {
    let mut seen = Vec::new();
    let mut result = Vec::new();

    let mut i = 0;
    while i < numbers.len() {
        let number = numbers[i];
        let mut is_new = true;
        let mut j = 0;
        while j < seen.len() {
            if number == seen[j] {
                is_new = false;
                break;
            }
            j += 1;
        }
        if is_new {
            seen.push(number);
            result.push(number);
        }
        i += 1;
    }

    result
}

fn main() {
    // Example usage:
    let numbers = vec![1, 2, 2, 3, 4, 4, 5];
    let unique_numbers = remove_duplicates(numbers);
    println!("{:?}", unique_numbers);
}
