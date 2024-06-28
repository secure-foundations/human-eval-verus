/// Write a function that accepts a list of strings as a parameter,
/// deletes the strings that have odd lengths from it,
/// and returns the resulted list with a sorted order,
/// The list is always a list of strings and never an array of numbers,
/// and it may contain duplicates.
/// The order of the list should be ascending by length of each word, and you
/// should return the list sorted by that rule.
/// If two words have the same length, sort the list alphabetically.
/// The function should return a list of strings in sorted order.
/// You may assume that all words will have the same length.
/// For example:
/// assert list_sort(["aa", "a", "aaa"]) => ["aa"]
/// assert list_sort(["ab", "a", "aaa", "cd"]) => ["ab", "cd"]

fn sorted_list_sum(lst: Vec<String>) -> Vec<String> {
    let mut even_length_strings: Vec<String> = lst.into_iter()
        .filter(|s| s.len() % 2 == 0)
        .collect();

    // Implementing a simple bubble sort for demonstration purposes.
    let mut n = even_length_strings.len();
    while n > 0 {
        let mut new_n = 0;
        for i in 1..n {
            if even_length_strings[i - 1].len() > even_length_strings[i].len() ||
               (even_length_strings[i - 1].len() == even_length_strings[i].len() &&
                even_length_strings[i - 1] > even_length_strings[i]) {
                even_length_strings.swap(i - 1, i);
                new_n = i;
            }
        }
        n = new_n;
    }

    even_length_strings
}

fn main() {
    // Example usage:
    let strings = vec![
        "apple".to_string(),
        "banana".to_string(),
        "kiwi".to_string(),
        "cherry".to_string(),
        "mango".to_string(),
    ];
    let sorted_strings = sorted_list_sum(strings);
    for s in sorted_strings {
        println!("{}", s);
    }
}
