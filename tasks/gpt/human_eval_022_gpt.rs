/// Filter given list of any values only for integers
///
/// # Examples
///
/// ```
/// let result = filter_integers(vec![Value::String("a".to_string()), Value::Float(3.14), Value::Int(5)]);
/// assert_eq!(result, vec![5]);
///
/// let result = filter_integers(vec![Value::Int(1), Value::Int(2), Value::Int(3), Value::String("abc".to_string()), Value::Map(HashMap::new()), Value::List(vec![])]);
/// assert_eq!(result, vec![1, 2, 3]);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
    // Assuming Value is an enum defined elsewhere in the code with an Int variant
    enum Value {
        Int(i32),
        // ... other variants
    }

    fn filter_integers(values: Vec<Value>) -> (ret: Vec<i32>) {
        let mut result: Vec<i32> = Vec::new();
        let mut i = 0;
        while i < values.len() {
            match values[i] {
                Value::Int(num) => {
                    result.push(num);
                },
                _ => {}
            }
            i += 1;
        }
        result
    }
}
