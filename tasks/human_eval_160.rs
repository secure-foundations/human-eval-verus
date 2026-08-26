/*
### ID
HumanEval/160
*/
/*
### VERUS BEGIN
*/
use vstd::arithmetic::power::*;
use vstd::prelude::*;

/*
Specification definitions to inspect
* spec_i128_checked_pow, Operator::spec_apply_op, and Expr::eval evaluates an expression tree.
* Operator::spec_precedence, Expr::root_precedence, and Expr::satisfy_precedence specify the precedence rules. An expression is valid if it satisfies the precedence rules.
* Expr::operators and Expr::operands flatten an expression tree into operator and operand sequences.
* construct_from is a spec function that constructs an expression tree from operator and operand sequences.
* In lemma_construct_from, it is proved that the result satisfies the precedence rules, and
* (operators, operands) --construct_from--> expr --(Expr::operators, Expr::operands)--> (operators, operands)
* This two properties gurantee that construct_from gives the desired expression we want to evaluate.
* The linear-time execution function eval_by_stack is verified to return construct_from(operators@, operands@).eval() for every valid input.
*/

verus! {

// A specification of checked_pow(n: i128, m: i128) -> Option<i128>, returns vstd::arithmetic::power::pow if n, m >= 0 and the result does not overflow, and None otherwise.
spec fn spec_i128_checked_pow(n: i128, m: i128) -> Option<i128> {
    if n < 0 || m < 0 {
        None
    } else {
        let res = pow(n as int, m as nat);
        if res > i128::MAX as int {
            None
        } else {
            Some(res as i128)
        }
    }
}

// An implementation of checked_pow(i128, i128) -> Option<i128> using loop and checked_mul which produce the same result as the specification.
exec fn i128_checked_pow(n: i128, m: i128) -> Option<i128>
    returns
        spec_i128_checked_pow(n, m),
    decreases m,
{
    if n < 0 || m < 0 {
        return None;
    }
    proof {
        lemma_pow0(n as int);  // n ** 0 == 1
    }
    if n == 0 {
        if m == 0 {
            return Some(1);
        }
        proof {
            lemma0_pow(m as nat);  // 0 ** m == 0
        }
        return Some(0);
    }
    let mut ret: i128 = 1;
    for i in 0..m
        invariant
            n > 0,
            0 <= i <= m,
            ret as int == pow(n as int, i as nat),
        decreases m - i,
    {
        proof {
            lemma_pow_adds(n as int, i as nat, 1);  // n ** (i + 1) == n ** i * n ** 1
            lemma_pow1(n as int);  // n ** 1 == n
            lemma_pow_positive(n as int, (i + 1) as nat);  // n ** i >= 0
            lemma_pow_increases(n as nat, (i + 1) as nat, m as nat);  // n ** (i + 1) <= n ** m
        }
        match ret.checked_mul(n) {
            None => return None,
            Some(r) => ret = r,
        }
    }
    Some(ret)
}

#[derive(Clone, Copy)]
enum Operator {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
}

// This part defines three helper functions and their specifications counterparts:
// precedence, to get the precedence of an operator. It returns 1 for + and -, 2 for * and /, and 3 for ^.
// need_pop, to determine whether the operator on the top of the stack should be popped when a new operator is encountered.
// apply_op, to apply an operator to two operands and return the result, or None if overflow occurs.
impl Operator {
    spec fn spec_precedence(self) -> u8 {
        match self {
            Operator::Add | Operator::Sub => 1u8,
            Operator::Mul | Operator::Div => 2u8,
            Operator::Pow => 3u8,
        }
    }

    spec fn spec_need_pop(op1: Self, op2: Self) -> bool {
        let p1 = op1.spec_precedence();
        let p2 = op2.spec_precedence();
        p1 > p2 || p1 == p2 && p1 != 3
    }

    spec fn spec_apply_op(self, left: i128, right: i128) -> Option<i128> {
        match self {
            Operator::Add => left.checked_add(right),
            Operator::Sub => left.checked_sub(right),
            Operator::Mul => left.checked_mul(right),
            Operator::Div => left.checked_div(right),
            Operator::Pow => spec_i128_checked_pow(left, right),
        }
    }

    exec fn precedence(&self) -> u8
        returns
            self.spec_precedence(),
    {
        match self {
            Operator::Add | Operator::Sub => 1u8,
            Operator::Mul | Operator::Div => 2u8,
            Operator::Pow => 3u8,
        }
    }

    exec fn need_pop(op1: &Self, op2: &Self) -> bool
        returns
            Operator::spec_need_pop(*op1, *op2),
    {
        let p1 = op1.precedence();
        let p2 = op2.precedence();
        p1 > p2 || p1 == p2 && p1 != 3
    }

    exec fn apply_op(&self, left: i128, right: i128) -> Option<i128>
        returns
            self.spec_apply_op(left, right),
    {
        match self {
            Operator::Add => left.checked_add(right),
            Operator::Sub => left.checked_sub(right),
            Operator::Mul => left.checked_mul(right),
            Operator::Div => left.checked_div(right),
            Operator::Pow => i128_checked_pow(left, right),
        }
    }
}

enum Expr {
    Base(i128),
    Op(Operator, Box<Expr>, Box<Expr>),
}

// These functions appear in the specification
impl Expr {
    // Operator sequence of the infix expression
    spec fn operators(self) -> Seq<Operator>
        decreases self,
    {
        match self {
            Expr::Base(_) => seq![],
            Expr::Op(op, left, right) => left.operators().push(op) + right.operators(),
        }
    }

    // Operand sequence of the infix expression
    spec fn operands(self) -> Seq<i128>
        decreases self,
    {
        match self {
            Expr::Base(n) => seq![n],
            Expr::Op(_, left, right) => left.operands() + right.operands(),
        }
    }

    // Evaluate the expression and return None if overflow occurs in any step.
    spec fn eval(self) -> Option<i128>
        decreases self,
    {
        match self {
            Expr::Base(n) => Some(n),
            Expr::Op(op, left, right) => match (left.eval(), right.eval()) {
                (Some(left), Some(right)) => op.spec_apply_op(left, right),
                _ => None,
            },
        }
    }

    // Precedence of the expression
    spec fn root_precedence(&self) -> u8
        decreases self,
    {
        match self {
            Expr::Base(_) => 4,
            Expr::Op(op, _, _) => op.spec_precedence(),
        }
    }

    // Check if the expression satisfies the precedence rules
    // These conditions make sure that the expression has no brackets
    spec fn satisfy_precedence(self) -> bool
        decreases self,
    {
        match self {
            Expr::Base(_) => true,
            Expr::Op(op, left, right) => {
                left.satisfy_precedence() && right.satisfy_precedence() && if op == Operator::Pow {
                    left.root_precedence() > op.spec_precedence() && right.root_precedence()
                        >= op.spec_precedence()
                } else {
                    left.root_precedence() >= op.spec_precedence() && right.root_precedence()
                        > op.spec_precedence()
                }
            },
        }
    }
}

enum EvalOnceResult {
    Single(i128),
    Overflow,
    Next(Expr),
}

// These are auxiliary functions and lemmas
impl Expr {
    // Constructor
    spec fn mk(op: Operator, left: Expr, right: Expr) -> Expr {
        Expr::Op(op, Box::new(left), Box::new(right))
    }

    // Evaluate the leftmost step of the expression
    // return Overflow if overflow occurs in that step
    // return Single(n) if the expression is a single number n
    // return Next(expr_cur) if the expression is evaluated to expr_cur in that step.
    spec fn eval_once(self) -> EvalOnceResult
        decreases self,
    {
        use Expr::*;
        use EvalOnceResult::*;
        match self {
            Base(n) => Single(n),
            Op(op, left, right) => {
                match left.eval_once() {
                    Single(left_value) => {
                        match right.eval_once() {
                            Single(right_value) => {
                                match op.spec_apply_op(left_value, right_value) {
                                    None => Overflow,
                                    Some(res) => Next(Base(res)),
                                }
                            },
                            Overflow => Overflow,
                            Next(right) => Next(Self::mk(op, Base(left_value), right)),
                        }
                    },
                    Overflow => Overflow,
                    Next(left) => Next(Self::mk(op, left, *right)),
                }
            },
        }
    }

    // eval_once() preserves eval() and satisfy_precedence()
    proof fn lemma_eval_once(&self)
        ensures
            self.eval_once() matches EvalOnceResult::Next(res) ==> self.eval() == res.eval() && (
            self.satisfy_precedence() ==> res.satisfy_precedence()),
            self.eval_once() matches EvalOnceResult::Single(n) ==> self.eval() == Some(n),
            self.eval_once() matches EvalOnceResult::Overflow ==> self.eval() is None,
        decreases self,
    {
        if let Expr::Op(_, left, right) = self {
            left.lemma_eval_once();
            right.lemma_eval_once();
        }
    }

    // The length of the operator sequence plus one equals the length of the operand sequence
    proof fn lemma_len(&self)
        ensures
            self.operators().len() + 1 == self.operands().len(),
        decreases self,
    {
        if let Expr::Op(_, left, right) = self {
            left.lemma_len();
            right.lemma_len();
        }
    }

    // Properties of Expr::Base(n)
    proof fn lemma_base(n: i128)
        ensures
            Expr::Base(n).operators() == seq![],
            Expr::Base(n).operands() == seq![n],
            Expr::Base(n).eval() == Some(n),
            Expr::Base(n).eval_once() == EvalOnceResult::Single(n),
            Expr::Base(n).satisfy_precedence(),
    {
    }

    // Append a new operator and operand to the expression
    spec fn append(self, operator: Operator, operand: i128) -> Expr
        decreases self,
    {
        match self {
            Expr::Base(_) => Expr::mk(operator, self, Expr::Base(operand)),
            Expr::Op(op, left, right) => {
                if Operator::spec_need_pop(op, operator) {
                    Expr::mk(operator, self, Expr::Base(operand))
                } else {
                    Expr::mk(op, *left, right.append(operator, operand))
                }
            },
        }
    }

    // append() has desired effects on operator and operand sequences, and preserves satisfy_precedence()
    proof fn lemma_append(self, operator: Operator, operand: i128)
        ensures
            self.append(operator, operand).operators() == self.operators().push(operator),
            self.append(operator, operand).operands() == self.operands().push(operand),
            self.satisfy_precedence() ==> self.append(operator, operand).satisfy_precedence(),
        decreases self,
    {
        Expr::lemma_base(operand);
        if let Expr::Op(_, _, right) = self {
            right.lemma_append(operator, operand);
        }
    }
}

// Construct the expression tree
spec fn construct_from(operators: Seq<Operator>, operands: Seq<i128>) -> Expr
    recommends
        operators.len() + 1 == operands.len(),
    decreases operators.len(),
{
    if operators.len() == 0 {
        Expr::Base(operands[0])
    } else {
        construct_from(operators.drop_last(), operands.drop_last()).append(
            operators.last(),
            operands.last(),
        )
    }
}

// Correctness of construct_from:
// From operator and operand sequences, construct_from() produces an expression that flattens to the same pair of sequences and satisfies the precedence rules.
proof fn lemma_construct_from(operators: Seq<Operator>, operands: Seq<i128>)
    requires
        operators.len() + 1 == operands.len(),
    ensures
        construct_from(operators, operands).operators() == operators,
        construct_from(operators, operands).operands() == operands,
        construct_from(operators, operands).satisfy_precedence(),
    decreases operators.len(),
{
    if operators.len() == 0 {
        assert(operators == seq![]);
        assert(operands == seq![operands[0]]);
    } else {
        lemma_construct_from(operators.drop_last(), operands.drop_last());
        construct_from(operators.drop_last(), operands.drop_last()).lemma_append(
            operators.last(),
            operands.last(),
        );
    }
}

// The invariant condition of stack
spec fn stack_condition(seq: Seq<Operator>) -> bool {
    forall|i: int|
        0 <= i < seq.len() - 1 ==> !#[trigger] Operator::spec_need_pop(seq[i], seq[i + 1])
}

// !spec_need_pop is transitive, so a sequence satisfying stack_condition is "monotone".
proof fn stack_condition_transitivity(seq: Seq<Operator>, x: int, y: int)
    requires
        0 <= x < y < seq.len(),
        stack_condition(seq),
    ensures
        !Operator::spec_need_pop(seq[x], seq[y]),
    decreases y - x,
{
    assert(!Operator::spec_need_pop(seq[x], seq[x + 1]));
    if x + 1 != y {
        stack_condition_transitivity(seq, x + 1, y);
    }
}

// The expected relation between expr and expr.eval_once()
spec fn reduce_aux_relation(
    operators: Seq<Operator>,
    operands: Seq<i128>,
    res: EvalOnceResult,
    k: int,
    compute: Option<i128>,
) -> bool {
    match compute {
        None => res matches EvalOnceResult::Overflow,
        Some(num) => res matches EvalOnceResult::Next(expr_cur) && expr_cur.operators()
            == operators.take(k) + operators.skip(k + 1) && expr_cur.operands() == operands.take(
            k,
        ).push(num) + operands.skip(k + 2),
    }
}

impl Expr {
    // If the first operator of expr pops op, then the root of expr pops op
    proof fn lemma_right_precedence(self, high: Operator)
        requires
            self.satisfy_precedence(),
            self.operators().len() > 0,
            Operator::spec_need_pop(high, self.operators()[0]),
        ensures
            self matches Expr::Op(op, _, _) ==> Operator::spec_need_pop(high, op),
        decreases self,
    {
        if let Expr::Op(op, left, right) = self {
            if left.operators().len() > 0 {
                left.lemma_right_precedence(high);
            }
        }
    }

    // The main lemma connecting a stack reduction and an expression reduction, which states that
    // the first index in operator sequence that needs to pop corresponds to the step eval_once calculates
    #[verifier::rlimit(30)]
    proof fn lemma_reduce_aux(self, k: int)
        requires
            self.satisfy_precedence(),
            0 <= k < self.operators().len(),
            stack_condition(self.operators().take(k + 1)),
            k + 1 == self.operators().len() || Operator::spec_need_pop(
                self.operators()[k],
                self.operators()[k + 1],
            ),
        ensures
            reduce_aux_relation(
                self.operators(),
                self.operands(),
                self.eval_once(),
                k,
                self.operators()[k].spec_apply_op(self.operands()[k], self.operands()[k + 1]),
            ),
        decreases self,
    {
        if let Expr::Op(op, left, right) = self {
            let left = *left;
            let right = *right;
            if k < left.operators().len() {
                assert(left.operators().take(k + 1) == self.operators().take(k + 1));
                left.lemma_len();
                left.lemma_reduce_aux(k);
                if let Some(num) = self.operators()[k].spec_apply_op(
                    self.operands()[k],
                    self.operands()[k + 1],
                ) {
                    assert(self.operands().take(k).push(num) + self.operands().skip(k + 2)
                        == left.operands().take(k).push(num) + left.operands().skip(k + 2)
                        + right.operands());
                    assert(self.operators().take(k) + self.operators().skip(k + 1)
                        == left.operators().take(k) + left.operators().skip(k + 1).push(op)
                        + right.operators());
                }
            } else {
                if left matches Expr::Op(_, _, _) {
                    assert(left.operators().push(op) == self.operators().take(
                        left.operators().len() + 1 as int,
                    ));
                    if let Expr::Op(old, ll, lr) = left {
                        stack_condition_transitivity(
                            left.operators().push(op),
                            ll.operators().len() as int,
                            (ll.operators().len() + 1 + lr.operators().len()) as int,
                        );
                    }
                }
                if k == left.operators().len() {
                    if let Expr::Base(n) = left {
                        match right {
                            Expr::Op(_, _, _) => {
                                right.lemma_right_precedence(op);
                            },
                            Expr::Base(m) => {
                                Expr::lemma_base(n);
                                Expr::lemma_base(m);
                                if let Some(num) = self.operators()[k].spec_apply_op(
                                    self.operands()[k],
                                    self.operands()[k + 1],
                                ) {
                                    assert(self.operators().take(k) + self.operators().skip(k + 1)
                                        == seq![]);
                                    assert(self.operands().take(k).push(num) + self.operands().skip(
                                        k + 2,
                                    ) == seq![num]);
                                }
                            },
                        }
                    }
                } else {
                    if let Expr::Base(n) = left {
                        let k2 = k - left.operators().len() - 1;
                        assert(stack_condition(right.operators().take(k2 + 1))) by {
                            let seq = right.operators().take(k2 + 1);
                            assert forall|i: int|
                                0 <= i < seq.len() - 1 implies !#[trigger] Operator::spec_need_pop(
                                seq[i],
                                seq[i + 1],
                            ) by {
                                assert(seq[i] == self.operators().take(k + 1)[left.operators().len()
                                    + 1 + i]);
                                assert(seq[i + 1] == self.operators().take(
                                    k + 1,
                                )[left.operators().len() + 1 + i + 1]);
                            }
                        }
                        right.lemma_len();
                        right.lemma_reduce_aux(k2);
                        Expr::lemma_base(n);
                        if let Some(num) = self.operators()[k].spec_apply_op(
                            self.operands()[k],
                            self.operands()[k + 1],
                        ) {
                            assert(self.operands().take(k).push(num) + self.operands().skip(k + 2)
                                == left.operands() + (right.operands().take(k2).push(num)
                                + right.operands().skip(k2 + 2)));
                            assert(self.operators().take(k) + self.operators().skip(k + 1)
                                == left.operators().push(op) + (right.operators().take(k2)
                                + right.operators().skip(k2 + 1)));
                        }
                    }
                }
            }
        }
    }
}

// This lemma proves the special case of the main result. Its condition is that the last operator is Add and the last operand is 0.
// In this case, the stack will be easy to analyze at the end of execution, because the last Add operator will pop all the other operators.
// Most of the execution code goes here.
exec fn eval_by_stack_a(operators: Vec<Operator>, operands: Vec<i128>) -> Option<i128>
    requires
        operators.len() >= 1,
        operators.len() + 1 == operands.len(),
        operators@.last() == Operator::Add,
        operands@.last() == 0,
    returns
        construct_from(operators@, operands@).eval(),
{
    let mut num_stack: Vec<i128> = Vec::new();
    let mut op_stack: Vec<Operator> = Vec::new();
    let ghost mut expr_cur = construct_from(operators@, operands@);
    proof {
        lemma_construct_from(operators@, operands@);
    }

    for i in 0..operators.len()
        invariant
            operators.len() + 1 == operands.len(),  // immutable
            operators@.last() == Operator::Add,  // immutable
            operands@.last() == 0,  // immutable
            0 <= i <= operators.len(),
            num_stack.len() == op_stack.len(),
            expr_cur.eval() == construct_from(operators@, operands@).eval(),
            i == operators.len() ==> op_stack.len() == 1 && op_stack@[0] == Operator::Add,
            stack_condition(op_stack@),
            expr_cur.operators() == op_stack@ + operators@.skip(i as int),
            expr_cur.operands() == num_stack@ + operands@.skip(i as int),
            expr_cur.satisfy_precedence(),
        decreases operators.len() - i,
    {
        num_stack.push(operands[i]);
        while !op_stack.is_empty() && Operator::need_pop(op_stack.last().unwrap(), &operators[i])
            invariant
                i < operators.len(),  // immutable
                num_stack.len() == op_stack.len() + 1,
                stack_condition(op_stack@),
                expr_cur.eval() == construct_from(operators@, operands@).eval(),
                expr_cur.operators() == op_stack@ + operators@.skip(i as int),
                expr_cur.operands() == num_stack@ + operands@.skip(i + 1),
                expr_cur.satisfy_precedence(),
            decreases op_stack.len(),
        {
            let ghost old_num_stack = num_stack@;
            let ghost old_op_stack = op_stack@;
            let right = num_stack.pop().unwrap();
            let left = num_stack.pop().unwrap();
            let op_in_stack = op_stack.pop().unwrap();
            let res = op_in_stack.apply_op(left, right);
            proof {
                expr_cur.lemma_eval_once();
                expr_cur.lemma_reduce_aux(old_op_stack.len() - 1);
            }
            if res.is_none() {
                return None;
            }
            num_stack.push(res.unwrap());
            proof {
                if let EvalOnceResult::Next(expr_nxt) = expr_cur.eval_once() {
                    expr_cur = expr_nxt;
                }
            }
        }
        op_stack.push(operators[i]);
    }
    proof {
        if let Expr::Op(op, left, right) = expr_cur {
            assert(num_stack@.add(operands@.skip(operators.len() as int)) == seq![
                num_stack@[0],
                0,
            ]);
            assert(expr_cur.operators().len() == left.operators().len() + 1
                + right.operators().len());
            match (*left, *right) {
                (Expr::Base(n1), Expr::Base(n2)) => {
                    Expr::lemma_base(n1);
                    Expr::lemma_base(n2);
                    assert(seq![op] == seq![Operator::Add]);
                    assert(seq![op][0] == seq![Operator::Add][0]);
                },
                _ => {},
            }
        }
    }
    num_stack.pop()
}

// This is the main execution function. It calls special case proved above.
exec fn eval_by_stack(operators: Vec<Operator>, operands: Vec<i128>) -> Option<i128>
    requires
        operators.len() + 1 == operands.len(),
    returns
        construct_from(operators@, operands@).eval(),
{
    let mut operators_a = operators;
    operators_a.push(Operator::Add);
    let mut operands_a = operands;
    operands_a.push(0);
    let ghost expr_a = construct_from(operators_a@, operands_a@);
    proof {
        lemma_construct_from(operators_a@, operands_a@);
        Expr::lemma_base(0);
    }
    assert(operators_a@.drop_last() == operators@);
    assert(operands_a@.drop_last() == operands@);
    eval_by_stack_a(operators_a, operands_a)
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def do_algebra(operator, operand):
    """
    Given two lists operator, and operand. The first list has basic algebra operations, and
    the second list is a list of integers. Use the two given lists to build the algebric
    expression and return the evaluation of this expression.

    The basic algebra operations:
    Addition ( + )
    Subtraction ( - )
    Multiplication ( * )
    Floor division ( // )
    Exponentiation ( ** )

    Example:
    operator['+', '*', '-']
    array = [2, 3, 4, 5]
    result = 2 + 3 * 4 - 5
    => result = 9

    Note:
        The length of operator list is equal to the length of operand list minus one.
        Operand is a list of of non-negative integers.
        Operator list has at least one operator, and operand list has at least two operands.

    """

*/

/*
### ENTRY POINT
do_algebra
*/

/*
### CANONICAL SOLUTION
    expression = str(operand[0])
    for oprt, oprn in zip(operator, operand[1:]):
        expression+= oprt + str(oprn)
    return eval(expression)

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate(['**', '*', '+'], [2, 3, 4, 5]) == 37
    assert candidate(['+', '*', '-'], [2, 3, 4, 5]) == 9
    assert candidate(['//', '*'], [7, 3, 4]) == 8, "This prints if this assert fails 1 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"


*/
