/*
### ID
HumanEval/160
*/
/*
### VERUS BEGIN
*/
use vstd::arithmetic::power::*;
use vstd::prelude::*;

verus! {

// This part defines
// - Some lemmas about vstd::arithmetic::power::pow
// - A specification of checked_pow(n: i128, m: i128) -> Option<i128>, returns vstd::arithmetic::power::pow if n, m >= 0 and the result does not overflow, and None otherwise.
// - An implementation of checked_pow(n: i128, m: i128) -> Option<i128> using loop and checked_mul which produce the same result as the specification.
proof fn lemma_pow00()
    ensures
        pow(0, 0) == 1,
{
    lemma_pow0(0);
}

proof fn lemma_0pow(n: nat)
    ensures
        pow(0, n) == 0 || pow(0, n) == 1,
{
    if n == 0 {
        lemma_pow00();
    } else {
        lemma0_pow(n);
    }
}

proof fn lemma_pow_add1(n: int, m: nat)
    ensures
        pow(n, m + 1) == pow(n, m) * n,
{
    lemma_pow_adds(n, m, 1);
    lemma_pow1(n);
}

proof fn lemma_pow_nonneg(n: int, m: nat)
    requires
        n >= 0,
    ensures
        pow(n, m) >= 0,
{
    if n > 0 {
        lemma_pow_positive(n, m);
    } else {
        lemma_0pow(m);
    }
}

spec fn spec_i128_checked_pow(n: i128, m: i128) -> (res: Option<i128>) {
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

exec fn i128_checked_pow(n: i128, m: i128) -> (res: Option<i128>)
    returns
        spec_i128_checked_pow(n, m),
    decreases m,
{
    if n < 0 || m < 0 {
        return None;
    }
    let mut ret: i128 = 1;
    proof {
        lemma_pow0(n as int);
    }
    for i in 0..m
        invariant
            n >= 0,
            0 <= i <= m,
            ret as int == pow(n as int, i as nat),
        decreases m - i,
    {
        proof {
            lemma_pow_add1(n as int, i as nat);
            lemma_pow_nonneg(n as int, i as nat);
            lemma_0pow((i + 1) as nat);
        }
        match ret.checked_mul(n) {
            None => {
                if n != 0 {
                    proof {
                        lemma_pow_increases(n as nat, (i + 1) as nat, m as nat);
                    }
                }
                return None;
            },
            Some(r) => {
                ret = r;
            },
        }
    }
    Some(ret)
}

// This part defines a tree structure definition to characterize expression without brackets.
// For each of these level, define
// - .operator() and .operand() to get the operator and operand sequence of the infix expression.
// - .eval() to evaluate the expression and return None if overflow occurs in any step.
// - .from_num(n: i128) to construct an expression from a single number n.
// - .lemma_from_num(n: i128) to prove that .from_num(n) has no operator and the operand is [n]. (MulDivExpr & AddSubExpr)
// - .eval_once() to evaluate the leftmost step of the expression and return Err(None) if overflow occurs in that step, or Err(Some(n)) if the expression is a single number n, or Ok(expr2) if the expression is evaluated to expr2 in that step.
// - .lemma_eval_once() to prove that .eval_once() preserves .eval()
// - .lemma_no_operator() to prove that if .operator() is empty, then the expression is a single number. (AddSubExpr)
// - .lemma_len() to prove that the length of .operator() + 1 equals the length of .operand().
#[derive(Debug)]
pub enum PowExpr {
    Base(i128),
    Pow(i128, Box<PowExpr>),
}

#[derive(Debug)]
pub enum MulDivExpr {
    Factor(PowExpr),
    Mul(Box<MulDivExpr>, Box<PowExpr>),
    Div(Box<MulDivExpr>, Box<PowExpr>),
}

#[derive(Debug)]
pub enum AddSubExpr {
    Term(MulDivExpr),
    Add(Box<AddSubExpr>, Box<MulDivExpr>),
    Sub(Box<AddSubExpr>, Box<MulDivExpr>),
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
enum Operator {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
}

impl PowExpr {
    spec fn operator(&self) -> Seq<Operator>
        decreases self,
    {
        match self {
            PowExpr::Base(_) => seq![],
            PowExpr::Pow(_, right) => seq![Operator::Pow].add(right.operator()),
        }
    }

    spec fn operand(&self) -> Seq<i128>
        decreases self,
    {
        match self {
            PowExpr::Base(coe) => seq![*coe],
            PowExpr::Pow(left, right) => seq![*left].add(right.operand()),
        }
    }

    spec fn eval(&self) -> (res: Option<i128>)
        decreases self,
    {
        match self {
            PowExpr::Base(n) => { Some(*n) },
            PowExpr::Pow(left, right) => {
                match right.eval() {
                    None => None,
                    Some(res) => { spec_i128_checked_pow(*left, res) },
                }
            },
        }
    }

    spec fn from_num(n: i128) -> PowExpr {
        PowExpr::Base(n)
    }

    spec fn eval_once(self) -> Result<PowExpr, Option<i128>>
        decreases self,
    {
        match self {
            PowExpr::Base(n) => Err(Some(n)),
            PowExpr::Pow(left, right) => {
                match right.eval_once() {
                    Err(None) => Err(None),
                    Err(Some(n)) => {
                        match spec_i128_checked_pow(left, n) {
                            None => Err(None),
                            Some(res) => Ok(PowExpr::from_num(res)),
                        }
                    },
                    Ok(right) => Ok(PowExpr::Pow(left, Box::new(right))),
                }
            },
        }
    }

    proof fn lemma_eval_once(&self)
        ensures
            self.eval_once() matches Ok(res) ==> self.eval() == res.eval(),
            self.eval_once() matches Err(res) ==> self.eval() == res,
        decreases self,
    {
        match self {
            PowExpr::Base(_) => {},
            PowExpr::Pow(_, right) => {
                right.lemma_eval_once();
            },
        }
    }

    proof fn lemma_len(&self)
        ensures
            self.operator().len() + 1 == self.operand().len(),
        decreases self,
    {
        match self {
            PowExpr::Base(_) => {},
            PowExpr::Pow(_, right) => {
                right.lemma_len();
            },
        }
    }
}

spec fn and_then2<T, U, V>(a: Option<T>, b: Option<U>, f: spec_fn(T, U) -> Option<V>) -> Option<V> {
    match a {
        None => None,
        Some(x) => match b {
            None => None,
            Some(y) => f(x, y),
        },
    }
}

impl MulDivExpr {
    spec fn operator(&self) -> Seq<Operator>
        decreases self,
    {
        match self {
            MulDivExpr::Factor(factor) => factor.operator(),
            MulDivExpr::Mul(left, right) => left.operator().add(seq![Operator::Mul]).add(
                right.operator(),
            ),
            MulDivExpr::Div(left, right) => left.operator().add(seq![Operator::Div]).add(
                right.operator(),
            ),
        }
    }

    spec fn operand(&self) -> Seq<i128>
        decreases self,
    {
        match self {
            MulDivExpr::Factor(factor) => factor.operand(),
            MulDivExpr::Mul(left, right) => left.operand().add(right.operand()),
            MulDivExpr::Div(left, right) => left.operand().add(right.operand()),
        }
    }

    spec fn eval(&self) -> Option<i128>
        decreases self,
    {
        match self {
            MulDivExpr::Factor(factor) => factor.eval(),
            MulDivExpr::Mul(left, right) => and_then2(
                left.eval(),
                right.eval(),
                |l: i128, r: i128| l.checked_mul(r),
            ),
            MulDivExpr::Div(left, right) => and_then2(
                left.eval(),
                right.eval(),
                |l: i128, r: i128| l.checked_div(r),
            ),
        }
    }

    spec fn from_num(n: i128) -> MulDivExpr {
        MulDivExpr::Factor(PowExpr::Base(n))
    }

    proof fn lemma_from_num(n: i128)
        ensures
            MulDivExpr::from_num(n).operator() == Seq::<Operator>::empty(),
            MulDivExpr::from_num(n).operand() == seq![n],
    {
    }

    spec fn eval_once(self) -> Result<MulDivExpr, Option<i128>>
        decreases self,
    {
        match self {
            MulDivExpr::Factor(factor) => {
                match factor.eval_once() {
                    Err(None) => Err(None),
                    Err(Some(n)) => Err(Some(n)),
                    Ok(factor) => Ok(MulDivExpr::Factor(factor)),
                }
            },
            MulDivExpr::Mul(left, right) => {
                match left.eval_once() {
                    Err(None) => Err(None),
                    Err(Some(n)) => {
                        match right.eval_once() {
                            Err(None) => Err(None),
                            Err(Some(m)) => {
                                match n.checked_mul(m) {
                                    None => Err(None),
                                    Some(res) => Ok(MulDivExpr::from_num(res)),
                                }
                            },
                            Ok(right) => Ok(
                                MulDivExpr::Mul(Box::new(MulDivExpr::from_num(n)), Box::new(right)),
                            ),
                        }
                    },
                    Ok(left) => Ok(MulDivExpr::Mul(Box::new(left), right)),
                }
            },
            MulDivExpr::Div(left, right) => {
                match left.eval_once() {
                    Err(None) => Err(None),
                    Err(Some(n)) => {
                        match right.eval_once() {
                            Err(None) => Err(None),
                            Err(Some(m)) => {
                                match n.checked_div(m) {
                                    None => Err(None),
                                    Some(res) => Ok(MulDivExpr::from_num(res)),
                                }
                            },
                            Ok(right) => Ok(
                                MulDivExpr::Div(Box::new(MulDivExpr::from_num(n)), Box::new(right)),
                            ),
                        }
                    },
                    Ok(left) => Ok(MulDivExpr::Div(Box::new(left), right)),
                }
            },
        }
    }

    proof fn lemma_eval_once(&self)
        ensures
            self.eval_once() matches Ok(res) ==> self.eval() == res.eval(),
            self.eval_once() matches Err(res) ==> self.eval() == res,
        decreases self,
    {
        match self {
            MulDivExpr::Factor(factor) => {
                factor.lemma_eval_once();
            },
            MulDivExpr::Mul(left, right) => {
                left.lemma_eval_once();
                right.lemma_eval_once();
            },
            MulDivExpr::Div(left, right) => {
                left.lemma_eval_once();
                right.lemma_eval_once();
            },
        }
    }

    proof fn lemma_len(&self)
        ensures
            self.operator().len() + 1 == self.operand().len(),
        decreases self,
    {
        match self {
            MulDivExpr::Factor(factor) => {
                factor.lemma_len();
            },
            MulDivExpr::Mul(left, right) => {
                left.lemma_len();
                right.lemma_len();
            },
            MulDivExpr::Div(left, right) => {
                left.lemma_len();
                right.lemma_len();
            },
        }
    }
}

impl AddSubExpr {
    spec fn operator(&self) -> Seq<Operator>
        decreases self,
    {
        match self {
            AddSubExpr::Term(term) => term.operator(),
            AddSubExpr::Add(left, right) => left.operator().add(seq![Operator::Add]).add(
                right.operator(),
            ),
            AddSubExpr::Sub(left, right) => left.operator().add(seq![Operator::Sub]).add(
                right.operator(),
            ),
        }
    }

    spec fn operand(&self) -> Seq<i128>
        decreases self,
    {
        match self {
            AddSubExpr::Term(term) => term.operand(),
            AddSubExpr::Add(left, right) => left.operand().add(right.operand()),
            AddSubExpr::Sub(left, right) => left.operand().add(right.operand()),
        }
    }

    spec fn eval(&self) -> Option<i128>
        decreases self,
    {
        match self {
            AddSubExpr::Term(term) => term.eval(),
            AddSubExpr::Add(left, right) => {
                let ghost left = left.eval();
                let ghost right = right.eval();
                and_then2(left, right, |l: i128, r: i128| l.checked_add(r))
            },
            AddSubExpr::Sub(left, right) => {
                let ghost left = left.eval();
                let ghost right = right.eval();
                and_then2(left, right, |l: i128, r: i128| l.checked_sub(r))
            },
        }
    }

    spec fn from_num(n: i128) -> AddSubExpr {
        AddSubExpr::Term(MulDivExpr::from_num(n))
    }

    proof fn lemma_from_num(n: i128)
        ensures
            AddSubExpr::from_num(n).operator() == Seq::<Operator>::empty(),
            AddSubExpr::from_num(n).operand() == seq![n],
    {
    }

    spec fn eval_once(self) -> Result<AddSubExpr, Option<i128>>
        decreases self,
    {
        match self {
            AddSubExpr::Term(term) => {
                match term.eval_once() {
                    Err(res) => Err(res),
                    Ok(term) => Ok(AddSubExpr::Term(term)),
                }
            },
            AddSubExpr::Add(left, right) => {
                match left.eval_once() {
                    Err(None) => Err(None),
                    Err(Some(n)) => {
                        match right.eval_once() {
                            Err(None) => Err(None),
                            Err(Some(m)) => {
                                match spec_apply_op(n, m, Operator::Add) {
                                    None => Err(None),
                                    Some(res) => Ok(AddSubExpr::from_num(res)),
                                }
                            },
                            Ok(right) => Ok(
                                AddSubExpr::Add(Box::new(AddSubExpr::from_num(n)), Box::new(right)),
                            ),
                        }
                    },
                    Ok(left) => Ok(AddSubExpr::Add(Box::new(left), Box::new(*right))),
                }
            },
            AddSubExpr::Sub(left, right) => {
                match left.eval_once() {
                    Err(None) => Err(None),
                    Err(Some(n)) => {
                        match right.eval_once() {
                            Err(None) => Err(None),
                            Err(Some(m)) => {
                                match spec_apply_op(n, m, Operator::Sub) {
                                    None => Err(None),
                                    Some(res) => Ok(AddSubExpr::from_num(res)),
                                }
                            },
                            Ok(right) => Ok(
                                AddSubExpr::Sub(Box::new(AddSubExpr::from_num(n)), Box::new(right)),
                            ),
                        }
                    },
                    Ok(left) => Ok(AddSubExpr::Sub(Box::new(left), Box::new(*right))),
                }
            },
        }
    }

    proof fn lemma_eval_once(&self)
        ensures
            self.eval_once() matches Ok(res) ==> self.eval() == res.eval(),
            self.eval_once() matches Err(res) ==> self.eval() == res,
        decreases self,
    {
        match self {
            AddSubExpr::Term(term) => {
                term.lemma_eval_once();
            },
            AddSubExpr::Add(left, right) => {
                left.lemma_eval_once();
                right.lemma_eval_once();
            },
            AddSubExpr::Sub(left, right) => {
                left.lemma_eval_once();
                right.lemma_eval_once();
            },
        }
    }

    proof fn lemma_no_operator(&self)
        requires
            self.operator().len() == 0,
        ensures
            self matches AddSubExpr::Term(MulDivExpr::Factor(PowExpr::Base(_))),
    {
    }

    proof fn lemma_len(&self)
        ensures
            self.operator().len() + 1 == self.operand().len(),
        decreases self,
    {
        match self {
            AddSubExpr::Term(term) => {
                term.lemma_len();
            },
            AddSubExpr::Add(left, right) => {
                left.lemma_len();
                right.lemma_len();
            },
            AddSubExpr::Sub(left, right) => {
                left.lemma_len();
                right.lemma_len();
            },
        }
    }
}

// This part defines three helper functions and their specifications counterparts:
// precedence(Operator), to get the precedence of an operator. It returns 1 for + and -, 2 for * and /, and 3 for ^.
// need_pop, to determine whether the operator on the top of the stack should be popped when a new operator is encountered.
// apply_op, to apply an operator to two operands and return the result, or None if overflow occurs.
spec fn spec_precedence(op: Operator) -> (res: u8) {
    match op {
        Operator::Add => 1u8,
        Operator::Sub => 1u8,
        Operator::Mul => 2u8,
        Operator::Div => 2u8,
        Operator::Pow => 3u8,
    }
}

spec fn spec_need_pop(op1: Operator, op2: Operator) -> (res: bool) {
    let p1 = spec_precedence(op1);
    let p2 = spec_precedence(op2);
    if p1 != p2 {
        p1 > p2
    } else {
        match op1 {
            Operator::Pow => false,
            _ => true,
        }
    }
}

spec fn spec_apply_op(left: i128, right: i128, op: Operator) -> (res: Option<i128>) {
    match op {
        Operator::Add => left.checked_add(right),
        Operator::Sub => left.checked_sub(right),
        Operator::Mul => left.checked_mul(right),
        Operator::Div => left.checked_div(right),
        Operator::Pow => spec_i128_checked_pow(left, right),
    }
}

exec fn precedence(op: &Operator) -> (res: u8)
    returns
        spec_precedence(*op),
{
    match op {
        Operator::Add => 1,
        Operator::Sub => 1,
        Operator::Mul => 2,
        Operator::Div => 2,
        Operator::Pow => 3,
    }
}

exec fn need_pop(op1: &Operator, op2: &Operator) -> (res: bool)
    ensures
        op2 == Operator::Add ==> res == true,
        res == spec_need_pop(*op1, *op2),
{
    let p1 = precedence(op1);
    let p2 = precedence(op2);
    if p1 != p2 {
        p1 > p2
    } else {
        match op1 {
            Operator::Pow => false,
            _ => true,
        }
    }
}

exec fn apply_op(left: i128, right: i128, op: Operator) -> (res: Option<i128>)
    ensures
        res == spec_apply_op(left, right, op),
{
    match op {
        Operator::Add => left.checked_add(right),
        Operator::Sub => left.checked_sub(right),
        Operator::Mul => left.checked_mul(right),
        Operator::Div => left.checked_div(right),
        Operator::Pow => i128_checked_pow(left, right),
    }
}

// This part defines complex functions on operator stack.
// - stack_condition(Seq<Operator>) to state the invariant condition of stack
// - .lemma_operator_type(k: int) to prove that the operator at index k has the correct precedence. (PowExpr & MulDivExpr)
// - .lemma_stack_num(op: Operator) to prove that if an expression's operator sequence plus a new operator op satisfies stack_condition, then the expression is a single number. (MulDivExpr & AddSubExpr)
spec fn stack_condition(seq: Seq<Operator>) -> bool {
    forall|i: int| 0 <= i < seq.len() - 1 ==> !#[trigger] spec_need_pop(seq[i], seq[i + 1])
}

impl PowExpr {
    proof fn lemma_operator_type(self, k: int)
        requires
            0 <= k < self.operator().len(),
        ensures
            spec_precedence(self.operator()[k]) > 2,
        decreases self,
    {
        match self {
            PowExpr::Base(_) => {},
            PowExpr::Pow(_, right) => {
                if k > 0 {
                    right.lemma_operator_type(k - 1);
                }
            },
        }
    }
}

impl MulDivExpr {
    proof fn lemma_operator_type(self, k: int)
        requires
            0 <= k < self.operator().len(),
        ensures
            spec_precedence(self.operator()[k]) > 1,
        decreases self,
    {
        match self {
            MulDivExpr::Factor(factor) => {
                factor.lemma_operator_type(k);
            },
            MulDivExpr::Mul(left, right) => {
                if k < left.operator().len() {
                    left.lemma_operator_type(k);
                } else if k == left.operator().len() {
                } else {
                    right.lemma_operator_type(k - left.operator().len() - 1);
                }
            },
            MulDivExpr::Div(left, right) => {
                if k < left.operator().len() {
                    left.lemma_operator_type(k);
                } else if k == left.operator().len() {
                } else {
                    right.lemma_operator_type(k - left.operator().len() - 1);
                }
            },
        }
    }

    proof fn lemma_stack_num(self, op: Operator)
        requires
            spec_precedence(op) <= 2,
            stack_condition(self.operator().push(op)),
        ensures
            self matches MulDivExpr::Factor(PowExpr::Base(_)),
    {
        if (self.operator().len() > 0) {
            self.lemma_operator_type(self.operator().len() - 1);
            assert(spec_need_pop(
                self.operator().push(op)[self.operator().len() - 1],
                self.operator().push(op)[(self.operator().len() - 1) + 1],
            ));
        }
    }
}

impl AddSubExpr {
    proof fn lemma_stack_num(self, op: Operator)
        requires
            spec_precedence(op) == 1,
            stack_condition(self.operator().push(op)),
        ensures
            self matches AddSubExpr::Term(MulDivExpr::Factor(PowExpr::Base(_))),
    {
        if (self.operator().len() > 0) {
            assert(spec_need_pop(
                self.operator().push(op)[self.operator().len() - 1],
                self.operator().push(op)[(self.operator().len() - 1) + 1],
            ));
        }
    }
}

// This lemma proves that a subrange of a sequence satisfying stack_condition
// also satisfies stack_condition.
proof fn lemma_stack_condition_subrange(seq: Seq<Operator>, start: int, end: int)
    requires
        stack_condition(seq),
        0 <= start <= end <= seq.len(),
    ensures
        stack_condition(seq.subrange(start, end)),
{
    assert forall|i: int|
        0 <= i < seq.subrange(start, end).len() - 1 implies !#[trigger] spec_need_pop(
        seq.subrange(start, end)[i],
        seq.subrange(start, end)[i + 1],
    ) by {
        assert(seq.subrange(start, end)[i + 1] == seq[start + i + 1]);
    }
}

spec fn some_spec(expr: AddSubExpr, operator: Seq<Operator>, operand: Seq<i128>) -> bool {
    expr.operator() == operator && expr.operand() == operand
}

// This part defines the main lemmas connecting a stack reduction and an expression reduction.
// Each one basically says: the first index in expr.operator() that needs to pop corresponds to expr.eval_once()
// _merge functions are used to prevent an oversized proof tree, and merge similar proof
proof fn lemma_reduce_pow(expr: PowExpr, k: int)
    requires
        0 <= k < expr.operator().len(),
        stack_condition(expr.operator().subrange(0, k + 1)),
        k + 1 == expr.operator().len() || spec_need_pop(expr.operator()[k], expr.operator()[k + 1]),
    ensures
        match spec_apply_op(expr.operand()[k], expr.operand()[k + 1], expr.operator()[k]) {
            None => expr.eval_once() matches Err(None),
            Some(num) => expr.eval_once() matches Ok(expr2) && expr2.operator()
                == expr.operator().subrange(0, k).add(
                expr.operator().subrange(k + 1, expr.operator().len() as int),
            ) && expr2.operand() == expr.operand().subrange(0, k).add(seq![num]).add(
                expr.operand().subrange(k + 2, expr.operand().len() as int),
            ),
        },
    decreases expr,
{
    match expr {
        PowExpr::Base(base) => {},
        PowExpr::Pow(left, right) => {
            if k != 0 {
                let k2 = k - 1;
                assert(right.operator().subrange(0, k2 + 1) == expr.operator().subrange(
                    0,
                    k + 1,
                ).subrange(1, k + 1));
                right.lemma_len();
                lemma_reduce_pow(*right, k - 1);
            }
        },
    }
}

proof fn lemma_reduce_muldiv_merge(
    left: MulDivExpr,
    right: PowExpr,
    k: int,
    op: Operator,
    operator: Seq<Operator>,
    operand: Seq<i128>,
    eval_once: Result<MulDivExpr, Option<i128>>,
)
    requires
        0 <= k < operator.len(),
        stack_condition(operator.subrange(0, k + 1)),
        k + 1 == operator.len() || spec_need_pop(operator[k], operator[k + 1]),
        operator == left.operator().add(seq![op]).add(right.operator()),
        operand == left.operand().add(right.operand()),
        left.eval_once() matches Err(None) ==> eval_once matches Err(None),
        left.eval_once() matches Err(Some(n1)) ==> right.eval_once() matches Err(Some(n2))
            ==> spec_apply_op(n1, n2, op) is None ==> eval_once matches Err(None),
        left.eval_once() matches Err(Some(n1)) ==> right.eval_once() matches Err(Some(n2))
            ==> spec_apply_op(n1, n2, op) matches Some(n3) ==> eval_once == Ok::<
            MulDivExpr,
            Option<i128>,
        >(MulDivExpr::from_num(n3)),
        left.eval_once() matches Err(Some(n1)) ==> right.eval_once() matches Err(None)
            ==> eval_once matches Err(None),
        left.eval_once() matches Err(Some(n1)) ==> right.eval_once() matches Ok(right2)
            ==> eval_once matches Ok(expr2) && expr2.operator() == seq![op].add(right2.operator())
            && expr2.operand() == seq![n1].add(right2.operand()),
        left.eval_once() matches Ok(left2) ==> eval_once matches Ok(expr2) && expr2.operator()
            == left2.operator().add(seq![op]).add(right.operator()) && expr2.operand()
            == left2.operand().add(right.operand()),
        spec_precedence(op) <= 2,
    ensures
        match spec_apply_op(operand[k], operand[k + 1], operator[k]) {
            None => eval_once matches Err(None),
            Some(num) => eval_once matches Ok(expr2) && expr2.operator() == operator.subrange(
                0,
                k,
            ).add(operator.subrange(k + 1, operator.len() as int)) && expr2.operand()
                == operand.subrange(0, k).add(seq![num]).add(
                operand.subrange(k + 2, operand.len() as int),
            ),
        },
    decreases left, 1int,
{
    if k < left.operator().len() {
        assert(left.operator().subrange(0, k + 1) == operator.subrange(0, k + 1));
        left.lemma_len();
        lemma_reduce_muldiv(left, k);
    } else if k == left.operator().len() {
        assert(left.operator().push(op) == operator.subrange(0, k + 1));
        left.lemma_stack_num(op);
    } else {
        let k2 = k - left.operator().len() - 1;
        assert(right.operator().subrange(0, k2 + 1) == operator.subrange(0, k + 1).subrange(
            left.operator().len() + 1 as int,
            k + 1,
        ));
        lemma_stack_condition_subrange(
            operator.subrange(0, k + 1),
            left.operator().len() + 1 as int,
            k + 1,
        );
        left.lemma_len();
        right.lemma_len();
        lemma_reduce_pow(right, k - left.operator().len() - 1);
        assert(left.operator().push(op) == operator.subrange(0, left.operator().len() + 1 as int));
        left.lemma_stack_num(op);
    }
}

proof fn lemma_reduce_muldiv(expr: MulDivExpr, k: int)
    requires
        0 <= k < expr.operator().len(),
        stack_condition(expr.operator().subrange(0, k + 1)),
        k + 1 == expr.operator().len() || spec_need_pop(expr.operator()[k], expr.operator()[k + 1]),
    ensures
        match spec_apply_op(expr.operand()[k], expr.operand()[k + 1], expr.operator()[k]) {
            None => expr.eval_once() matches Err(None),
            Some(num) => expr.eval_once() matches Ok(expr2) && expr2.operator()
                == expr.operator().subrange(0, k).add(
                expr.operator().subrange(k + 1, expr.operator().len() as int),
            ) && expr2.operand() == expr.operand().subrange(0, k).add(seq![num]).add(
                expr.operand().subrange(k + 2, expr.operand().len() as int),
            ),
        },
    decreases expr, 0int,
{
    match expr {
        MulDivExpr::Factor(factor) => {
            lemma_reduce_pow(factor, k);
        },
        MulDivExpr::Mul(left, right) => {
            match (left.eval_once(), right.eval_once()) {
                (Err(Some(n1)), Ok(right2)) => {
                    MulDivExpr::lemma_from_num(n1);
                },
                _ => {},
            }
            assert(left.eval_once() matches Err(Some(n1)) ==> right.eval_once() matches Ok(right2)
                ==> expr.eval_once() matches Ok(expr2) && expr2.operator() == Seq::empty().push(
                Operator::Mul,
            ).add(right2.operator()) && expr2.operand() == seq![n1].add(right2.operand()));
            lemma_reduce_muldiv_merge(
                *left,
                *right,
                k,
                Operator::Mul,
                expr.operator(),
                expr.operand(),
                expr.eval_once(),
            );
        },
        MulDivExpr::Div(left, right) => {
            match (left.eval_once(), right.eval_once()) {
                (Err(Some(n1)), Ok(right2)) => {
                    MulDivExpr::lemma_from_num(n1);
                },
                _ => {},
            }
            assert(left.eval_once() matches Err(Some(n1)) ==> right.eval_once() matches Ok(right2)
                ==> expr.eval_once() matches Ok(expr2) && expr2.operator() == Seq::empty().push(
                Operator::Div,
            ).add(right2.operator()) && expr2.operand() == seq![n1].add(right2.operand()));
            lemma_reduce_muldiv_merge(
                *left,
                *right,
                k,
                Operator::Div,
                expr.operator(),
                expr.operand(),
                expr.eval_once(),
            );
        },
    }
}

#[verifier::rlimit(20)]
proof fn lemma_reduce_addsub_merge(
    left: AddSubExpr,
    right: MulDivExpr,
    k: int,
    op: Operator,
    operator: Seq<Operator>,
    operand: Seq<i128>,
    eval_once: Result<AddSubExpr, Option<i128>>,
)
    requires
        0 <= k < operator.len(),
        stack_condition(operator.subrange(0, k + 1)),
        k + 1 == operator.len() || spec_need_pop(operator[k], operator[k + 1]),
        operator == left.operator().add(seq![op]).add(right.operator()),
        operand == left.operand().add(right.operand()),
        left.eval_once() matches Err(None) ==> eval_once matches Err(None),
        left.eval_once() matches Err(Some(n1)) ==> right.eval_once() matches Err(Some(n2))
            ==> spec_apply_op(n1, n2, op) is None ==> eval_once matches Err(None),
        left.eval_once() matches Err(Some(n1)) ==> right.eval_once() matches Err(Some(n2))
            ==> spec_apply_op(n1, n2, op) matches Some(n3) ==> eval_once == Ok::<
            AddSubExpr,
            Option<i128>,
        >(AddSubExpr::from_num(n3)),
        left.eval_once() matches Err(Some(n1)) ==> right.eval_once() matches Err(None)
            ==> eval_once matches Err(None),
        left.eval_once() matches Err(Some(n1)) ==> right.eval_once() matches Ok(right2)
            ==> eval_once matches Ok(expr2) && expr2.operator() == seq![op].add(right2.operator())
            && expr2.operand() == seq![n1].add(right2.operand()),
        left.eval_once() matches Ok(left2) ==> eval_once matches Ok(expr2) && expr2.operator()
            == left2.operator().add(seq![op]).add(right.operator()) && expr2.operand()
            == left2.operand().add(right.operand()),
        spec_precedence(op) == 1,
    ensures
        match spec_apply_op(operand[k], operand[k + 1], operator[k]) {
            None => eval_once matches Err(None),
            Some(num) => eval_once matches Ok(expr2) && expr2.operator() == operator.subrange(
                0,
                k,
            ).add(operator.subrange(k + 1, operator.len() as int)) && expr2.operand()
                == operand.subrange(0, k).add(seq![num]).add(
                operand.subrange(k + 2, operand.len() as int),
            ),
        },
    decreases left, 1int,
{
    if k < left.operator().len() {
        assert(left.operator().subrange(0, k + 1) == operator.subrange(0, k + 1));
        left.lemma_len();
        lemma_reduce_addsub(left, k);
    } else if k == left.operator().len() {
        if (k + 1 < operator.len()) {
            right.lemma_operator_type(0);
        }
        assert(left.operator().push(op) == operator.subrange(0, k + 1));
        left.lemma_stack_num(op);
    } else {
        let k2 = k - left.operator().len() - 1;
        assert(right.operator().subrange(0, k2 + 1) == operator.subrange(0, k + 1).subrange(
            left.operator().len() + 1 as int,
            k + 1,
        ));
        lemma_stack_condition_subrange(
            operator.subrange(0, k + 1),
            left.operator().len() + 1 as int,
            k + 1,
        );
        left.lemma_len();
        right.lemma_len();
        lemma_reduce_muldiv(right, k - left.operator().len() - 1);
        assert(left.operator().push(op) == operator.subrange(0, left.operator().len() + 1 as int));
        left.lemma_stack_num(op);
    }
}

proof fn lemma_reduce_addsub(expr: AddSubExpr, k: int)
    requires
        0 <= k < expr.operator().len(),
        stack_condition(expr.operator().subrange(0, k + 1)),
        k + 1 == expr.operator().len() || spec_need_pop(expr.operator()[k], expr.operator()[k + 1]),
    ensures
        match spec_apply_op(expr.operand()[k], expr.operand()[k + 1], expr.operator()[k]) {
            None => expr.eval_once() matches Err(None),
            Some(num) => expr.eval_once() matches Ok(expr2) && expr2.operator()
                == expr.operator().subrange(0, k).add(
                expr.operator().subrange(k + 1, expr.operator().len() as int),
            ) && expr2.operand() == expr.operand().subrange(0, k).add(seq![num]).add(
                expr.operand().subrange(k + 2, expr.operand().len() as int),
            ),
        },
    decreases expr, 0int,
{
    match expr {
        AddSubExpr::Term(term) => {
            lemma_reduce_muldiv(term, k);
        },
        AddSubExpr::Add(left, right) => {
            match (left.eval_once(), right.eval_once()) {
                (Err(Some(n1)), Ok(right2)) => {
                    AddSubExpr::lemma_from_num(n1);
                },
                _ => {},
            }
            assert(left.eval_once() matches Err(Some(n1)) ==> right.eval_once() matches Ok(right2)
                ==> expr.eval_once() matches Ok(expr2) && expr2.operator() == Seq::empty().push(
                Operator::Add,
            ).add(right2.operator()) && expr2.operand() == seq![n1].add(right2.operand()));
            lemma_reduce_addsub_merge(
                *left,
                *right,
                k,
                Operator::Add,
                expr.operator(),
                expr.operand(),
                expr.eval_once(),
            );
        },
        AddSubExpr::Sub(left, right) => {
            match (left.eval_once(), right.eval_once()) {
                (Err(Some(n1)), Ok(right2)) => {
                    AddSubExpr::lemma_from_num(n1);
                },
                _ => {},
            }
            assert(left.eval_once() matches Err(Some(n1)) ==> right.eval_once() matches Ok(right2)
                ==> expr.eval_once() matches Ok(expr2) && expr2.operator() == Seq::empty().push(
                Operator::Sub,
            ).add(right2.operator()) && expr2.operand() == seq![n1].add(right2.operand()));
            lemma_reduce_addsub_merge(
                *left,
                *right,
                k,
                Operator::Sub,
                expr.operator(),
                expr.operand(),
                expr.eval_once(),
            );
        },
    }
}

// This part defines two interface lemmas connecting the proof call in the execution function and the expression reduction lemmas above.
proof fn lemma_reduce_err(
    expr: AddSubExpr,
    num_st: Seq<i128>,
    op_st: Seq<Operator>,
    operator: Seq<Operator>,
    operand: Seq<i128>,
)
    requires
        some_spec(expr, op_st.add(operator), num_st.add(operand)),
        stack_condition(op_st),
        op_st.len() + 1 == num_st.len(),
        num_st.len() >= 2,
        spec_apply_op(
            num_st[num_st.len() - 2],
            num_st[num_st.len() - 1],
            op_st[op_st.len() - 1],
        ) is None,
        operator.len() > 0,
        spec_need_pop(op_st[op_st.len() - 1], operator[0]),
    ensures
        expr.eval_once() matches Err(None),
{
    let k = op_st.len() - 1;
    lemma_reduce_addsub(expr, op_st.len() - 1);
}

proof fn lemma_reduce_ok(
    expr: AddSubExpr,
    num_st: Seq<i128>,
    op_st: Seq<Operator>,
    operator: Seq<Operator>,
    operand: Seq<i128>,
    num: i128,
)
    requires
        some_spec(expr, op_st.add(operator), num_st.add(operand)),
        stack_condition(op_st),
        op_st.len() + 1 == num_st.len(),
        num_st.len() >= 2,
        spec_apply_op(num_st[num_st.len() - 2], num_st[num_st.len() - 1], op_st[op_st.len() - 1])
            == Some(num),
        operator.len() > 0,
        spec_need_pop(op_st[op_st.len() - 1], operator[0]),
    ensures
        expr.eval_once() matches Ok(expr2) && some_spec(
            expr2,
            op_st.subrange(0, op_st.len() - 1).add(operator),
            num_st.subrange(0, num_st.len() - 2).add(seq![num]).add(operand),
        ),
{
    let k = op_st.len() - 1;
    lemma_reduce_addsub(expr, op_st.len() - 1);
    assert(expr.operator().subrange(0, k).add(
        expr.operator().subrange(k + 1, expr.operator().len() as int),
    ) == op_st.subrange(0, op_st.len() - 1).add(operator));
    assert(expr.operand().subrange(0, k).add(seq![num]).add(
        expr.operand().subrange(k + 2, expr.operand().len() as int),
    ) == num_st.subrange(0, num_st.len() - 2).add(seq![num]).add(operand));
}

// This lemma deals with the end of execution.
proof fn lemma_simple_expr_reverse(expr: AddSubExpr, x: i128)
    requires
        expr.operator() == seq![Operator::Add] && expr.operand() == seq![x, 0],
    ensures
        expr.eval() == Some(x),
{
    match expr {
        AddSubExpr::Term(MulDivExpr::Factor(PowExpr::Base(n))) => {
            assert(expr.operator() == Seq::<Operator>::empty());
        },
        AddSubExpr::Term(MulDivExpr::Factor(PowExpr::Pow(left, right))) => {
            assert(expr.operator() == seq![Operator::Pow].add(right.operator()));
            assert(expr.operator()[0] == Operator::Pow);
        },
        AddSubExpr::Term(MulDivExpr::Mul(left, right)) => {
            assert(expr.operator() == left.operator().add(seq![Operator::Mul]).add(
                right.operator(),
            ));
            assert(expr.operator()[left.operator().len() as int] == Operator::Mul);
        },
        AddSubExpr::Term(MulDivExpr::Div(left, right)) => {
            assert(expr.operator() == left.operator().add(seq![Operator::Div]).add(
                right.operator(),
            ));
            assert(expr.operator()[left.operator().len() as int] == Operator::Div);
        },
        AddSubExpr::Sub(left, right) => {
            assert(expr.operator() == left.operator().add(seq![Operator::Sub]).add(
                right.operator(),
            ));
            assert(expr.operator()[left.operator().len() as int] == Operator::Sub);
        },
        AddSubExpr::Add(left, right) => {
            left.lemma_no_operator();
            match *left {
                AddSubExpr::Term(MulDivExpr::Factor(PowExpr::Base(n1))) => {
                    match *right {
                        MulDivExpr::Factor(PowExpr::Base(n2)) => {
                            assert(expr.operand() == left.operand().add(right.operand()));
                            assert(x == n1);
                            assert(0 == n2);
                            assert(left.eval() == Some(n1));
                            assert(right.eval() == Some(0 as i128));
                            assert(expr.eval() == n1.checked_add(0));
                        },
                        _ => {
                            assert(false);
                        },
                    }
                },
                _ => {},
            }
        },
    }
}

// This lemma proves the special case of the main result. Its condition is that the last operator is Add and the last operand is 0.
// Most of the execution code goes here.
exec fn eval_by_stack_a(operator: Vec<Operator>, operand: Vec<i128>) -> (res: Option<i128>)
    requires
        operator.len() >= 1,
        operator.len() == operand.len() - 1,
        operator@.last() == Operator::Add,
        operand@.last() == 0,
    ensures
        forall|expr: AddSubExpr| #[trigger]
            some_spec(expr, operator@, operand@) ==> res == expr.eval(),
{
    let mut num_stack: Vec<i128> = Vec::new();
    let mut op_stack: Vec<Operator> = Vec::new();

    assert forall|expr: AddSubExpr| #[trigger] some_spec(expr, operator@, operand@) implies (exists|
        expr2: AddSubExpr,
    | #[trigger]
        expr2.eval() == expr.eval() && some_spec(
            expr2,
            op_stack@.add(operator@.subrange(0, operator.len() as int)),
            num_stack@.add(operand@.subrange(0, operand.len() as int)),
        )) by {
        let expr2 = expr;
        assert(op_stack@.add(operator@.subrange(0, operator.len() as int)) == operator@);
        assert(num_stack@.add(operand@.subrange(0, operand.len() as int)) == operand@);
    }

    let mut i = 0;
    while i < operator.len()
        invariant
            0 <= i <= operator.len(),
            operator.len() == operand.len() - 1,
            num_stack.len() == op_stack.len(),
            i == operator.len() ==> num_stack.len() == 1 && op_stack.len() == 1 && op_stack@[0]
                == Operator::Add,
            stack_condition(op_stack@),
            operator[operator.len() - 1] == Operator::Add,
            operand[operand.len() - 1] == 0,
            forall|expr: AddSubExpr| #[trigger]
                some_spec(expr, operator@, operand@) ==> (exists|expr2: AddSubExpr| #[trigger]
                    expr2.eval() == expr.eval() && some_spec(
                        expr2,
                        op_stack@.add(operator@.subrange(i as int, operator.len() as int)),
                        num_stack@.add(operand@.subrange(i as int, operand.len() as int)),
                    )),
        decreases operator.len() - i,
    {
        let op = operator[i].clone();
        let ghost old_num_stack = num_stack@;
        num_stack.push(operand[i]);

        assert forall|expr: AddSubExpr| #[trigger] some_spec(expr, operator@, operand@) implies (
        exists|expr2: AddSubExpr|
            expr2.eval() == expr.eval() && #[trigger] some_spec(
                expr2,
                op_stack@.add(operator@.subrange(i as int, operator.len() as int)),
                num_stack@.add(operand@.subrange(i + 1, operand.len() as int)),
            )) by {
            let expr2 = choose|expr2: AddSubExpr|
                expr2.eval() == expr.eval() && #[trigger] some_spec(
                    expr2,
                    op_stack@.add(operator@.subrange(i as int, operator.len() as int)),
                    old_num_stack.add(operand@.subrange(i as int, operand.len() as int)),
                );
            assert(num_stack@.add(operand@.subrange(i + 1, operand.len() as int))
                == old_num_stack.add(operand@.subrange(i as int, operand.len() as int)));
        }

        while !op_stack.is_empty() && need_pop(op_stack.last().unwrap(), &op)
            invariant
                i < operator.len(),
                op == operator[i as int],
                num_stack.len() == op_stack.len() + 1,
                stack_condition(op_stack@),
                forall|expr: AddSubExpr| #[trigger]
                    some_spec(expr, operator@, operand@) ==> (exists|expr2: AddSubExpr|
                        expr2.eval() == expr.eval() && #[trigger] some_spec(
                            expr2,
                            op_stack@.add(operator@.subrange(i as int, operator.len() as int)),
                            num_stack@.add(operand@.subrange(i + 1, operand.len() as int)),
                        )),
            decreases op_stack.len(),
        {
            let ghost old_num_stack = num_stack@;
            let ghost old_op_stack = op_stack@;
            let right = num_stack.pop().unwrap();
            let left = num_stack.pop().unwrap();
            let op_in_stack = op_stack.pop().unwrap();
            let res = apply_op(left, right, op_in_stack);
            if res.is_none() {
                assert forall|expr: AddSubExpr| #[trigger]
                    some_spec(expr, operator@, operand@) implies None::<i128> == expr.eval() by {
                    let expr2 = choose|expr2: AddSubExpr|
                        expr2.eval() == expr.eval() && #[trigger] some_spec(
                            expr2,
                            old_op_stack.add(operator@.subrange(i as int, operator.len() as int)),
                            old_num_stack.add(operand@.subrange(i + 1, operand.len() as int)),
                        );
                    lemma_reduce_err(
                        expr2,
                        old_num_stack,
                        old_op_stack,
                        operator@.subrange(i as int, operator.len() as int),
                        operand@.subrange(i + 1, operand.len() as int),
                    );
                    expr2.lemma_eval_once();
                }
                return None;
            }
            num_stack.push(res.unwrap());
            assert forall|expr: AddSubExpr| #[trigger]
                some_spec(expr, operator@, operand@) implies (exists|expr2: AddSubExpr| #[trigger]
                expr2.eval() == expr.eval() && some_spec(
                    expr2,
                    op_stack@.add(operator@.subrange(i as int, operator.len() as int)),
                    num_stack@.add(operand@.subrange(i + 1, operand.len() as int)),
                )) by {
                let expr2 = choose|expr2: AddSubExpr|
                    expr2.eval() == expr.eval() && #[trigger] some_spec(
                        expr2,
                        old_op_stack.add(operator@.subrange(i as int, operator.len() as int)),
                        old_num_stack.add(operand@.subrange(i + 1, operand.len() as int)),
                    );
                lemma_reduce_ok(
                    expr2,
                    old_num_stack,
                    old_op_stack,
                    operator@.subrange(i as int, operator.len() as int),
                    operand@.subrange(i + 1, operand.len() as int),
                    res.unwrap(),
                );
                match expr2.eval_once() {
                    Ok(expr3) => {
                        expr2.lemma_eval_once();
                        assert(num_stack@.add(operand@.subrange(i + 1, operand.len() as int))
                            == old_num_stack.subrange(0, old_num_stack.len() - 2).add(
                            seq![res.unwrap()],
                        ).add(operand@.subrange(i + 1, operand.len() as int)));
                    },
                    Err(_) => {},
                }
            }
        }
        let ghost old_op_stack = op_stack@;
        op_stack.push(op);
        assert forall|expr: AddSubExpr| #[trigger] some_spec(expr, operator@, operand@) implies (
        exists|expr2: AddSubExpr|
            expr2.eval() == expr.eval() && #[trigger] some_spec(
                expr2,
                op_stack@.add(operator@.subrange(i + 1, operator.len() as int)),
                num_stack@.add(operand@.subrange(i + 1, operand.len() as int)),
            )) by {
            let expr2 = choose|expr2: AddSubExpr|
                expr2.eval() == expr.eval() && some_spec(
                    expr2,
                    old_op_stack.add(operator@.subrange(i as int, operator.len() as int)),
                    num_stack@.add(operand@.subrange(i + 1, operand.len() as int)),
                );
            assert(old_op_stack.add(operator@.subrange(i as int, operator.len() as int))
                == op_stack@.add(operator@.subrange(i + 1, operator.len() as int)));
        }
        i += 1;
    }
    assert forall|expr: AddSubExpr| #![auto] some_spec(expr, operator@, operand@) implies Some(
        num_stack@[0],
    ) == expr.eval() by {
        let expr2 = choose|expr2: AddSubExpr|
            expr2.eval() == expr.eval() && #[trigger] some_spec(
                expr2,
                op_stack@.add(operator@.subrange(i as int, operator.len() as int)),
                num_stack@.add(operand@.subrange(i as int, operand.len() as int)),
            );
        assert(op_stack@.add(operator@.subrange(i as int, operator.len() as int))
            == Seq::empty().push(Operator::Add));
        assert(num_stack@.add(operand@.subrange(i as int, operand.len() as int))
            == seq!(num_stack@[0], 0));
        lemma_simple_expr_reverse(expr2, num_stack@[0]);
    }
    num_stack.pop()
}

// This is the main execution function. It changes general case into special case proved above.
exec fn eval_by_stack(operator: Vec<Operator>, operand: Vec<i128>) -> (res: Option<i128>)
    requires
        operator.len() == operand.len() - 1,
    ensures
        forall|expr: AddSubExpr| #[trigger]
            some_spec(expr, operator@, operand@) ==> res == expr.eval(),
{
    let mut operator_a = operator;
    operator_a.push(Operator::Add);
    let mut operand_a = operand;
    operand_a.push(0);
    let zero = MulDivExpr::Factor(PowExpr::Base(0));
    assert forall|expr: AddSubExpr|
        #![auto]
        some_spec(expr, operator@, operand@) implies AddSubExpr::Add(
        Box::new(expr),
        Box::new(zero),
    ).eval() == expr.eval() && some_spec(
        AddSubExpr::Add(Box::new(expr), Box::new(zero)),
        operator_a@,
        operand_a@,
    ) by {
        assert(AddSubExpr::Add(Box::new(expr), Box::new(zero)).operator() == operator_a@);
        assert(AddSubExpr::Add(Box::new(expr), Box::new(zero)).operand() == operand_a@);
    }
    eval_by_stack_a(operator_a, operand_a)
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
        Operator list has at least one operator, and operand list has at least two ops.

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
