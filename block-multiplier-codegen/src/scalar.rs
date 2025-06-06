use {
    crate::{constants::*, load_store::load_const},
    hla::*,
    std::{
        array,
        cmp::{max, min},
        mem,
        ops::{Index, IndexMut},
    },
};

// BUILDERS

/// Sets up the assembly generation context for a widening multiplication of two
/// u256 numbers.
///
/// Initializes the necessary registers and calls `widening_mul_u256`.
/// Returns the input and output variables for the generated assembly function.
pub fn setup_widening_mul_u256(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
) -> (Vec<FreshVariable>, FreshVariable) {
    let a = alloc.fresh_array();
    let b = alloc.fresh_array();

    let s = widening_mul_u256(alloc, asm, &a, &b);

    (
        vec![FreshVariable::new("a", &a), FreshVariable::new("b", &b)],
        FreshVariable::new("out", &s),
    )
}

/// Sets up the assembly generation context for Montgomery multiplication of two
/// u256 numbers.
pub fn setup_single_step(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
) -> (Vec<FreshVariable>, FreshVariable) {
    let a = alloc.fresh_array();
    let b = alloc.fresh_array();

    let s = single_step(alloc, asm, &a, &b);
    (
        vec![FreshVariable::new("a", &a), FreshVariable::new("b", &b)],
        FreshVariable::new("out", &s),
    )
}

/// Sets up the assembly generation context for bn254 u256 Montgomery squaring.
pub fn setup_square_single_step(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
) -> (Vec<FreshVariable>, FreshVariable) {
    let a = alloc.fresh_array();

    let s = square_single_step(alloc, asm, &a);
    (
        vec![FreshVariable::new("a", &a)],
        FreshVariable::new("out", &s),
    )
}

/// Sets up the assembly generation context for Montgomery log jump
/// multiplication.
pub fn setup_log_jump(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
) -> (Vec<FreshVariable>, FreshVariable) {
    let a = alloc.fresh_array();
    let b = alloc.fresh_array();

    let s = log_jump(alloc, asm, &a, &b);
    (
        vec![FreshVariable::new("a", &a), FreshVariable::new("b", &b)],
        FreshVariable::new("out", &s),
    )
}

/// Sets up the assembly generation context for bn254 u256 Montgomery squaring
/// using Domb's log jump.
pub fn setup_square_log_jump(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
) -> (Vec<FreshVariable>, FreshVariable) {
    let a = alloc.fresh_array();

    let s = square_log_jump(alloc, asm, &a);
    (
        vec![FreshVariable::new("a", &a)],
        FreshVariable::new("out", &s),
    )
}
/// Sets up the assembly generation context for a u256 multiply-add-limb
/// operation (`r = r + a * b`).
///
/// Initializes the necessary registers and calls `madd_u256_limb`.
/// Returns the input and output variables for the generated assembly function.
pub fn setup_madd_u256_limb(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
) -> (Vec<FreshVariable>, FreshVariable) {
    let add = alloc.fresh_array();
    let var_add = FreshVariable::new("r#add", &add);
    let a = alloc.fresh_array();
    let b = alloc.fresh();

    let s = madd_u256_limb(alloc, asm, add, &a, &b);

    (
        vec![
            var_add,
            FreshVariable::new("a", &a),
            FreshVariable::new("b", &[b]),
        ],
        FreshVariable::new("out", &s),
    )
}

// GENERATORS

/// Performs `ret = s + [0, add]` with carry propagation.
///
/// Takes a 2-limb value `s` and a single limb `add`.
/// Returns the 2-limb result. Uses `adds` and `cinc` instructions.
pub fn carry_add(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
    s: &[Reg<u64>; 2],
    add: &Reg<u64>,
) -> [Reg<u64>; 2] {
    let ret = array::from_fn(|_| alloc.fresh());
    asm.append_instruction(vec![
        adds_inst(&ret[0], &s[0], add),
        cinc_inst(&ret[1], &s[1], "hs".to_string()),
    ]);
    ret
}

/// Performs a compare-negative (`cmn s[0], add`) and propagates the carry to
/// `s[1]`.
///
/// Returns the updated high limb `s[1]`.
pub fn carry_cmn(asm: &mut Assembler, s: [Reg<u64>; 2], add: &Reg<u64>) -> Reg<u64> {
    asm.append_instruction(vec![
        cmn_inst(&s[0], add),
        cinc_inst(&s[1], &s[1], "hs".to_string()),
    ]);
    let [_, out] = s;
    out
}

/// Computes `t += a * b` where `t` is 5 limbs, `a` is 4 limbs, and `b` is 1
/// limb.
pub fn madd_u256_limb(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
    mut t: [Reg<u64>; 5],
    a: &[Reg<u64>; 4],
    b: &Reg<u64>,
) -> [Reg<u64>; 5] {
    let mut carry;
    // First multiplication is outside of the loop as it doesn't have the second
    // carry add to add the carry of a previous multiplication
    let tmp = widening_mul(alloc, asm, &a[0], b);
    [t[0], carry] = carry_add(alloc, asm, &tmp, &t[0]);

    for i in 1..a.len() {
        let tmp = widening_mul(alloc, asm, &a[i], b);
        let tmp = carry_add(alloc, asm, &tmp, &carry);
        [t[i], carry] = carry_add(alloc, asm, &tmp, &t[i]);
    }
    t[a.len()] = add(alloc, asm, &t[a.len()], &carry);

    t
}

/// Computes `t += a * b` where `t` is 6 limbs, `a` is 4 limbs, and `b` is 1
/// limb.
///
/// A variation of [`madd_u256_limb`] where t is one limb larger to deal with
/// the potential carry of the lower 5 limbs + a*b
pub fn maddc_u256_limb(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
    mut t: [Reg<u64>; 6],
    a: &[Reg<u64>; 4],
    b: &Reg<u64>,
) -> [Reg<u64>; 6] {
    let mut carry;
    // First multiplication is outside of the loop as it doesn't have the second
    // carry add to add the carry of a previous multiplication
    let tmp = widening_mul(alloc, asm, &a[0], b);
    [t[0], carry] = carry_add(alloc, asm, &tmp, &t[0]);

    for i in 1..a.len() {
        let tmp = widening_mul(alloc, asm, &a[i], b);
        let tmp = carry_add(alloc, asm, &tmp, &carry);
        [t[i], carry] = carry_add(alloc, asm, &tmp, &t[i]);
    }
    let ta = mem::replace(&mut t[a.len()], alloc.fresh());
    let ta1 = mem::replace(&mut t[a.len() + 1], alloc.fresh());
    [t[a.len()], t[a.len() + 1]] = carry_add(alloc, asm, &[ta, ta1], &carry);

    t
}

/// Computes `t += a * b` where `t` is 5 limbs, `a` is 4 limbs, and `b` is 1
/// limb, truncating the result to the upper 4 limbs.
///
/// Similar to `madd_u256_limb` but uses `carry_cmn` for the first step and
/// returns only the upper 4 limbs of the result.
///
/// A variation of madd_u256_limb that truncates the results. This is required
/// because the assembler checks whether all registers are used. The HLA
/// performs no optimizations.
pub fn madd_u256_limb_truncate(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
    mut t: [Reg<u64>; 5],
    a: &[Reg<u64>; 4],
    b: &Reg<u64>,
) -> [Reg<u64>; 4] {
    let tmp = widening_mul(alloc, asm, &a[0], b);
    let mut carry = carry_cmn(asm, tmp, &t[0]);
    for i in 1..a.len() {
        let tmp = widening_mul(alloc, asm, &a[i], b);
        let tmp = carry_add(alloc, asm, &tmp, &carry);
        [t[i], carry] = carry_add(alloc, asm, &tmp, &t[i]);
    }
    t[a.len()] = add(alloc, asm, &t[a.len()], &carry);

    let [_, out @ ..] = t;
    out
}

/// Computes `a - b` for two 4-limb (256-bit) numbers with borrow propagation.
///
/// Uses `subs` and `sbcs` instructions.
pub fn sub_u256(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
    a: &[Reg<u64>; 4],
    b: &[Reg<u64>; 4],
) -> [Reg<u64>; 4] {
    let out = array::from_fn(|_| alloc.fresh());
    // Due to carry chain this needs to be an atomic block.
    asm.append_instruction(vec![
        subs_inst(&out[0], &a[0], &b[0]),
        sbcs_inst(&out[1], &a[1], &b[1]),
        sbcs_inst(&out[2], &a[2], &b[2]),
        sbcs_inst(&out[3], &a[3], &b[3]),
    ]);
    out
}

/// Computes the Montgomery multiplication of two 4-limb (256-bit) numbers `a`
/// and `b`.
///
/// Implements the Domb's single step Montgomery multiplication algorithm.
/// The result is less than `4P`.
pub fn single_step(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
    a: &[Reg<u64>; 4],
    b: &[Reg<u64>; 4],
) -> [Reg<u64>; 4] {
    let t = widening_mul_u256(alloc, asm, a, b);
    single_step_reduction(alloc, asm, t)
}

fn single_step_reduction(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
    t: [Reg<u64>; 8],
) -> [Reg<u64>; 4] {
    let [t0, t1, t2, s @ ..] = t;

    let i3 = U64_I3.map(|val| load_const(alloc, asm, val));
    let r1 = madd_u256_limb(alloc, asm, s, &i3, &t0);

    let i2 = U64_I2.map(|val| load_const(alloc, asm, val));
    let r2 = madd_u256_limb(alloc, asm, r1, &i2, &t1);

    let i1 = U64_I1.map(|val| load_const(alloc, asm, val));
    let r3 = madd_u256_limb(alloc, asm, r2, &i1, &t2);

    let mu0 = load_const(alloc, asm, U64_MU0);
    let m = mul(alloc, asm, &mu0, &r3[0]);

    let p = U64_P.map(|val| load_const(alloc, asm, val));
    madd_u256_limb_truncate(alloc, asm, r3, &p, &m)
}

/// Computes the Montgomery multiplication of two 4-limb (256-bit) numbers `a`
/// and `b`.
///
/// Implements the Domb's log jump Montgomery multiplication algorithm.
/// The result is less than `3P`.
pub fn log_jump(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
    a: &[Reg<u64>; 4],
    b: &[Reg<u64>; 4],
) -> [Reg<u64>; 4] {
    let t = widening_mul_u256(alloc, asm, a, b);
    log_jump_reduction(alloc, asm, t)
}

/// Computes the Montgomery multiplication of two 4-limb (256-bit) numbers `a`
/// and `b`.
///
/// Implements the Domb's log jump Montgomery squaring algorithm.
/// The result is less than `3P`.
pub fn square_log_jump(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
    a: &[Reg<u64>; 4],
) -> [Reg<u64>; 4] {
    let t = square_u256(alloc, asm, a);
    log_jump_reduction(alloc, asm, t)
}

fn log_jump_reduction(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
    t: [Reg<u64>; 8],
) -> [Reg<u64>; 4] {
    let [t0, t1, s @ ..] = t;

    let i2 = U64_I2.map(|val| load_const(alloc, asm, val));
    // This combines t0' and t2 which get reduced later by i1
    let [t02, r0 @ ..] = maddc_u256_limb(alloc, asm, s, &i2, &t0);

    let r2 = madd_u256_limb(alloc, asm, r0, &i2, &t1);

    let i1 = U64_I1.map(|val| load_const(alloc, asm, val));
    let r3 = madd_u256_limb(alloc, asm, r2, &i1, &t02);

    let mu0 = load_const(alloc, asm, U64_MU0);
    let m = mul(alloc, asm, &mu0, &r3[0]);

    let p = U64_P.map(|val| load_const(alloc, asm, val));
    madd_u256_limb_truncate(alloc, asm, r3, &p, &m)
}

/// Computes the 128-bit widening multiplication of two 64-bit registers `a` and
/// `b`.
///
/// Returns the low 64 bits (`mul a, b`) and high 64 bits (`umulh a, b`).
pub fn widening_mul(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
    a: &Reg<u64>,
    b: &Reg<u64>,
) -> [Reg<u64>; 2] {
    [mul(alloc, asm, a, b), umulh(alloc, asm, a, b)]
}

/// Computes the Montgomery square of a 4-limb (256-bit) number `a`
///
/// Implements the Domb's single step Montgomery multiplication algorithm.
/// The result is less than `4P`.
pub fn square_single_step(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
    a: &[Reg<u64>; 4],
) -> [Reg<u64>; 4] {
    let t = square_u256(alloc, asm, a);
    single_step_reduction(alloc, asm, t)
}

fn square_u256(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
    a: &[Reg<u64>; 4],
) -> [Reg<u64>; 8] {
    let mult = LazySymmetricMatrix(lazy_outer_product(a, a));
    accumulate(alloc, asm, mult)
}

/// Widening multiplication u256 x u256 -> u512
pub fn widening_mul_u256(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
    a: &[Reg<u64>; 4],
    b: &[Reg<u64>; 4],
) -> [Reg<u64>; 8] {
    let outer_product = lazy_outer_product(a, b);
    accumulate(alloc, asm, outer_product)
}

fn lazy_widening_mul<'a>(a: &'a Reg<u64>, b: &'a Reg<u64>) -> Lazy<'a, [Reg<u64>; 2]> {
    Lazy::thunk(Box::new(|alloc, asm| widening_mul(alloc, asm, a, b)))
}

/// Compute the outer product of two vectors
fn lazy_outer_product<'a>(
    a: &'a [Reg<u64>; 4],
    b: &'a [Reg<u64>; 4],
) -> SquareMatrix<Lazy<'a, [Reg<u64>; 2]>, 4> {
    let mult = array::from_fn(|i| array::from_fn(|j| lazy_widening_mul(&a[i], &b[j])));
    SquareMatrix(mult)
}

fn accumulate<'a, T>(
    alloc: &mut FreshAllocator,
    asm: &mut Assembler,
    mut outer_product: T,
) -> [Reg<u64>; 8]
where
    T: LazyMatrix<'a, [Reg<u64>; 2]>,
{
    let rows = 4;
    let columns = 4;

    let mut t: [Reg<u64>; 8] = array::from_fn(|_| alloc.fresh());
    // The all multiplication of a with the lowest limb of b do not have a previous
    // round to add to. That's why this loop is separated.
    let mut carry;

    // replace such that we can use the registers of mult[0][0] in the output.
    let tmp = mem::replace(
        &mut outer_product[(0, 0)],
        Lazy::forced([alloc.fresh(), alloc.fresh()]),
    );

    [t[0], carry] = tmp.into_(alloc, asm);
    for i in 1..rows {
        let tmp = &mut outer_product[(i, 0)];
        let tmp = tmp.as_(alloc, asm);
        [t[i], carry] = carry_add(alloc, asm, tmp, &carry);
    }
    t[rows] = carry;

    // 2nd and later carry chain
    for j in 1..columns {
        let mut carry;
        let tmp = &mut outer_product[(0, j)];
        let tmp = tmp.as_(alloc, asm);
        [t[j], carry] = carry_add(alloc, asm, tmp, &t[j]);
        for i in 1..rows {
            let tmp = &mut outer_product[(i, j)];
            let tmp = tmp.as_(alloc, asm);
            let tmp = carry_add(alloc, asm, tmp, &carry);
            [t[i + j], carry] = carry_add(alloc, asm, &tmp, &t[i + j]);
        }
        t[j + rows] = carry;
    }

    t
}

struct SquareMatrix<T, const N: usize>([[T; N]; N]);

impl<const N: usize, T> Index<(usize, usize)> for SquareMatrix<T, N> {
    type Output = T;

    fn index(&self, index: (usize, usize)) -> &T {
        &self.0[index.0][index.1]
    }
}

impl<T, const N: usize> IndexMut<(usize, usize)> for SquareMatrix<T, N> {
    fn index_mut(&mut self, index: (usize, usize)) -> &mut T {
        &mut self.0[index.0][index.1]
    }
}

// For simplicity the backing store is a lazy square matrix where we only
// evaluate the upper triangle
struct LazySymmetricMatrix<'a, T, const N: usize>(SquareMatrix<Lazy<'a, T>, N>);

impl<'a, const N: usize, T> Index<(usize, usize)> for LazySymmetricMatrix<'a, T, N> {
    type Output = Lazy<'a, T>;

    fn index(&self, index: (usize, usize)) -> &Self::Output {
        let (i, j) = index;
        let x = min(i, j);
        let y = max(i, j);
        &self.0[(x, y)]
    }
}

impl<'a, T, const N: usize> IndexMut<(usize, usize)> for LazySymmetricMatrix<'a, T, N> {
    fn index_mut(&mut self, index: (usize, usize)) -> &mut Lazy<'a, T> {
        let (i, j) = index;
        let x = min(i, j);
        let y = max(i, j);
        &mut self.0[(x, y)]
    }
}

trait LazyMatrix<'a, T>:
    Index<(usize, usize), Output = Lazy<'a, T>> + IndexMut<(usize, usize)>
{
}

impl<'a, T, const N: usize> LazyMatrix<'a, T> for SquareMatrix<Lazy<'a, T>, N> {}
impl<'a, T, const N: usize> LazyMatrix<'a, T> for LazySymmetricMatrix<'a, T, N> {}
