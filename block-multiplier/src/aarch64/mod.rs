//! The domain and range of Montgomery multiplication vary based on the
//! algorithm used. This table shows the output range (in multiples of bn254
//! prime) for different input sizes. The bracketed numbers indicate the maximum
//! number of prime multiples that can be added before a U256 overflow occurs.
//!
//! Input Size | single_step | single_step_simd | log_jump
//! -----------|-------------|------------------|---------
//! p          | 3.24 [2.05] |    2.43 [2.8639] | 2.35 [2.94]
//! 2p         | 3.80 [1.49] |    2.99 [2.2968] | 2.91 [2.38]
//! 3p         | 4.75 [0.54] |    3.94 [1.3517] | 3.86 [1.43]
//! 2ˆ256-2p   | 5.09 [0.20] |    4.28 [1.0067] | 4.20 [1.09]
use {
    core::{arch::asm, simd::Simd},
    fp_rounding::{RoundingGuard, Zero},
};

/// A block multiplier with 3 concurrent multiplications.
#[inline]
pub fn montgomery_interleaved_3(
    _rtz: &RoundingGuard<Zero>,
    a: [u64; 4],
    b: [u64; 4],
    av: [Simd<u64, 2>; 4],
    bv: [Simd<u64, 2>; 4],
) -> ([u64; 4], [Simd<u64, 2>; 4]) {
    let mut out = [0; 4];
    let mut outv = [Simd::splat(0); 4];
    unsafe {
        asm!(include_str!("montgomery_interleaved_3.s"),
        in("x0") a[0], in("x1") a[1], in("x2") a[2], in("x3") a[3],
        in("x4") b[0], in("x5") b[1], in("x6") b[2], in("x7") b[3],
        in("v0") av[0], in("v1") av[1], in("v2") av[2], in("v3") av[3],
        in("v4") bv[0], in("v5") bv[1], in("v6") bv[2], in("v7") bv[3],
        lateout("x0") out[0], lateout("x1") out[1], lateout("x2") out[2], lateout("x3") out[3],
        lateout("v0") outv[0], lateout("v1") outv[1], lateout("v2") outv[2], lateout("v3") outv[3],
        lateout("x4") _, lateout("x5") _, lateout("x6") _, lateout("x7") _, lateout("x8") _, lateout("x9") _, lateout("x10") _, lateout("x11") _, lateout("x12") _, lateout("x13") _, lateout("x14") _, lateout("x15") _, lateout("x16") _, lateout("v4") _, lateout("v5") _, lateout("v6") _, lateout("v7") _, lateout("v8") _, lateout("v9") _, lateout("v10") _, lateout("v11") _, lateout("v12") _, lateout("v13") _, lateout("v14") _, lateout("v15") _, lateout("v16") _, lateout("v17") _, lateout("v18") _, lateout("v19") _, lateout("v20") _, lateout("v21") _, lateout("v22") _, lateout("v23") _, lateout("v24") _,
        lateout("lr") _,
        options(nomem, nostack)
        )
    };
    (out, outv)
}

#[inline]
/// A block squarer with 3 concurrent multiplications
///
/// The scalar input uses `single_step` and the SIMD input uses
/// `single_step_simd`. See the module documentation for the implications of
/// this.
pub fn montgomery_square_interleaved_3(
    _rtz: &RoundingGuard<Zero>,
    a: [u64; 4],
    av: [Simd<u64, 2>; 4],
) -> ([u64; 4], [Simd<u64, 2>; 4]) {
    let mut out = [0; 4];
    let mut outv = [Simd::splat(0); 4];
    unsafe {
        asm!(include_str!("montgomery_square_interleaved_3.s"),
        in("x0") a[0], in("x1") a[1], in("x2") a[2], in("x3") a[3],
        in("v0") av[0], in("v1") av[1], in("v2") av[2], in("v3") av[3],
        lateout("x0") out[0], lateout("x1") out[1], lateout("x2") out[2], lateout("x3") out[3],
        lateout("v0") outv[0], lateout("v1") outv[1], lateout("v2") outv[2], lateout("v3") outv[3],
        lateout("x4") _, lateout("x5") _, lateout("x6") _, lateout("x7") _, lateout("x8") _, lateout("x9") _, lateout("x10") _, lateout("x11") _, lateout("x12") _, lateout("x13") _, lateout("x14") _, lateout("x15") _, lateout("x16") _, lateout("x17") _, lateout("v4") _, lateout("v5") _, lateout("v6") _, lateout("v7") _, lateout("v8") _, lateout("v9") _, lateout("v10") _, lateout("v11") _, lateout("v12") _, lateout("v13") _, lateout("v14") _, lateout("v15") _, lateout("v16") _, lateout("v17") _, lateout("v18") _, lateout("v19") _,
        lateout("lr") _,
        options(nomem, nostack)
        )
    };
    (out, outv)
}

#[inline]
/// A block squarer with 3 concurrent multiplications
///
/// The scalar input uses `log_jump` and the SIMD input uses
/// `single_step_simd`. See the module documentation for the implications of
/// this.
pub fn montgomery_square_log_interleaved_3(
    _rtz: &RoundingGuard<Zero>,
    a: [u64; 4],
    av: [Simd<u64, 2>; 4],
) -> ([u64; 4], [Simd<u64, 2>; 4]) {
    let mut out = [0; 4];
    let mut outv = [Simd::splat(0); 4];
    unsafe {
        asm!(
            include_str!("montgomery_square_log_interleaved_3.s"),
            in("x0") a[0], in("x1") a[1], in("x2") a[2], in("x3") a[3],
            in("v0") av[0], in("v1") av[1], in("v2") av[2], in("v3") av[3],
            lateout("x0") out[0], lateout("x1") out[1], lateout("x2") out[2], lateout("x3")
            out[3], lateout("v0") outv[0], lateout("v1") outv[1], lateout("v2")
            outv[2], lateout("v3") outv[3], lateout("x4") _, lateout("x5") _,
            lateout("x6") _, lateout("x7") _, lateout("x8") _, lateout("x9") _, lateout("x10") _,
            lateout("x11") _, lateout("x12") _, lateout("x13") _, lateout("x14") _,
            lateout("x15") _, lateout("x16") _, lateout("x17") _, lateout("v4") _, lateout("v5") _,
            lateout("v6") _, lateout("v7") _, lateout("v8") _, lateout("v9") _,
            lateout("v10") _, lateout("v11") _, lateout("v12") _, lateout("v13") _,
            lateout("v14") _, lateout("v15") _, lateout("v16") _, lateout("v17") _,
            lateout("v18") _, lateout("v19") _, lateout("lr") _,
            options(nomem, nostack)
        )
    };
    (out, outv)
}

/// A block multiplier with 4 concurrent multiplications.
///
/// The scalar inputs uses `single_step` and the SIMD input uses
/// `single_step_simd`. See the module documentation for the implications of
/// this.
#[inline]
pub fn montgomery_interleaved_4(
    _rtz: &RoundingGuard<Zero>,
    a: [u64; 4],
    b: [u64; 4],
    a1: [u64; 4],
    b1: [u64; 4],
    av: [Simd<u64, 2>; 4],
    bv: [Simd<u64, 2>; 4],
) -> ([u64; 4], [u64; 4], [Simd<u64, 2>; 4]) {
    let mut out = [0; 4];
    let mut out1 = [0; 4];
    let mut outv = [Simd::splat(0); 4];
    unsafe {
        asm!(include_str!("montgomery_interleaved_4.s"),
            in("x0") a[0], in("x1") a[1], in("x2") a[2], in("x3") a[3],
            in("x4") b[0], in("x5") b[1], in("x6") b[2], in("x7") b[3],
            in("x8") a1[0], in("x9") a1[1], in("x10") a1[2], in("x11") a1[3],
            in("x12") b1[0], in("x13") b1[1], in("x14") b1[2], in("x15") b1[3],
            in("v0") av[0], in("v1") av[1], in("v2") av[2], in("v3") av[3],
            in("v4") bv[0], in("v5") bv[1], in("v6") bv[2], in("v7") bv[3],
            lateout("x0") out[0], lateout("x1") out[1], lateout("x2") out[2], lateout("x3") out[3],
            lateout("x4") out1[0], lateout("x5") out1[1], lateout("x6") out1[2], lateout("x7") out1[3],
            lateout("v0") outv[0], lateout("v1") outv[1], lateout("v2") outv[2], lateout("v3") outv[3],
            lateout("x8") _, lateout("x9") _, lateout("x10") _, lateout("x11") _, lateout("x12") _, lateout("x13") _, lateout("x14") _, lateout("x15") _, lateout("x16") _, lateout("x17") _, lateout("x20") _, lateout("x21") _, lateout("x22") _, lateout("x23") _, lateout("x24") _, lateout("x25") _, lateout("x26") _, lateout("v4") _, lateout("v5") _, lateout("v6") _, lateout("v7") _, lateout("v8") _, lateout("v9") _, lateout("v10") _, lateout("v11") _, lateout("v12") _, lateout("v13") _, lateout("v14") _, lateout("v15") _, lateout("v16") _, lateout("v17") _, lateout("v18") _, lateout("v19") _, lateout("v20") _, lateout("v21") _, lateout("v22") _, lateout("v23") _, lateout("v24") _,
            lateout("lr") _,
            options(nomem, nostack)
        )
    };
    (out, out1, outv)
}

#[inline]
/// A block multiplier with 4 concurrent multiplications.
///
/// The scalar inputs use `single_step` and the SIMD input uses
/// `single_step_simd`. See the module documentation for the implications of
/// this.
pub fn montgomery_square_interleaved_4(
    _rtz: &RoundingGuard<Zero>,
    a: [u64; 4],
    a1: [u64; 4],
    av: [Simd<u64, 2>; 4],
) -> ([u64; 4], [u64; 4], [Simd<u64, 2>; 4]) {
    let mut out = [0; 4];
    let mut out1 = [0; 4];
    let mut outv = [Simd::splat(0); 4];
    unsafe {
        asm!(
            include_str!("montgomery_square_interleaved_4.s"),
            in("x0") a[0], in("x1") a[1], in("x2") a[2], in("x3") a[3],
            in("x4") a1[0], in("x5") a1[1], in("x6") a1[2], in("x7") a1[3],
            in("v0") av[0], in("v1") av[1], in("v2") av[2], in("v3") av[3],
            lateout("x0") out[0], lateout("x1") out[1], lateout("x2") out[2], lateout("x3")
            out[3], lateout("x4") out1[0], lateout("x5") out1[1], lateout("x6")
            out1[2], lateout("x7") out1[3], lateout("v0") outv[0], lateout("v1")
            outv[1], lateout("v2") outv[2], lateout("v3") outv[3], lateout("x8") _,
            lateout("x9") _, lateout("x10") _, lateout("x11") _, lateout("x12") _,
            lateout("x13") _, lateout("x14") _, lateout("x15") _, lateout("x16") _,
            lateout("x17") _, lateout("x20") _, lateout("x21") _, lateout("x22") _,
            lateout("x23") _, lateout("x24") _, lateout("v4") _, lateout("v5") _, lateout("v6") _,
            lateout("v7") _, lateout("v8") _, lateout("v9") _, lateout("v10") _,
            lateout("v11") _, lateout("v12") _, lateout("v13") _, lateout("v14") _,
            lateout("v15") _, lateout("v16") _, lateout("v17") _, lateout("v18") _,
            lateout("v19") _, lateout("lr") _,
            options(nomem, nostack)
        )
    };
    (out, out1, outv)
}

#[inline]
/// A block multiplier with 4 concurrent multiplications.
///
/// The scalar inputs use `log_jump` and the SIMD input uses
/// `single_step_simd`. See the module documentation for the implications of
/// this.
pub fn montgomery_square_log_interleaved_4(
    _rtz: &RoundingGuard<Zero>,
    a: [u64; 4],
    a1: [u64; 4],
    av: [Simd<u64, 2>; 4],
) -> ([u64; 4], [u64; 4], [Simd<u64, 2>; 4]) {
    let mut out = [0; 4];
    let mut out1 = [0; 4];
    let mut outv = [Simd::splat(0); 4];
    unsafe {
        asm!(
            include_str!("montgomery_square_log_interleaved_4.s"),
            in("x0") a[0], in("x1") a[1], in("x2") a[2], in("x3") a[3],
            in("x4") a1[0], in("x5") a1[1], in("x6") a1[2], in("x7") a1[3],
            in("v0") av[0], in("v1") av[1], in("v2") av[2], in("v3") av[3],
            lateout("x0") out[0], lateout("x1") out[1], lateout("x2") out[2], lateout("x3")
            out[3], lateout("x4") out1[0], lateout("x5") out1[1], lateout("x6")
            out1[2], lateout("x7") out1[3], lateout("v0") outv[0], lateout("v1")
            outv[1], lateout("v2") outv[2], lateout("v3") outv[3], lateout("x8") _,
            lateout("x9") _, lateout("x10") _, lateout("x11") _, lateout("x12") _,
            lateout("x13") _, lateout("x14") _, lateout("x15") _, lateout("x16") _,
            lateout("x17") _, lateout("x20") _, lateout("x21") _, lateout("x22") _,
            lateout("x23") _, lateout("x24") _, lateout("v4") _, lateout("v5") _, lateout("v6") _,
            lateout("v7") _, lateout("v8") _, lateout("v9") _, lateout("v10") _,
            lateout("v11") _, lateout("v12") _, lateout("v13") _, lateout("v14") _,
            lateout("v15") _, lateout("v16") _, lateout("v17") _, lateout("v18") _,
            lateout("v19") _, lateout("lr") _,
            options(nomem, nostack)
        )
    };
    (out, out1, outv)
}

#[cfg(test)]
mod tests {
    use {
        super::*,
        crate::test_utils::{ark_ff_reference, safe_bn254_montgomery_input},
        ark_bn254::Fr,
        ark_ff::BigInt,
        fp_rounding::with_rounding_mode,
        proptest::proptest,
        std::array,
    };

    /// test that compares square interleaved with ark_ff
    #[test]
    fn test_montgomery_square() {
        proptest!(|(
            a in safe_bn254_montgomery_input(),
            b in safe_bn254_montgomery_input(),
            c in safe_bn254_montgomery_input(),
        )| {
            let av = array::from_fn(|i| Simd::from_array([b[i],c[i]]));
            unsafe {
                with_rounding_mode((), |rtz, _| {
                    let (result_sqr, result_sqr_v) = montgomery_square_interleaved_3(rtz, a, av);
                    let a_squared = ark_ff_reference(a, a);
                    let b_squared = ark_ff_reference(b, b);
                    let c_squared = ark_ff_reference(c, c);
                    let a_squared_interleaved = Fr::new(BigInt(result_sqr));
                    let b_squared_interleaved = Fr::new(BigInt(result_sqr_v.map(|e| e[0])));
                    let c_squared_interleaved = Fr::new(BigInt(result_sqr_v.map(|e| e[1])));
                    assert_eq!(a_squared, a_squared_interleaved);
                    assert_eq!(b_squared, b_squared_interleaved);
                    assert_eq!(c_squared, c_squared_interleaved);
                });
            }
        });
    }

    /// test that compares square interleaved with ark_ff
    #[test]
    fn test_montgomery_square_log() {
        proptest!(|(
            a in safe_bn254_montgomery_input(),
            b in safe_bn254_montgomery_input(),
            c in safe_bn254_montgomery_input(),
        )| {
            let av = array::from_fn(|i| Simd::from_array([b[i],c[i]]));
            unsafe {
                with_rounding_mode((), |rtz, _| {
                    let (result_sqr, result_sqr_v) = montgomery_square_log_interleaved_3(rtz, a, av);
                    let a_squared = ark_ff_reference(a, a);
                    let b_squared = ark_ff_reference(b, b);
                    let c_squared = ark_ff_reference(c, c);
                    let a_squared_interleaved = Fr::new(BigInt(result_sqr));
                    let b_squared_interleaved = Fr::new(BigInt(result_sqr_v.map(|e| e[0])));
                    let c_squared_interleaved = Fr::new(BigInt(result_sqr_v.map(|e| e[1])));
                    assert_eq!(a_squared, a_squared_interleaved);
                    assert_eq!(b_squared, b_squared_interleaved);
                    assert_eq!(c_squared, c_squared_interleaved);
                });
            }
        });
    }
}
