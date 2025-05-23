use {
    core::{arch::asm, simd::Simd},
    fp_rounding::{RoundingGuard, Zero},
};

/// A block multiplier with 3 concurrent multiplications.
///
/// Raspberry Pi 5:  2.2 times the throughput compared to a single multiplier.
/// Apple Silicon (M3): same throughput as a single multiplier
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

/// A block multiplier with 4 concurrent multiplications.
///
/// Raspberry Pi 5:  1.8 times the throughput compared to a single multiplier.
/// Apple Silicon (M3): ~1.06 times the throughput of a single multiplier
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
