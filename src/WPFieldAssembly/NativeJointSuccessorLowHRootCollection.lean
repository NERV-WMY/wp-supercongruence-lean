import WPFieldAssembly.NativeClosureLowHCollection
import WPFieldAssembly.NativeClosureLowHSource
import WPFieldAssembly.NativeClosureUniversalSource

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
open WPFieldAssembly.ActualBpairContraction WPFieldAssembly.GreenLaurentOperators
open WPFieldAssembly.ActualBpairLowHLocalPole
open WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.NativeClosureLowH

variable {K : Type*} [Field K]
set_option maxHeartbeats 2200000

/- STATEMENT_FIDELITY: This uses the original actualZ52 and the genuine
actualAK with its complete reciprocal. The H(V) multiplier is collected
through the actual product derivative, the proved positive native band and
the proved negative native half band. The Xi expression is exactly the one
inside nativeOriginalHSource. For p>=19, CMK is half the human C_M:
CMK*dS=C_M*d(S/2). The cleared coefficient 3/2 and the full 3h branch
therefore keep the human normalization; endpoint values are not substituted.
The period-row shift -10E(Q)/9 is not halved. Its remaining branch density is retained, so
this theorem alone does not identify the entire marked Euler source with
IR64d or evaluate the actual NC77 scalar. -/

/-- The actual Green13 source loses only its common nonzero zeta factor.
The complete H pullback and its constant correction remain in the source. -/
theorem native_actual_CB_H_cleared (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent *
        D (ActualGreenResidue.CMK (K := K) p).toLaurent =
      LaurentPolynomial.C (3 / 2 : K) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        ((ActualGreenResidue.HpullK (K := K) p).toLaurent +
          2 * LaurentPolynomial.C (ActualGreenResidue.hK (K := K) p)) -
      (ActualThreePhase.CBK (K := K) p).toLaurent * (33 - 12 * T 1) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have hc : (3 / 2 : K) * (1 / 3) = 1 / 2 := by
    field_simp [h2, h3]
  have hR := WPFiniteZSource.R_cleared (K := K) p hp
  have hRζ : (WPFiniteZSource.Abar : K[X]).toLaurent * WPFiniteZSource.R p =
      LaurentPolynomial.C (3 / 2 : K) * ActualChiEndpoints.zeta p *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) := by
    rw [native_zeta_phase p hp, ← mul_assoc, ← map_mul, hc]
    exact hR
  have ht : (T (-(p : ℤ)) : K[T;T⁻¹]) ≠ 0 := by
    intro hz
    have he : (T (-(p : ℤ)) * T (p : ℤ) : K[T;T⁻¹]) = 1 := by
      rw [← T_add, neg_add_cancel, T_zero]
    rw [hz, zero_mul] at he
    exact zero_ne_one he
  have hζ : ActualChiEndpoints.zeta (K := K) p ≠ 0 := by
    have hC3 : (LaurentPolynomial.C (1 / 3 : K) : K[T;T⁻¹]) ≠ 0 := by
      intro hz
      have he := congrArg (fun Q : K[T;T⁻¹] => Q.coeff 0) hz
      have hc : (1 / 3 : K) = 0 := by simpa [LaurentPolynomial.C_apply] using he
      exact one_div_ne_zero h3 hc
    rw [ActualChiEndpoints.zeta]
    exact mul_ne_zero
      (mul_ne_zero hC3 ht)
      (pow_ne_zero _ (WPFiniteZSource.Abar_nonzero p hp))
  have hm := ActualGreenResidue.actual_mapped_CM_source (K := K) p hp
  apply mul_left_cancel₀ hζ
  linear_combination hm +
    ((ActualGreenResidue.HpullK (K := K) p).toLaurent +
      2 * LaurentPolynomial.C (ActualGreenResidue.hK (K := K) p)) * hRζ

/-- Collecting the actual CB branch against the root H band retains the
original CM derivative and the full harmonic constant source. -/
theorem native_actual_CB_H_branch_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (S : K[T;T⁻¹]) :
    -LaurentPolynomial.C (3 / 2 : K) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * S *
        (ActualGreenResidue.HpullK (K := K) p).toLaurent +
      S * (ActualThreePhase.CBK (K := K) p).toLaurent * (33 - 12 * T 1) =
    -(WPFiniteZSource.Abar : K[X]).toLaurent * S *
        D (ActualGreenResidue.CMK (K := K) p).toLaurent +
      LaurentPolynomial.C (3 * ActualGreenResidue.hK (K := K) p) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * S := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hc : (3 / 2 : K) * 2 = 3 := by
    field_simp [h2]
  have hcL := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc
  simp only [map_mul, map_ofNat] at hcL
  have hm := native_actual_CB_H_cleared (K := K) p hp
  simp only [map_mul, map_ofNat]
  linear_combination S * hm +
    WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * S *
      LaurentPolynomial.C (ActualGreenResidue.hK (K := K) p) * hcL

/-- The same branch collection uses the actual polynomial H/Abar quotient.
This is the source cancellation required by the root kernel/Xi collection. -/
theorem native_actual_CB_H_quotient_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (S : K[T;T⁻¹]) :
    (WPFiniteZSource.Abar : K[X]).toLaurent *
        (-LaurentPolynomial.C (3 / 2 : K) *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * S *
          (lowHBranchYQuotient (nativeH (K := K) p)).toLaurent) +
      S * (ActualThreePhase.CBK (K := K) p).toLaurent * (33 - 12 * T 1) =
    -(WPFiniteZSource.Abar : K[X]).toLaurent * S *
        D (ActualGreenResidue.CMK (K := K) p).toLaurent +
      LaurentPolynomial.C (3 * ActualGreenResidue.hK (K := K) p) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * S := by
  have hy : (WPFiniteZSource.Abar : K[X]).toLaurent *
        (lowHBranchYQuotient (nativeH (K := K) p)).toLaurent =
      (ActualGreenResidue.HpullK (K := K) p).toLaurent := by
    rw [← nativeH_original_Hpull p hp,
      lowHBranchYQuotient_source _ (nativeH_origin p), map_mul]
  have he := native_actual_CB_H_branch_collection (K := K) p hp S
  calc
    _ = -LaurentPolynomial.C (3 / 2 : K) *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * S *
          ((WPFiniteZSource.Abar : K[X]).toLaurent *
            (lowHBranchYQuotient (nativeH (K := K) p)).toLaurent) +
        S * (ActualThreePhase.CBK (K := K) p).toLaurent * (33 - 12 * T 1) := by ring
    _ = _ := by rw [hy]; exact he

/-- Integration by parts keeps the actual full CM source and the harmonic
branch residue. No signed band, origin or endpoint is assigned a value. -/
theorem native_actual_CB_H_branch_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (S : K[T;T⁻¹]) :
    originPole ((WPFiniteZSource.Abar : K[X]).toLaurent *
        (-LaurentPolynomial.C (3 / 2 : K) *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * S *
          (lowHBranchYQuotient (nativeH (K := K) p)).toLaurent) +
      S * (ActualThreePhase.CBK (K := K) p).toLaurent * (33 - 12 * T 1)) =
    ((ActualGreenResidue.CMK (K := K) p).toLaurent * D S).coeff (-1) +
      (3 * ActualGreenResidue.hK (K := K) p) *
        originPole (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * S) := by
  have hz : (D (S * (ActualGreenResidue.CMK (K := K) p).toLaurent)).coeff (-1) = 0 := by
    rw [D_coeff]
    norm_num
  rw [D_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hz
  have hc : D S * (ActualGreenResidue.CMK (K := K) p).toLaurent =
      (ActualGreenResidue.CMK (K := K) p).toLaurent * D S := by ring
  rw [hc] at hz
  rw [native_actual_CB_H_quotient_collection p hp S]
  rw [show -(WPFiniteZSource.Abar : K[X]).toLaurent * S *
        D (ActualGreenResidue.CMK (K := K) p).toLaurent +
      LaurentPolynomial.C (3 * ActualGreenResidue.hK (K := K) p) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * S =
      LaurentPolynomial.C (3 * ActualGreenResidue.hK (K := K) p) *
        (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * S) -
      (WPFiniteZSource.Abar : K[X]).toLaurent *
        (S * D (ActualGreenResidue.CMK (K := K) p).toLaurent) by ring]
  rw [originPole_sub, originPole_C_mul, originPole_cleared p hp]
  linear_combination -hz

/-- The actual whole norm derivative supplies the original LowH Xi block
and its retained branch term before residue extraction. -/
theorem native_actual_Z52_H_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (η : K) (H : K[X]) (h0 : H.coeff 0 = 0) :
    let G := T (p : ℤ)
    let Xn := T (((p - 1) / 2 : ℕ) : ℤ)
    let Bp := 4 * G - 11
    let φ := 4 * T (-(p : ℤ)) - 11
    let sN := WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)
    let u := (actualAK (K := K) p).toLaurent
    let v := invert u
    let P := WPFiniteZSource.P p η
    let Ds := (Dstar p : K[X]).toLaurent
    let y := (lowHCubicY H).toLaurent
    let yl := (lowHqCubicDensity H).toLaurent
    let ylq := lowHLinearYQLog H
    let Q := (lowHBranchYQuotient H).toLaurent;
    -LaurentPolynomial.C (5 / 24 : K) * G * (y * D (actualZ52 p η)) =
      (LaurentPolynomial.C (5 / 12 : K) * G *
          (v * (y * D u) + (u - (1 + Xn) * v) * (y * D v)) +
        LaurentPolynomial.C (5 / 24 : K) * G * (u * yl - Xn * v * ylq) -
        LaurentPolynomial.C (5 / 4 : K) * G *
          (v * (y * (D P - D Ds)) + (P - Ds) * (y * D v))) +
      LaurentPolynomial.C (5 / 8 : K) * G * sN * (Bp * u + φ * v) * Q := by
  let f : K[T;T⁻¹] →+* LaurentSeries K := localFiniteSeriesHom
  have hfC (c : K) : f (LaurentPolynomial.C c) = algebraMap K (LaurentSeries K) c :=
    localFiniteSeries_C c
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h2S : (2 : LaurentSeries K) ≠ 0 := by
    change HahnSeries.C (2 : K) ≠ 0
    exact HahnSeries.C_ne_zero h2
  have h3S : (3 : LaurentSeries K) ≠ 0 := by
    change HahnSeries.C (3 : K) ≠ 0
    exact HahnSeries.C_ne_zero h3
  have hU := congrArg f (native_u_shifted_density (K := K) p hp H h0)
  have hV := congrArg f (native_v_shifted_density (K := K) p hp H h0)
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat] at hU hV
  have he := original_Z52_H_collection h2S h3S
    (f (T (p : ℤ))) (f (T (((p - 1) / 2 : ℕ) : ℤ)))
    (f (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)))
    (f (4 * T (p : ℤ) - 11)) (f (4 * T (-(p : ℤ)) - 11))
    (f (actualAK (K := K) p).toLaurent)
    (f (invert (actualAK (K := K) p).toLaurent))
    (f (WPFiniteZSource.P p η)) (f (Dstar p : K[X]).toLaurent)
    (f ((lowHCubicY H).toLaurent * D (actualAK (K := K) p).toLaurent))
    (f ((lowHCubicY H).toLaurent * D (invert (actualAK (K := K) p).toLaurent)))
    (f ((lowHCubicY H).toLaurent * D (WPFiniteZSource.P p η)))
    (f ((lowHCubicY H).toLaurent * D (Dstar p : K[X]).toLaurent))
    (f (lowHqCubicDensity H).toLaurent) (f (lowHLinearYQLog H))
    (f (lowHBranchYQuotient H).toLaurent)
    (by simpa only [map_mul, map_sub, map_ofNat] using hU)
    (by simpa only [map_mul, map_sub, map_ofNat] using hV)
  apply lowH_whole_finiteSeries_injective
  change f _ = f _
  rw [actual_Z52_derivative p η]
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat,
    hfC, map_div₀, map_one] at he ⊢
  convert he using 1 <;> ring

/-- The actual root Euler derivative and the original two elementary H
terms give the complete kernel/Xi part. The retained branch is exactly
the coefficient multiplying the original CB carrier in the marked source. -/
theorem native_actual_root_H_kernel_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (η : K) (H : K[X]) (h0 : H.coeff 0 = 0) :
    let G := T (p : ℤ)
    let Xp := T (-(p : ℤ))
    let Xn := T (((p - 1) / 2 : ℕ) : ℤ)
    let sN := WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)
    let u := (actualAK (K := K) p).toLaurent
    let v := invert u
    let P := WPFiniteZSource.P p η
    let Ds := (Dstar p : K[X]).toLaurent
    let y := (lowHCubicY H).toLaurent
    let yl := (lowHqCubicDensity H).toLaurent
    let ylq := lowHLinearYQLog H
    let z := lowHLinearYOverX H
    let Q := (lowHBranchYQuotient H).toLaurent
    let KB := literalKB (K := K) p;
    -y * D (actualRootUniversalV p η) - KB * yl +
        LaurentPolynomial.C (1 / 2 : K) * KB * z =
      (P - LaurentPolynomial.C (1 / 3 : K) * u) * y * D KB -
        LaurentPolynomial.C (5 / 6 : K) * KB * yl +
      (LaurentPolynomial.C (5 / 12 : K) * G *
          (v * (y * D u) + (u - (1 + Xn) * v) * (y * D v)) +
        LaurentPolynomial.C (5 / 24 : K) * G * (u * yl - Xn * v * ylq) -
        LaurentPolynomial.C (5 / 4 : K) * G *
          (v * (y * (D P - D Ds)) + (P - Ds) * (y * D v))) +
      -LaurentPolynomial.C (3 / 2 : K) * sN *
        (-2 * (1 - LaurentPolynomial.C (2 / 3 : K) * Xp) * KB +
          LaurentPolynomial.C (5 / 12 : K) * G * actualR52 (K := K) p) * Q := by
  let f : K[T;T⁻¹] →+* LaurentSeries K := localFiniteSeriesHom
  have hfC (c : K) : f (LaurentPolynomial.C c) = algebraMap K (LaurentSeries K) c :=
    localFiniteSeries_C c
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h2S : (2 : LaurentSeries K) ≠ 0 := by
    change HahnSeries.C (2 : K) ≠ 0
    exact HahnSeries.C_ne_zero h2
  have h3S : (3 : LaurentSeries K) ≠ 0 := by
    change HahnSeries.C (3 : K) ≠ 0
    exact HahnSeries.C_ne_zero h3
  have h4S : (4 : LaurentSeries K) ≠ 0 := by
    convert pow_ne_zero 2 h2S using 1
    norm_num
  have h6S : (6 : LaurentSeries K) ≠ 0 := by
    convert mul_ne_zero h2S h3S using 1
    ring
  have h8S : (8 : LaurentSeries K) ≠ 0 := by
    convert pow_ne_zero 3 h2S using 1
    norm_num
  have h12S : (12 : LaurentSeries K) ≠ 0 := by
    convert mul_ne_zero h4S h3S using 1
    ring
  have h24S : (24 : LaurentSeries K) ≠ 0 := by
    convert mul_ne_zero h8S h3S using 1
    ring
  have hG : D (T (p : ℤ) : K[T;T⁻¹]) = 0 := by
    have h := D_monomial (1 : K) (p : ℤ)
    simpa only [map_one, one_mul, Int.cast_natCast, CharP.cast_eq_zero,
      map_zero, zero_mul] using h
  have hU := congrArg f (native_u_shifted_density (K := K) p hp H h0)
  have hP := congrArg f (native_P_density (K := K) p hp η H h0)
  have hZ := congrArg f (native_actual_Z52_H_collection (K := K) p hp η H h0)
  apply lowH_whole_finiteSeries_injective
  change f _ = f _
  simp only [actualRootUniversalV, actualR52, map_add, D_mul, map_sub, D_C,
    hG, zero_mul, mul_zero, zero_add, add_zero]
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat,
    hfC, map_div₀, map_one] at hU hP hZ ⊢
  linear_combination (norm := (field_simp [h2S, h3S, h4S, h6S, h8S, h12S, h24S]; ring))
    hZ + f (literalKB (K := K) p) * hP -
      (f (literalKB (K := K) p) / 6) * hU

/-- The kernel and Xi terms are the literal first block of IR64d.
The native carriers and all weighted derivatives remain actual expressions. -/
noncomputable def nativeRootHKernelXi (p : ℕ) [Fact p.Prime] [CharP K p]
    (η : K) (H : K[X]) : K[T;T⁻¹] :=
  let G := T (p : ℤ)
  let Xn := T (((p - 1) / 2 : ℕ) : ℤ)
  let u := (actualAK (K := K) p).toLaurent
  let v := invert u
  let P := WPFiniteZSource.P p η
  let Ds := (Dstar p : K[X]).toLaurent
  let y := (lowHCubicY H).toLaurent
  let yl := (lowHqCubicDensity H).toLaurent
  let ylq := lowHLinearYQLog H
  let KB := literalKB (K := K) p
  (P - LaurentPolynomial.C (1 / 3 : K) * u) * y * D KB -
    LaurentPolynomial.C (5 / 6 : K) * KB * yl +
    (LaurentPolynomial.C (5 / 12 : K) * G *
      (v * (y * D u) + (u - (1 + Xn) * v) * (y * D v)) +
      LaurentPolynomial.C (5 / 24 : K) * G * (u * yl - Xn * v * ylq) -
      LaurentPolynomial.C (5 / 4 : K) * G *
        (v * (y * (D P - D Ds)) + (P - Ds) * (y * D v)))

/-- This is exactly the coefficient of the original CB source after NC123. -/
noncomputable def nativeActualCBMultiplier (p : ℕ) [Fact p.Prime] [CharP K p] :
    K[T;T⁻¹] :=
  -2 * (1 - LaurentPolynomial.C (2 / 3 : K) * T (-(p : ℤ))) *
      literalKB (K := K) p +
    LaurentPolynomial.C (5 / 12 : K) * T (p : ℤ) * actualR52 (K := K) p

/-- Its derivative retains both actual native halves; the two Frobenius
phases have zero derivative in characteristic p. -/
theorem native_actual_CB_multiplier_derivative (p : ℕ) [Fact p.Prime] [CharP K p] :
    D (nativeActualCBMultiplier (K := K) p) =
      -2 * (1 - LaurentPolynomial.C (2 / 3 : K) * T (-(p : ℤ))) *
          D (literalKB (K := K) p) -
        LaurentPolynomial.C (5 / 12 : K) * T (p : ℤ) *
          ((4 * T (-(p : ℤ)) - 11) *
              D (invert (actualAK (K := K) p).toLaurent) +
            (4 * T (p : ℤ) - 11) * D (actualAK (K := K) p).toLaurent) := by
  have hG : D (T (p : ℤ) : K[T;T⁻¹]) = 0 := by
    have h := D_monomial (1 : K) (p : ℤ)
    simpa only [map_one, one_mul, Int.cast_natCast, CharP.cast_eq_zero,
      map_zero, zero_mul] using h
  have hXp : D (T (-(p : ℤ)) : K[T;T⁻¹]) = 0 := by
    have h := D_monomial (1 : K) (-(p : ℤ))
    simpa only [map_one, one_mul, Int.cast_neg, Int.cast_natCast,
      CharP.cast_eq_zero, neg_zero, map_zero, zero_mul] using h
  have h1 : D (1 : K[T;T⁻¹]) = 0 := by
    simpa only [map_one] using D_C (1 : K)
  have h2 : D (-2 : K[T;T⁻¹]) = 0 := by
    simpa only [map_neg, map_ofNat] using D_C (-2 : K)
  simp only [nativeActualCBMultiplier, map_add, D_mul, map_sub, D_C,
    hG, hXp, h1, h2, zero_mul, mul_zero, sub_zero, zero_add, add_zero,
    actual_R52_derivative p]
  ring

/-- The actual universal source collects the original root H block and
its whole CB branch. The bracket derivative, metric, endpoint values and
both harmonic contributions are retained as their original sources. -/
theorem native_actual_universal_H_CB_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (η : K) (h4 : (4 : K) ≠ 0) :
    actualUniversalDensity (K := K) p η h4 =
      (actualUniversalV (K := K) p η * (33 - 12 * T 1) +
        (WPFiniteZSource.Abar : K[X]).toLaurent *
          nativeRootHKernelXi p η (nativeH (K := K) p)) -
      (WPFiniteZSource.Abar : K[X]).toLaurent *
        (nativeActualCBMultiplier p * D (ActualGreenResidue.CMK (K := K) p).toLaurent) +
      LaurentPolynomial.C (3 * ActualGreenResidue.hK (K := K) p) *
        (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          nativeActualCBMultiplier p) +
      (WPFiniteZSource.Abar : K[X]).toLaurent *
        (LaurentPolynomial.C (ActualGreenResidue.hK (K := K) p) *
          (literalKB (K := K) p * T (-1))) -
      literalKB (K := K) p * actualMarkedEndpointSource p η h4 -
      (WPFiniteZSource.Abar : K[X]).toLaurent *
        coefficientMap (ActualThreePhase.φ (K := K) p) (actualEulerBracketDensity p) -
      LaurentPolynomial.C (1 / 3 : K) *
        ((WPFiniteZSource.Abar : K[X]).toLaurent *
          coefficientMap (ActualThreePhase.φ (K := K) p) (properMetricDensity p)) := by
  have hRoot := native_actual_root_H_kernel_collection (K := K) p hp η
    (nativeH p) (nativeH_origin p)
  have hCB := native_actual_CB_H_quotient_collection (K := K) p hp
    (nativeActualCBMultiplier p)
  have hyL : (WPFiniteZSource.Abar : K[X]).toLaurent *
      (lowHqCubicDensity (nativeH (K := K) p)).toLaurent =
      (lowHCubicY (nativeH (K := K) p)).toLaurent * (33 - 12 * T 1) := by
    rw [lowH_linear_ylog_polynomial,
      lowHBranchYQuotient_source _ (nativeH_origin p), map_mul]
    simp only [map_mul, map_sub, map_ofNat, Polynomial.toLaurent_X]
    ring
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hc : (2 : K[T;T⁻¹]) * LaurentPolynomial.C (1 / 2 : K) = 1 := by
    change LaurentPolynomial.C (2 : K) * LaurentPolynomial.C (1 / 2 : K) = 1
    rw [← map_mul, mul_one_div_cancel h2, map_one]
  rw [actualUniversalDensity_source p η h4]
  simp only [actualMarkedEulerDensity, actualMarkedNonfDensity, actualUniversalV]
  rw [← nativeH_original_Hpull p hp]
  dsimp only [lowHLinearYOverX] at hRoot
  dsimp only [nativeRootHKernelXi, nativeActualCBMultiplier, lowHLinearYOverX] at hCB ⊢
  linear_combination
    (WPFiniteZSource.Abar : K[X]).toLaurent * hRoot + hCB +
    literalKB (K := K) p * hyL +
    ((WPFiniteZSource.Abar : K[X]).toLaurent *
      LaurentPolynomial.C (ActualGreenResidue.hK (K := K) p) *
      literalKB p * T (-1)) * hc

/-- Finite Laurent integration by parts supplies the actual CM derivative
term without assigning any bracket, metric, endpoint or branch residue. -/
theorem native_actual_universal_H_CB_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (η : K) (h4 : (4 : K) ≠ 0) :
    originPole (actualUniversalDensity (K := K) p η h4) =
      originPole (actualUniversalV (K := K) p η * (33 - 12 * T 1)) +
      (nativeRootHKernelXi p η (nativeH (K := K) p)).coeff (-1) +
      ((ActualGreenResidue.CMK (K := K) p).toLaurent *
        D (nativeActualCBMultiplier p)).coeff (-1) +
      (3 * ActualGreenResidue.hK (K := K) p) *
        originPole (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          nativeActualCBMultiplier p) +
      ActualGreenResidue.hK (K := K) p * (literalKB p * T (-1)).coeff (-1) -
      originPole (literalKB (K := K) p * actualMarkedEndpointSource p η h4) -
      (coefficientMap (ActualThreePhase.φ (K := K) p) (actualEulerBracketDensity p)).coeff (-1) -
      (1 / 3 : K) *
        (coefficientMap (ActualThreePhase.φ (K := K) p) (properMetricDensity p)).coeff (-1) := by
  have hz : (D (nativeActualCBMultiplier (K := K) p *
      (ActualGreenResidue.CMK (K := K) p).toLaurent)).coeff (-1) = 0 := by
    rw [D_coeff]
    norm_num
  rw [D_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hz
  have hc : D (nativeActualCBMultiplier (K := K) p) *
      (ActualGreenResidue.CMK (K := K) p).toLaurent =
      (ActualGreenResidue.CMK (K := K) p).toLaurent *
        D (nativeActualCBMultiplier p) := by ring
  rw [hc] at hz
  rw [native_actual_universal_H_CB_collection p hp η h4]
  simp only [originPole_add, originPole_sub, originPole_C_mul,
    originPole_cleared p hp, C_mul_coeff]
  linear_combination -hz

end WPFieldAssembly.NativeClosureLowH
