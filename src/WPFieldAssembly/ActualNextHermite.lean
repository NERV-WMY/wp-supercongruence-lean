import WPFieldAssembly.ActualDeltaUNextSource
import WPFieldAssembly.NativeIR28
import WPFiniteKSource
import Mathlib.Algebra.Polynomial.FieldDivision

open scoped Polynomial
open Polynomial WPPIntegralReduction
  WPActualRankTwoGaussODE WPActualRankTwoLowTaylor
  WPActualRankTwoProper WPActualRankTwoComparison
  WPActualRankTwoLegendreField WPActualRankTwoCarryField
  WPFieldAssembly.NativeIR28 WPFieldAssembly.ActualDeltaUNextSource
  WPFiniteKSource WPActualPositivePair WPActualRankTwoFirstLift
  WPActualRankTwoResidueSource WPFieldAssembly.NativeFullGreen
  WPActualGaussBottom WPFieldAssembly.NativeQuadraticInverse
  WPFieldAssembly.ActualR0Node WPFieldAssembly.ConicKernel

namespace WPFieldAssembly.ActualNextHermite
set_option maxHeartbeats 1400000

noncomputable def hermiteOperator {K : Type*} [CommRing K]
    (Y C : K[X]) : K[X] :=
  (1 - X ^ 2) * (Y * C.derivative - 2 * Y.derivative * C)

noncomputable def hermiteNumerator {K : Type*} [CommRing K]
    (Y n A : K[X]) : K[X] :=
  A * n + (1 - X ^ 2) * Y * n * (A * n.derivative - A.derivative * n)

noncomputable def hermiteTail {K : Type*} [CommRing K]
    (d : ℕ) (Y n A : K[X]) : K[X] :=
  -3 * (1 - X ^ 2) * A * n.derivative -
    2 * (1 - X ^ 2) * X * n * n.derivative -
    2 * Y * (A + X * n) + 2 * C (d : K) * (1 - X ^ 2) * n ^ 2 +
    (1 - X ^ 2) * A.derivative * n

theorem hermiteOperator_add {K : Type*} [CommRing K] (Y C D : K[X]) :
    hermiteOperator Y (C + D) = hermiteOperator Y C + hermiteOperator Y D := by
  simp only [hermiteOperator, derivative_add]; ring

theorem hermiteOperator_C_mul {K : Type*} [CommRing K] (a : K) (Y C : K[X]) :
    hermiteOperator Y (Polynomial.C a * C) = Polynomial.C a * hermiteOperator Y C := by
  simp only [hermiteOperator, derivative_C_mul]; ring

theorem hermiteOperator_square_product {K : Type*} [CommRing K] (Y D : K[X]) :
    hermiteOperator Y (Y ^ 2 * D) = (1 - X ^ 2) * Y ^ 3 * D.derivative := by
  simp only [hermiteOperator, derivative_mul, derivative_pow_succ]
  norm_num1
  simp only [_root_.map_ofNat]
  ring

-- The complete triple-pole cancellation, expressed as polynomial algebra.
theorem hermite_numerator_source {K : Type*} [CommRing K]
    (d : ℕ) (Y n A : K[X])
    (hW : (1 - X ^ 2) * (Y * n.derivative - Y.derivative * n) = 1 - Y ^ 2)
    (hn : legendreJacobi d n = -2 * Y.derivative)
    (hA : legendreJacobi d A = 2 * X * Y.derivative - 2 * C (d : K) * Y) :
    hermiteOperator Y (hermiteNumerator Y n A) - 2 * A - 2 * X * n * Y ^ 2 =
      Y ^ 3 * hermiteTail d Y n A := by
  simp only [hermiteOperator, hermiteNumerator, hermiteTail, legendreJacobi,
    derivative_add, derivative_mul, derivative_sub, derivative_one,
    derivative_X, derivative_pow_succ] at hn hA ⊢
  norm_num1 at hn hA ⊢
  simp only [_root_.map_ofNat]
  linear_combination
    (2 * A + (1 - X ^ 2) * Y * (A * n.derivative - A.derivative * n) +
      2 * Y ^ 2 * (A + X * n)) * hW +
    Y ^ 2 * (1 - X ^ 2) * n * A * hn -
    Y ^ 2 * (1 - X ^ 2) * n ^ 2 * hA

noncomputable def hermiteCorrection {K : Type*} [Field K] (Y n A : K[X]) : K[X] :=
  C ((2 : K)⁻¹) * (hermiteNumerator Y n A % (Y ^ 2))

theorem hermiteOperator_degree {K : Type*} [Field K]
    (d : ℕ) (hd : 1 ≤ d) (Y C : K[X])
    (hY : Y.natDegree ≤ d) (hC : C.natDegree ≤ 2 * d - 1) :
    (hermiteOperator Y C).natDegree ≤ 3 * d := by
  have hDY : Y.derivative.natDegree ≤ d - 1 := by
    have h := natDegree_derivative_le Y; omega
  have hDC : C.derivative.natDegree ≤ 2 * d - 2 := by
    have h := natDegree_derivative_le C; omega
  have h1 : (Y * C.derivative).natDegree ≤ 3 * d - 2 :=
    (natDegree_mul_le_of_le hY hDC).trans (by omega)
  have h2 : (2 * Y.derivative * C).natDegree ≤ 3 * d - 2 := by
    rw [mul_assoc]
    exact (natDegree_C_mul_le _ _).trans
      ((natDegree_mul_le_of_le hDY hC).trans (by omega))
  have hq : (1 - X ^ 2 : K[X]).natDegree ≤ 2 := by compute_degree
  exact (natDegree_mul_le_of_le hq
    (by simpa only [max_self] using natDegree_sub_le_of_le h1 h2)).trans (by omega)

private theorem cube_divisible_small {K : Type*} [Field K]
    (d : ℕ) (Y P : K[X]) (hY : Y ≠ 0) (hYdeg : Y.natDegree = d)
    (hPdeg : P.natDegree ≤ 3 * d) (hdiv : Y ^ 3 ∣ P) :
    ∃ a : K, P = C a * Y ^ 3 := by
  rcases hdiv with ⟨W, hW⟩
  by_cases hz : W = 0
  · refine ⟨0, ?_⟩; rw [hW, hz]; simp
  · have hWd : W.natDegree ≤ 0 := by
      rw [hW, natDegree_mul (pow_ne_zero 3 hY) hz, natDegree_pow, hYdeg] at hPdeg
      omega
    have hWC : W = C (W.coeff 0) := by
      ext j
      cases j with
      | zero => simp
      | succ j =>
        rw [coeff_C, if_neg (by omega)]
        exact coeff_eq_zero_of_natDegree_lt (by omega)
    refine ⟨W.coeff 0, ?_⟩
    calc
      P = Y ^ 3 * W := hW
      _ = Y ^ 3 * C (W.coeff 0) := congrArg (fun Q : K[X] => Y ^ 3 * Q) hWC
      _ = _ := mul_comm _ _

-- No root-local residue or value of Y at a CM point occurs in this theorem.
theorem hermite_correction_source {K : Type*} [Field K]
    (d : ℕ) (hd : 1 ≤ d) (Y n A : K[X]) (h : K)
    (h2 : (2 : K) ≠ 0) (hY : Y ≠ 0) (hYdeg : Y.natDegree = d)
    (hndeg : n.natDegree < d) (hAdeg : A.natDegree ≤ d)
    (hY1 : Y.eval 1 = 1) (hn1 : n.eval 1 = -h) (hA1 : A.eval 1 = 0)
    (hW : (1 - X ^ 2) * (Y * n.derivative - Y.derivative * n) = 1 - Y ^ 2)
    (hn : legendreJacobi d n = -2 * Y.derivative)
    (hA : legendreJacobi d A = 2 * X * Y.derivative - 2 * C (d : K) * Y) :
    (hermiteCorrection Y n A).natDegree ≤ 2 * d - 1 ∧
      hermiteOperator Y (hermiteCorrection Y n A) =
        X * n * Y ^ 2 + A + C h * Y ^ 3 := by
  let R := hermiteNumerator Y n A % (Y ^ 2)
  let D := hermiteNumerator Y n A / (Y ^ 2)
  let c := hermiteCorrection Y n A
  let N := hermiteOperator Y c - A - X * n * Y ^ 2
  have hY2 : (Y ^ 2).natDegree = 2 * d := by rw [natDegree_pow, hYdeg]
  have hRdeg : R.natDegree < 2 * d := by
    simpa only [R, hY2] using
      natDegree_mod_lt (hermiteNumerator Y n A)
        (show (Y ^ 2).natDegree ≠ 0 by rw [hY2]; omega)
  have hcdeg : c.natDegree ≤ 2 * d - 1 := by
    change (C ((2 : K)⁻¹) * R).natDegree ≤ _
    exact (natDegree_C_mul_le _ _).trans (by omega)
  have hdivision : hermiteNumerator Y n A = Y ^ 2 * D + R := by
    simpa only [D, R, mul_comm] using
      (EuclideanDomain.div_add_mod (hermiteNumerator Y n A) (Y ^ 2)).symm
  have hnum := hermite_numerator_source d Y n A hW hn hA
  have hdivisionL := congrArg (hermiteOperator Y) hdivision
  rw [hermiteOperator_add, hermiteOperator_square_product] at hdivisionL
  have hR : hermiteOperator Y R - 2 * A - 2 * X * n * Y ^ 2 =
      Y ^ 3 * (hermiteTail d Y n A - (1 - X ^ 2) * D.derivative) := by
    linear_combination hnum - hdivisionL
  have hhalf : (C ((2 : K)⁻¹) : K[X]) * 2 = 1 := by
    change C ((2 : K)⁻¹) * C (2 : K) = 1
    rw [← C_mul, inv_mul_cancel₀ h2, C_1]
  have hN : N = Y ^ 3 *
      (C ((2 : K)⁻¹) * (hermiteTail d Y n A - (1 - X ^ 2) * D.derivative)) := by
    dsimp only [N, c, hermiteCorrection]
    rw [hermiteOperator_C_mul]
    change C ((2 : K)⁻¹) * hermiteOperator Y R - A - X * n * Y ^ 2 = _
    linear_combination C ((2 : K)⁻¹) * hR + (A + X * n * Y ^ 2) * hhalf
  have hT : (X * n * Y ^ 2).natDegree ≤ 3 * d := by
    have hnle : n.natDegree ≤ d - 1 := by omega
    have hXn : (X * n).natDegree ≤ d :=
      (natDegree_mul_le_of_le natDegree_X_le hnle).trans (by omega)
    exact (natDegree_mul_le_of_le hXn hY2.le).trans (by omega)
  have hNdeg : N.natDegree ≤ 3 * d := by
    have hL := hermiteOperator_degree d hd Y c hYdeg.le hcdeg
    have hA3 : A.natDegree ≤ 3 * d := hAdeg.trans (by omega)
    have hLA : (hermiteOperator Y c - A).natDegree ≤ 3 * d := by
      simpa only [max_self] using natDegree_sub_le_of_le hL hA3
    dsimp only [N]
    simpa only [max_self] using natDegree_sub_le_of_le hLA hT
  obtain ⟨a, ha⟩ := cube_divisible_small d Y N hY hYdeg hNdeg ⟨_, hN⟩
  have hN1 : N.eval 1 = h := by
    simp [N, hermiteOperator, hY1, hn1, hA1]
  have hah : a = h := by
    have he := congrArg (fun P : K[X] => P.eval 1) ha
    simpa only [hN1, eval_mul, eval_C, eval_pow, hY1, one_pow, mul_one] using he.symm
  refine ⟨hcdeg, ?_⟩
  rw [hah] at ha
  change hermiteOperator Y c - A - X * n * Y ^ 2 = C h * Y ^ 3 at ha
  linear_combination ha

-- The inverse of qY' modulo Y² is polynomial; no value of Y is inverted.
theorem hermite_root_inverse {K : Type*} [CommRing K] (Y n : K[X])
    (hW : (1 - X ^ 2) * (Y * n.derivative - Y.derivative * n) = 1 - Y ^ 2) :
    let a := (1 - X ^ 2) * n.derivative + Y
    let v := -n * (1 + Y * a);
    (1 - X ^ 2) * Y.derivative * v + Y ^ 2 * a ^ 2 = 1 := by
  dsimp only
  have hbez : Y * ((1 - X ^ 2) * n.derivative + Y) -
      (1 - X ^ 2) * Y.derivative * n = 1 := by
    linear_combination hW
  linear_combination
    (1 + Y * ((1 - X ^ 2) * n.derivative + Y)) * hbez

theorem hermite_inverse_representative {K : Type*} [CommRing K] (Y n A : K[X]) :
    let q := (1 - X ^ 2 : K[X])
    let a := q * n.derivative + Y
    let v := -n * (1 + Y * a);
    -A * v - Y * q * A.derivative * v ^ 2 - hermiteNumerator Y n A =
      Y ^ 2 * (A * n - 2 * q * A.derivative * n ^ 2 * a -
        Y * q * A.derivative * n ^ 2 * a ^ 2) := by
  dsimp only [hermiteNumerator]
  ring

variable (p : ℕ) [Fact p.Prime]

noncomputable def actualC (hp : 19 ≤ p) : (ZMod p)[X] :=
  hermiteCorrection (actualLegendreJacobi p) (properLegendreJacobi p)
    (actualVariationField p (by omega))

theorem actual_C_source_degree (hp : 19 ≤ p) :
    (actualC p hp).natDegree ≤ 2 * (p / 6) - 1 ∧
      (1 - X ^ 2) *
        (actualLegendreJacobi p * (actualC p hp).derivative -
          2 * (actualLegendreJacobi p).derivative * actualC p hp) =
      X * properLegendreJacobi p * actualLegendreJacobi p ^ 2 +
        actualVariationField p (by omega) +
        Polynomial.C (fieldHarmonic p (p / 6)) * actualLegendreJacobi p ^ 3 := by
  have hY : actualLegendreJacobi p ≠ 0 := by
    intro hz
    have he := congrArg (fun P : (ZMod p)[X] => P.eval 1) hz
    rw [actualLegendreJacobi_endpoint_one] at he
    simp at he
  have hA : legendreJacobi (p / 6) (actualVariationField p (by omega : 7 ≤ p)) =
      2 * X * (actualLegendreJacobi p).derivative -
        2 * Polynomial.C ((p / 6 : ℕ) : ZMod p) * actualLegendreJacobi p := by
    linear_combination actualVariationField_ODE p (by omega : 7 ≤ p)
  exact hermite_correction_source (p / 6) (by omega)
    (actualLegendreJacobi p) (properLegendreJacobi p)
    (actualVariationField p (by omega)) (fieldHarmonic p (p / 6))
    (WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega))
    hY (actual_legendre_exact_degree p hp)
    (properLegendreJacobi_degree p (by omega))
    (actualVariationField_degree p (by omega))
    (actualLegendreJacobi_endpoint_one p)
    (properLegendreJacobi_endpoint_one p)
    (actualVariationField_endpoint_one p (by omega))
    (properLegendreJacobi_wronskian p (by omega))
    (properLegendreJacobi_source p (by omega)) hA

theorem hermite_low_kernel_zero {K : Type*} [Field K]
    (d : ℕ) (Y n D : K[X]) (h2 : (2 : K) ≠ 0)
    (hY : Y ≠ 0) (hYdeg : Y.natDegree = d)
    (hW : (1 - X ^ 2) * (Y * n.derivative - Y.derivative * n) = 1 - Y ^ 2)
    (hDdeg : D.natDegree < 2 * d) (hzero : hermiteOperator Y D = 0) : D = 0 := by
  let q : K[X] := 1 - X ^ 2
  let a := q * n.derivative + Y
  let H := a * D - Polynomial.C ((2 : K)⁻¹) * q * n * D.derivative
  have hqdeg : q.natDegree = 2 := by dsimp [q]; compute_degree; exact neg_ne_zero.mpr one_ne_zero
  have hq : q ≠ 0 := by intro hz; simp [hz] at hqdeg
  have hbez : Y * a - Y.derivative * (q * n) = 1 := by
    dsimp only [a, q]
    linear_combination hW
  have hhalf : (Polynomial.C ((2 : K)⁻¹) : K[X]) * 2 = 1 := by
    change Polynomial.C ((2 : K)⁻¹) * Polynomial.C (2 : K) = 1
    rw [← C_mul, inv_mul_cancel₀ h2, C_1]
  have hfactor : D = Y * H := by
    dsimp only [H]
    change q * (Y * D.derivative - 2 * Y.derivative * D) = 0 at hzero
    linear_combination -D * hbez + Polynomial.C ((2 : K)⁻¹) * n * hzero +
      q * n * Y.derivative * D * hhalf
  have hH : Y * H.derivative - Y.derivative * H = 0 := by
    rw [hfactor] at hzero
    simp only [hermiteOperator, derivative_mul] at hzero
    have hz : q * Y * (Y * H.derivative - Y.derivative * H) = 0 := by
      dsimp only [q]
      linear_combination hzero
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hq hY)
  let J := a * H - q * n * H.derivative
  have hHfactor : H = Y * J := by
    dsimp only [J]
    linear_combination -H * hbez + q * n * hH
  have hDfactor : D = Y ^ 2 * J := by rw [hfactor, hHfactor]; ring
  by_cases hz : J = 0
  · rw [hDfactor, hz, mul_zero]
  · rw [hDfactor, natDegree_mul (pow_ne_zero 2 hY) hz,
      natDegree_pow, hYdeg] at hDdeg
    omega

theorem hermite_low_unique {K : Type*} [Field K]
    (d : ℕ) (Y n C D : K[X]) (h2 : (2 : K) ≠ 0)
    (hY : Y ≠ 0) (hYdeg : Y.natDegree = d)
    (hW : (1 - X ^ 2) * (Y * n.derivative - Y.derivative * n) = 1 - Y ^ 2)
    (hCdeg : C.natDegree < 2 * d) (hDdeg : D.natDegree < 2 * d)
    (hsource : hermiteOperator Y C = hermiteOperator Y D) : C = D := by
  apply sub_eq_zero.mp
  apply hermite_low_kernel_zero d Y n (C - D) h2 hY hYdeg hW
  · have hC : C.natDegree ≤ 2 * d - 1 := by omega
    have hD : D.natDegree ≤ 2 * d - 1 := by omega
    have hh := natDegree_sub_le_of_le hC hD
    simp only [Nat.max_self] at hh
    omega
  · simp only [hermiteOperator, derivative_sub] at hsource ⊢
    linear_combination hsource

noncomputable def actualMNumerator : (ZMod p)[X] :=
  properLegendreJacobi p * actualLegendreJacobi p - adjacentPrimitive p (p / 6)

noncomputable def actualMIntegrand : (ZMod p)[X] :=
  actualMNumerator p / (1 - X ^ 2)

noncomputable def actualM : (ZMod p)[X] :=
  WPActualPositivePair.eulerPrimitive p (X * actualMIntegrand p)

private theorem two_endpoint_division {K : Type*} [Field K]
    (P : K[X]) (h2 : (2 : K) ≠ 0) (h1 : P.eval 1 = 0)
    (hm : P.eval (-1) = 0) : (1 - X ^ 2) ∣ P := by
  obtain ⟨U, hU⟩ := (Polynomial.dvd_iff_isRoot (p := P) (a := (1 : K))).mpr h1
  have hUm : U.eval (-1) = 0 := by
    have he := congrArg (fun Q : K[X] => Q.eval (-1)) hU
    simp only [hm, eval_mul, eval_sub, eval_X, eval_C] at he
    have hz : (-2 : K) * U.eval (-1) = 0 := by linear_combination -he
    exact (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr h2)
  obtain ⟨V, hV⟩ := (Polynomial.dvd_iff_isRoot (p := U) (a := (-1 : K))).mpr hUm
  refine ⟨-V, ?_⟩
  rw [hU, hV]
  simp only [_root_.map_one, _root_.map_neg]
  ring

theorem actual_M_numerator_odd (hp : 19 ≤ p) :
    (actualMNumerator p).comp (-X) = -actualMNumerator p := by
  have hs : (C ((-1 : ZMod p) ^ (p / 6)) : (ZMod p)[X]) ^ 2 = 1 := by
    rw [← C_pow, WPActualGaussProper.negative_power_square, C_1]
  have hY : (actualLegendreJacobi p).comp (-X) =
      C ((-1 : ZMod p) ^ (p / 6)) * actualLegendreJacobi p :=
    legendreField_reflect p (p / 6) (by omega)
  rw [actualMNumerator, sub_comp, mul_comp,
    actual_proper_legendre_reflect p hp,
    hY,
    adjacentPrimitive_odd p (p / 6) (by omega)]
  linear_combination -(properLegendreJacobi p * actualLegendreJacobi p) * hs

theorem actual_M_source_degree (hp : 19 ≤ p) :
    (1 - X ^ 2) * (actualM p).derivative = actualMNumerator p ∧
      (actualM p).natDegree ≤ 2 * (p / 6) - 2 ∧
      (actualM p).coeff 0 = 0 ∧ (actualM p).comp (-X) = actualM p := by
  let d := p / 6
  let q : (ZMod p)[X] := 1 - X ^ 2
  let P := actualMNumerator p
  let J := actualMIntegrand p
  have hd : 3 ≤ d := by dsimp [d]; omega
  have hqdeg : q.natDegree = 2 := by dsimp [q]; compute_degree; exact neg_ne_zero.mpr one_ne_zero
  have hq : q ≠ 0 := by intro hz; simp [hz] at hqdeg
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have hPodd : P.comp (-X) = -P := actual_M_numerator_odd p hp
  have hP1 : P.eval 1 = 0 := by
    simp [P, actualMNumerator, actualLegendreJacobi_endpoint_one,
      properLegendreJacobi_endpoint_one, adjacentPrimitive_one]
  have hPm : P.eval (-1) = 0 := by
    have he := congrArg (fun Q : (ZMod p)[X] => Q.eval 1) hPodd
    simpa only [eval_comp, eval_neg, eval_X, hP1, neg_zero] using he
  have hdiv : q ∣ P := two_endpoint_division P h2 hP1 hPm
  have hJ : q * J = P := EuclideanDomain.mul_div_cancel' hq hdiv
  have hPdeg : P.natDegree ≤ 2 * d - 1 := by
    have hn := properLegendreJacobi_degree p (by omega : 7 ≤ p)
    have hprod : (properLegendreJacobi p * actualLegendreJacobi p).natDegree ≤
        2 * d - 1 :=
      (natDegree_mul_le_of_le (show _ ≤ d - 1 by dsimp [d]; omega)
        (actualLegendreJacobi_degree p)).trans (by dsimp [d]; omega)
    exact (natDegree_sub_le_of_le hprod (adjacentPrimitive_degree p d)).trans (by omega)
  have hJdeg : J.natDegree ≤ 2 * d - 3 := by
    by_cases hz : J = 0
    · simp [hz]
    · rw [← hJ, natDegree_mul hq hz, hqdeg] at hPdeg
      omega
  have hJodd : J.comp (-X) = -J := by
    have he := congrArg (fun Q : (ZMod p)[X] => Q.comp (-X)) hJ
    have hqe : q.comp (-X) = q := by simp [q]
    rw [mul_comp, hqe, hPodd, ← hJ] at he
    apply mul_left_cancel₀ hq
    linear_combination he
  have hXJdeg : (X * J).natDegree ≤ 2 * d - 2 :=
    (natDegree_mul_le_of_le natDegree_X_le hJdeg).trans (by omega)
  have hsmall : (X * J).natDegree < p := by
    have h := Nat.div_mul_le_self p 6
    dsimp [d] at *
    omega
  have hMD : (actualM p).derivative = J := by
    apply mul_left_cancel₀ (X_ne_zero : (X : (ZMod p)[X]) ≠ 0)
    exact WPActualPositivePair.eulerPrimitive_derivative p (X * J) hsmall (by simp)
  have hMdeg : (actualM p).natDegree ≤ 2 * d - 2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [actualM, WPActualPositivePair.eulerPrimitive_coeff,
      coeff_eq_zero_of_natDegree_lt (hXJdeg.trans_lt hj), zero_div]
  have hM0 : (actualM p).coeff 0 = 0 := by
    simp [actualM, WPActualPositivePair.eulerPrimitive_coeff]
  have hMeven : (actualM p).comp (-X) = actualM p := by
    have hXe : (X * J).comp (-X) = X * J := by
      rw [mul_comp, X_comp, hJodd]; ring
    ext j
    have he := congrArg (fun Q : (ZMod p)[X] => Q.coeff j) hXe
    rw [coeff_comp_neg] at he
    simp only [actualM, coeff_comp_neg, WPActualPositivePair.eulerPrimitive_coeff]
    linear_combination (j : ZMod p)⁻¹ * he
  exact ⟨by rw [hMD]; exact hJ, hMdeg, hM0, hMeven⟩

noncomputable def hermiteYQuotient {K : Type*} [Field K] (Y n A : K[X]) : K[X] :=
  (1 - X ^ 2) * n * (A * n.derivative - A.derivative * n) -
    Y * (hermiteNumerator Y n A / Y ^ 2)

theorem hermite_Y_quotient {K : Type*} [Field K]
    (Y n A : K[X]) (h2 : (2 : K) ≠ 0) :
    Y * hermiteYQuotient Y n A = 2 * hermiteCorrection Y n A - n * A := by
  let R := hermiteNumerator Y n A % (Y ^ 2)
  let D := hermiteNumerator Y n A / (Y ^ 2)
  have hdivision : hermiteNumerator Y n A = Y ^ 2 * D + R := by
    simpa only [D, R, mul_comm] using
      (EuclideanDomain.div_add_mod (hermiteNumerator Y n A) (Y ^ 2)).symm
  have hhalf : (2 : K[X]) * C ((2 : K)⁻¹) = 1 := by
    change C (2 : K) * C ((2 : K)⁻¹) = 1
    rw [← C_mul, mul_inv_cancel₀ h2, C_1]
  dsimp only [hermiteYQuotient, hermiteCorrection, hermiteNumerator] at ⊢ hdivision
  change Y * ((1 - X ^ 2) * n * (A * n.derivative - A.derivative * n) - Y * D) =
    2 * (C ((2 : K)⁻¹) * R) - n * A
  linear_combination hdivision - R * hhalf

noncomputable def actualCDiv (hp : 19 ≤ p) : (ZMod p)[X] :=
  hermiteYQuotient (actualLegendreJacobi p) (properLegendreJacobi p)
    (actualVariationField p (by omega))

theorem actual_C_division_degree (hp : 19 ≤ p) :
    actualLegendreJacobi p * actualCDiv p hp =
        2 * actualC p hp - properLegendreJacobi p * actualVariationField p (by omega) ∧
      (actualCDiv p hp).natDegree ≤ p / 6 - 1 := by
  have h2 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega : 0 < 2) (by omega : 2 < p)
  have hD := hermite_Y_quotient (actualLegendreJacobi p) (properLegendreJacobi p)
    (actualVariationField p (by omega)) h2
  change actualLegendreJacobi p * actualCDiv p hp =
    2 * actualC p hp - properLegendreJacobi p * actualVariationField p (by omega) at hD
  refine ⟨hD, ?_⟩
  have hd : 1 ≤ p / 6 := by omega
  have hYne : actualLegendreJacobi p ≠ 0 := by
    intro hz
    have he := congrArg (fun Q : (ZMod p)[X] => Q.eval 1) hz
    rw [actualLegendreJacobi_endpoint_one] at he
    simp at he
  have hn := properLegendreJacobi_degree p (by omega : 7 ≤ p)
  have hna : (properLegendreJacobi p * actualVariationField p (by omega)).natDegree ≤
      2 * (p / 6) - 1 :=
    (natDegree_mul_le_of_le (show _ ≤ p / 6 - 1 by omega)
      (actualVariationField_degree p (by omega))).trans (by omega)
  have hnum : (2 * actualC p hp -
      properLegendreJacobi p * actualVariationField p (by omega)).natDegree ≤
      2 * (p / 6) - 1 := by
    exact (natDegree_sub_le_of_le
      ((natDegree_C_mul_le _ _).trans (actual_C_source_degree p hp).1) hna).trans (by omega)
  by_cases hz : actualCDiv p hp = 0
  · simp [hz]
  · rw [← hD, natDegree_mul hYne hz, actual_legendre_exact_degree p hp] at hnum
    omega

noncomputable def scaledNextSource {K : Type*} [CommRing K]
    (d : ℕ) (u t v Y n A R : K[X]) : K[X] :=
  -(2 * X * A.derivative + A) - 6 * Y - 10 * X * R.derivative +
    2 * C ((d : K) - 2) * R + 6 * t * Y +
    12 * (1 - X ^ 2) * t * n.derivative -
    6 * (1 - X ^ 2) * v * n - 12 * u * n

theorem hermite_product_green {K : Type*} [CommRing K]
    (d : ℕ) (Y R A : K[X]) :
    Y * (hermiteOperator Y (R * A)).derivative -
        Y.derivative * hermiteOperator Y (R * A) =
      Y ^ 2 * (R * legendreJacobi d A + A * legendreJacobi d R) -
        2 * Y * R * A * legendreJacobi d Y +
        2 * (1 - X ^ 2) * (Y * R.derivative - Y.derivative * R) *
          (Y * A.derivative - Y.derivative * A) := by
  simp only [hermiteOperator, legendreJacobi, derivative_mul, derivative_sub,
    derivative_one, derivative_X, derivative_pow_succ, derivative_add, derivative_ofNat]
  norm_num1
  simp only [_root_.map_ofNat]
  ring

theorem hermite_square_lift {K : Type*} [CommRing K]
    (d : ℕ) (Y Z : K[X]) :
    Y * (hermiteOperator Y (Y * Z)).derivative -
        Y.derivative * hermiteOperator Y (Y * Z) =
      Y ^ 3 * legendreJacobi d Z - Y ^ 2 * Z * legendreJacobi d Y := by
  simp only [hermiteOperator, legendreJacobi, derivative_mul, derivative_sub,
    derivative_one, derivative_X, derivative_pow_succ, derivative_add, derivative_ofNat]
  norm_num1
  simp only [_root_.map_ofNat]
  ring

-- The upper derivative-invisible u=X^p slot is explicit throughout.
theorem next_six_reconstruction_source {K : Type*} [Field K]
    (d : ℕ) (Y n A R B O L M Kc cc Z u t v : K[X]) (c h : K)
    (hYne : Y ≠ 0) (hY : legendreJacobi d Y = 0)
    (hnW : (1 - X ^ 2) * (Y * n.derivative - Y.derivative * n) = 1 - Y ^ 2)
    (hA : legendreJacobi d A = 2 * X * Y.derivative - 2 * C (d : K) * Y)
    (hR : legendreJacobi d R = 2 * X * Y.derivative + Y)
    (hRW : (1 - X ^ 2) * (Y * R.derivative - Y.derivative * R) = X * Y ^ 2 - u)
    (hRdef : R = Y * (L - C h) - u * n)
    (hC : hermiteOperator Y cc = X * n * Y ^ 2 + A + C h * Y ^ 3)
    (hM : (1 - X ^ 2) * M.derivative = n * Y - B)
    (hK : 6 * (1 - X ^ 2) * Kc.derivative =
      (6 * C c + 2 * C h) * u - 6 * O - 4 * X * (L - C h))
    (hG : (1 - X ^ 2) * (C c * u - B - O).derivative = t - Y ^ 2)
    (huD : u.derivative = 0) (htD : t.derivative = -v) (hu : u = X * t)
    (hP : Y * Z + R * A =
      6 * Y * n * (C c * u - B - O) - 2 * u * cc + 6 * Y ^ 2 * (M + Kc)) :
    legendreJacobi d Z = scaledNextSource d u t v Y n A R := by
  let q : K[X] := 1 - X ^ 2
  let G := C c * u - B - O
  let V := 6 * Y * G + 6 * q * t * Y ^ 2 * n - 2 * u * A -
    4 * X * Y ^ 2 * R - hermiteOperator Y (R * A)
  dsimp only [hermiteOperator] at hC
  have hQ : hermiteOperator Y
      (6 * Y * n * G - 2 * u * cc + 6 * Y ^ 2 * (M + Kc)) =
      6 * Y * G + 6 * q * t * Y ^ 2 * n - 2 * u * A - 4 * X * Y ^ 2 * R := by
    simp only [hermiteOperator, derivative_add, derivative_sub, derivative_mul,
      derivative_ofNat, derivative_pow_succ, huD, zero_mul,
      mul_zero, zero_add, add_zero]
    norm_num1
    simp only [_root_.map_ofNat]
    dsimp only [q, G] at ⊢
    linear_combination
      6 * Y * (C c * u - B - O) * hnW + 6 * Y ^ 2 * n * hG -
      2 * u * hC + 6 * Y ^ 3 * hM + Y ^ 3 * hK +
      4 * X * Y ^ 2 * hRdef - 6 * X * Y ^ 2 * n * hu
  have hpre : hermiteOperator Y (Y * Z) = V := by
    have he := congrArg (hermiteOperator Y) hP
    rw [hermiteOperator_add] at he
    change hermiteOperator Y (Y * Z) + hermiteOperator Y (R * A) = _ at he
    dsimp only [V]
    dsimp only [G] at hQ
    linear_combination he + hQ
  have hg := hermite_product_green d Y R A
  rw [hY, hA, hR, mul_zero, sub_zero] at hg
  have hV : q * (Y * V.derivative - Y.derivative * V) =
      q * Y ^ 3 * scaledNextSource d u t v Y n A R := by
    have hGexpanded := hG
    simp only [derivative_sub, derivative_C_mul, huD, mul_zero, zero_sub] at hGexpanded
    simp only [V, derivative_sub, derivative_add, derivative_mul, derivative_ofNat,
      derivative_X, huD, htD, zero_mul, mul_zero, zero_add, add_zero]
    dsimp only [q, G, scaledNextSource] at ⊢
    simp only [derivative_sub, derivative_one, derivative_pow_succ, derivative_X]
    norm_num1
    simp only [derivative_C_mul, huD, mul_zero, zero_sub,
      _root_.map_sub, _root_.map_ofNat]
    linear_combination
      -(1 - X ^ 2) * hg + 6 * Y ^ 2 * hGexpanded +
      (6 * X * Y ^ 2 - 2 * (1 - X ^ 2) *
        (Y * A.derivative - Y.derivative * A)) * hRW -
      6 * (1 - X ^ 2) * t * Y ^ 2 * hnW +
      (12 * (1 - X ^ 2) * Y ^ 3 * n - 6 * X * Y ^ 2) * hu
  have hV' : q * (Y * (hermiteOperator Y (Y * Z)).derivative -
      Y.derivative * hermiteOperator Y (Y * Z)) =
      q * Y ^ 3 * scaledNextSource d u t v Y n A R := by
    rw [hpre]
    exact hV
  have hlift := hermite_square_lift d Y Z
  rw [hY, mul_zero, sub_zero] at hlift
  have hz : q * Y ^ 3 *
      (legendreJacobi d Z - scaledNextSource d u t v Y n A R) = 0 := by
    linear_combination hV' - q * hlift
  have hq : q ≠ 0 := by
    intro he
    have hc := congrArg (fun P : K[X] => P.coeff 0) he
    simp [q] at hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero hq (pow_ne_zero 3 hYne)))

theorem OP_cleared_derivative (hp : 19 ≤ p) :
    (1 - X ^ 2 : (ZMod p)[X]) * (WPFiniteKSource.OP p).derivative =
      1 - X ^ (p - 1) := by
  let a : (ZMod p)[X] := C ((2 : ZMod p)⁻¹)
  have hpred : Even (p - 1) := by
    obtain ⟨j, hj⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    exact ⟨j, by omega⟩
  have hd : (WPFiniteKSource.OP p : (ZMod p)[X]).derivative =
      a * ((1 - X) ^ (p - 1) + (1 + X) ^ (p - 1) - 2 * X ^ (p - 1)) := by
    simp only [WPFiniteKSource.OP, derivative_C_mul, derivative_sub, derivative_comp,
      derivative_neg, derivative_X, WPFiniteAffineLog.LP_derivative_closed_eq]
    simp only [sub_comp, one_comp, X_comp, pow_comp, sub_neg_eq_add, hpred.neg_pow]
    dsimp only [a]
    ring
  have hminus : (1 - X ^ 2 : (ZMod p)[X]) * (1 - X) ^ (p - 1) =
      (1 + X) * (1 - X ^ p) := by
    calc
      _ = (1 + X : (ZMod p)[X]) * ((1 - X) * (1 - X) ^ (p - 1)) := by ring
      _ = _ := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
        congr 1
        simpa only [one_pow] using sub_pow_char (p := p) (1 : (ZMod p)[X]) X
  have hplus : (1 - X ^ 2 : (ZMod p)[X]) * (1 + X) ^ (p - 1) =
      (1 - X) * (1 + X ^ p) := by
    calc
      _ = (1 - X : (ZMod p)[X]) * ((1 + X) * (1 + X) ^ (p - 1)) := by ring
      _ = _ := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p),
          add_pow_char (p := p), one_pow]
  have ha : 2 * a = 1 := by
    have h2 : (2 : ZMod p) ≠ 0 :=
      WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
    change C (2 : ZMod p) * C ((2 : ZMod p)⁻¹) = 1
    rw [← C_mul, mul_inv_cancel₀ h2, C_1]
  have hxu : X * (X ^ p : (ZMod p)[X]) +
      (1 - X ^ 2) * X ^ (p - 1) = X ^ (p - 1) := by
    have hu : (X : (ZMod p)[X]) ^ p = X * X ^ (p - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
    rw [hu]
    ring
  rw [hd]
  linear_combination a * hminus + a * hplus +
    (1 - X ^ (p - 1)) * ha - 2 * a * hxu

noncomputable def actualLowConstant : ZMod p :=
  (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) - fieldHarmonic p (p / 6)

noncomputable def actualSixS (hp : 19 ≤ p) : (ZMod p)[X] :=
  X ^ p * (6 * C (actualLowConstant p) * properLegendreJacobi p - actualCDiv p hp) +
    6 * actualLegendreJacobi p * (actualM p +
      WPFiniteKSource.KsrcP p (fieldHarmonic p (p / 6))) -
    6 * properLegendreJacobi p * (adjacentPrimitive p (p / 6) + WPFiniteKSource.OP p) -
    actualVariationField p (by omega) *
      (WPFiniteKSource.LPsrc p - C (fieldHarmonic p (p / 6)))

private theorem actual_K_source_six (hp : 19 ≤ p) :
    6 * (1 - X ^ 2 : (ZMod p)[X]) *
        (WPFiniteKSource.KsrcP p (fieldHarmonic p (p / 6))).derivative =
      (6 * C (actualLowConstant p) + 2 * C (fieldHarmonic p (p / 6))) * X ^ p -
        6 * WPFiniteKSource.OP p - 4 * X *
          (WPFiniteKSource.LPsrc p - C (fieldHarmonic p (p / 6))) := by
  let h := fieldHarmonic p (p / 6)
  let q2 : ZMod p := WPFiniteNC122.q p
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have hc : (6 : ZMod p) * (q2 - 2 * h / 3) = 6 * (q2 - h) + 2 * h := by
    field_simp [h3]; ring
  have h23 : (6 : ZMod p) * (2 / 3) = 4 := by
    field_simp [h3]; norm_num
  have he := WPFiniteKSource.KsrcP_cleared_derivative (K := ZMod p) p hp h
  calc
    _ = 6 * (C (q2 - 2 * h / 3) * X ^ p - WPFiniteKSource.OP p -
        C (2 / 3 : ZMod p) * X * (WPFiniteKSource.LPsrc p - C h)) := by
      linear_combination 6 * he
    _ = C (6 * (q2 - 2 * h / 3)) * X ^ p - 6 * WPFiniteKSource.OP p -
        C ((6 : ZMod p) * (2 / 3)) * X * (WPFiniteKSource.LPsrc p - C h) := by
      simp only [_root_.map_mul, _root_.map_ofNat]; ring
    _ = _ := by
      rw [hc, h23]
      simp only [_root_.map_add, _root_.map_mul, _root_.map_ofNat]
      rfl

private theorem actual_scaled_source (hp : 19 ≤ p) :
    scaledNextSource (p / 6) (X ^ p) (X ^ (p - 1)) (X ^ (p - 2))
      (actualLegendreJacobi p) (properLegendreJacobi p)
      (actualVariationField p (by omega)) (actualRankDividedField p (by omega)) =
      6 * actualCarryFieldSource p (by omega) := by
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 6 (by omega) (by omega)
  have hu6 : (6 : (ZMod p)[X]) * C (1 / 6 : ZMod p) = 1 := by
    rw [show (6 : (ZMod p)[X]) = C (6 : ZMod p) by rfl, ← C_mul]
    simp [h6]
  have hu53 : (6 : (ZMod p)[X]) * C (5 / 3 : ZMod p) = 10 := by
    change (6 : (ZMod p)[X]) * C (5 / 3 : ZMod p) = C (10 : ZMod p)
    rw [show (6 : (ZMod p)[X]) = C (6 : ZMod p) by rfl, ← C_mul]
    congr 1
    field_simp [h3]; ring
  have hud : (6 : (ZMod p)[X]) * C ((((p / 6 : ℕ) : ZMod p) - 2) / 3) =
      2 * C (((p / 6 : ℕ) : ZMod p) - 2) := by
    simp only [show (6 : (ZMod p)[X]) = C (6 : ZMod p) by rfl,
      show (2 : (ZMod p)[X]) = C (2 : ZMod p) by rfl, ← C_mul]
    congr 1
    field_simp [h3]; ring
  dsimp only [scaledNextSource, actualCarryFieldSource]
  linear_combination
    (2 * X * (actualVariationField p (by omega)).derivative +
      actualVariationField p (by omega)) * hu6 +
    X * (actualRankDividedField p (by omega)).derivative * hu53 -
    actualRankDividedField p (by omega) * hud

theorem actual_SixS_source (hp : 19 ≤ p) :
    legendreJacobi (p / 6) (actualSixS p hp) =
      6 * actualCarryFieldSource p (by omega) := by
  let Y := actualLegendreJacobi p
  let n := properLegendreJacobi p
  let A := actualVariationField p (by omega : 7 ≤ p)
  let R := actualRankDividedField p (by omega : 7 ≤ p)
  let B := adjacentPrimitive p (p / 6)
  let O : (ZMod p)[X] := WPFiniteKSource.OP p
  let L : (ZMod p)[X] := WPFiniteKSource.LPsrc p
  let Kc : (ZMod p)[X] := WPFiniteKSource.KsrcP p (fieldHarmonic p (p / 6))
  let c := actualLowConstant p
  let h := fieldHarmonic p (p / 6)
  let u : (ZMod p)[X] := X ^ p
  let t : (ZMod p)[X] := X ^ (p - 1)
  let v : (ZMod p)[X] := X ^ (p - 2)
  have hYne : Y ≠ 0 := by
    intro hz
    have he := congrArg (fun Q : (ZMod p)[X] => Q.eval 1) hz
    rw [actualLegendreJacobi_endpoint_one] at he
    simp at he
  have hY : legendreJacobi (p / 6) Y = 0 := actualLegendreJacobi_source_zero p (by omega)
  have hA : legendreJacobi (p / 6) A =
      2 * X * Y.derivative - 2 * C ((p / 6 : ℕ) : ZMod p) * Y := by
    linear_combination actualVariationField_ODE p (by omega : 7 ≤ p)
  have hR : legendreJacobi (p / 6) R = 2 * X * Y.derivative + Y :=
    actualRankDividedField_source p (by omega)
  have hRdef : R = Y * (L - C h) - u * n := by
    dsimp only [R]
    rw [WPActualRankTwoComparison.actual_rankDividedField_eq_hat p hp]
    dsimp only [rankHatField, Y, L, h, u, n, WPFiniteKSource.LPsrc,
      WPFiniteKSource.EP, evenLogPolynomial, WPFiniteNC122.q]
    simp only [_root_.map_sub]
    ring
  have huD : u.derivative = 0 := by dsimp only [u]; simp [derivative_X_pow]
  have htD : t.derivative = -v := by
    dsimp only [t, v]
    rw [derivative_X_pow, show p - 1 - 1 = p - 2 by omega]
    simp only [Nat.cast_sub (by omega : 1 ≤ p), ZMod.natCast_self,
      Nat.cast_one, zero_sub, _root_.map_neg, _root_.map_one, neg_one_mul]
  have hu : u = X * t := by
    dsimp only [u, t]
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hG : (1 - X ^ 2) * (C c * u - B - O).derivative = t - Y ^ 2 := by
    simp only [derivative_sub, derivative_C_mul, huD, mul_zero, zero_sub]
    linear_combination -(actual_adjacent_primitive_data p hp).1 - OP_cleared_derivative p hp
  have hP : Y * actualSixS p hp + R * A =
      6 * Y * n * (C c * u - B - O) - 2 * u * actualC p hp +
        6 * Y ^ 2 * (actualM p + Kc) := by
    dsimp only [actualSixS]
    linear_combination -u * (actual_C_division_degree p hp).1 + A * hRdef
  have hs := next_six_reconstruction_source (p / 6) Y n A R B O L
    (actualM p) Kc (actualC p hp) (actualSixS p hp) u t v c h hYne hY
    (properLegendreJacobi_wronskian p (by omega)) hA hR
    (WPFieldAssembly.NativeFullGreen.actual_first_rank_wronskian p hp) hRdef
    (actual_C_source_degree p hp).2 (actual_M_source_degree p hp).1
    (actual_K_source_six p hp) hG huD htD hu hP
  exact hs.trans (actual_scaled_source p hp)

private theorem actual_OP_degree :
    (WPFiniteKSource.OP p : (ZMod p)[X]).natDegree ≤ p - 1 := by
  have hc : ((WPFiniteAffineLog.LP p : (ZMod p)[X]).comp (-X)).natDegree ≤ p - 1 :=
    natDegree_comp_le.trans
      ((Nat.mul_le_mul (WPFiniteAffineLog.LP_natDegree_le p)
        (show (-X : (ZMod p)[X]).natDegree ≤ 1 by simp)).trans (by simp))
  exact (natDegree_C_mul_le _ _).trans
    ((natDegree_sub_le_of_le (WPFiniteAffineLog.LP_natDegree_le p) hc).trans (by omega))

private theorem actual_LPsrc_degree :
    (WPFiniteKSource.LPsrc p : (ZMod p)[X]).natDegree ≤ p - 1 := by
  change (C (WPFiniteNC122.q p : ZMod p) + evenLogPolynomial p).natDegree ≤ p - 1
  exact (natDegree_add_le_of_le (show (C _ : (ZMod p)[X]).natDegree ≤ p - 1 by simp)
    (evenLogPolynomial_degree p)).trans (by omega)

theorem actual_SixS_degree (hp : 19 ≤ p) :
    (actualSixS p hp).natDegree ≤ p + p / 6 - 1 := by
  let d := p / 6
  let D := p + d - 1
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hn : (properLegendreJacobi p).natDegree ≤ d - 1 := by
    have h := properLegendreJacobi_degree p (by omega : 7 ≤ p)
    dsimp [d]; omega
  have hCD : (actualCDiv p hp).natDegree ≤ d - 1 := (actual_C_division_degree p hp).2
  have htop : (X ^ p *
      (6 * C (actualLowConstant p) * properLegendreJacobi p - actualCDiv p hp)).natDegree ≤ D := by
    have hl : (6 * C (actualLowConstant p) * properLegendreJacobi p).natDegree ≤ d - 1 := by
      rw [mul_assoc]
      exact (natDegree_C_mul_le _ _).trans ((natDegree_C_mul_le _ _).trans hn)
    have hnum : (6 * C (actualLowConstant p) * properLegendreJacobi p -
        actualCDiv p hp).natDegree ≤ d - 1 := by
      simpa only [max_self] using natDegree_sub_le_of_le hl hCD
    exact (natDegree_mul_le_of_le (show (X ^ p : (ZMod p)[X]).natDegree ≤ p by simp)
      hnum).trans (by dsimp [D]; omega)
  have hmk : (actualM p + WPFiniteKSource.KsrcP p (fieldHarmonic p (p / 6))).natDegree ≤
      p - 1 := by
    have hm := (actual_M_source_degree p hp).2.1
    have hdiv := Nat.div_mul_le_self p 6
    have hmle : (actualM p).natDegree ≤ p - 1 := hm.trans (by omega)
    simpa only [max_self] using natDegree_add_le_of_le hmle
      (WPFiniteKSource.KsrcP_natDegree_le p _)
  have hmiddle : (6 * actualLegendreJacobi p *
      (actualM p + WPFiniteKSource.KsrcP p (fieldHarmonic p (p / 6)))).natDegree ≤ D := by
    rw [mul_assoc]
    exact (natDegree_C_mul_le _ _).trans
      ((natDegree_mul_le_of_le (actualLegendreJacobi_degree p) hmk).trans (by dsimp [D,d]; omega))
  have hbo : (adjacentPrimitive p (p / 6) + WPFiniteKSource.OP p).natDegree ≤ p - 1 := by
    have hdiv := Nat.div_mul_le_self p 6
    have hbdeg : (adjacentPrimitive p (p / 6)).natDegree ≤ p - 1 :=
      (adjacentPrimitive_degree p (p / 6)).trans (by omega)
    simpa only [max_self] using natDegree_add_le_of_le hbdeg (actual_OP_degree p)
  have hproper : (6 * properLegendreJacobi p *
      (adjacentPrimitive p (p / 6) + WPFiniteKSource.OP p)).natDegree ≤ D := by
    rw [mul_assoc]
    exact (natDegree_C_mul_le _ _).trans
      ((natDegree_mul_le_of_le hn hbo).trans (by dsimp [D]; omega))
  have hl : (WPFiniteKSource.LPsrc p - C (fieldHarmonic p (p / 6))).natDegree ≤ p - 1 :=
    (natDegree_sub_le_of_le (actual_LPsrc_degree p)
      (show (C _ : (ZMod p)[X]).natDegree ≤ p - 1 by simp)).trans (by omega)
  have hlast : (actualVariationField p (by omega) *
      (WPFiniteKSource.LPsrc p - C (fieldHarmonic p (p / 6)))).natDegree ≤ D :=
    (natDegree_mul_le_of_le (actualVariationField_degree p (by omega)) hl).trans (by dsimp [D,d]; omega)
  have hsum : (X ^ p *
      (6 * C (actualLowConstant p) * properLegendreJacobi p - actualCDiv p hp) +
      6 * actualLegendreJacobi p *
        (actualM p + WPFiniteKSource.KsrcP p (fieldHarmonic p (p / 6)))).natDegree ≤ D := by
    simpa only [max_self] using natDegree_add_le_of_le htop hmiddle
  have hsub : (X ^ p *
      (6 * C (actualLowConstant p) * properLegendreJacobi p - actualCDiv p hp) +
      6 * actualLegendreJacobi p *
        (actualM p + WPFiniteKSource.KsrcP p (fieldHarmonic p (p / 6))) -
      6 * properLegendreJacobi p *
        (adjacentPrimitive p (p / 6) + WPFiniteKSource.OP p)).natDegree ≤ D := by
    simpa only [max_self] using natDegree_sub_le_of_le hsum hproper
  change (actualSixS p hp).natDegree ≤ D
  simpa only [actualSixS, max_self] using natDegree_sub_le_of_le hsub hlast

private theorem actual_OP_endpoint (hp : 19 ≤ p) :
    (WPFiniteKSource.OP p : (ZMod p)[X]).eval 1 =
      (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
  have hu : (2 : (ZMod p)[X]) * C ((2 : ZMod p)⁻¹) = 1 := by
    have h2 : (2 : ZMod p) ≠ 0 :=
      WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
    change C (2 : ZMod p) * C ((2 : ZMod p)⁻¹) = 1
    rw [← C_mul, mul_inv_cancel₀ h2, C_1]
  have he : WPFiniteKSource.OP p + evenLogPolynomial p =
      (WPFiniteAffineLog.LP p : (ZMod p)[X]) := by
    dsimp only [WPFiniteKSource.OP, evenLogPolynomial]
    linear_combination WPFiniteAffineLog.LP p * hu
  have he1 := congrArg (fun Q : (ZMod p)[X] => Q.eval 1) he
  rw [eval_add, evenLogPolynomial_endpoint_one p hp,
    WPFiniteAffineLog.LP_eval_eq] at he1
  have hLP : WPFiniteField.ell p (1 : ZMod p) = 0 :=
    WPFiniteInversion.ell_one_eq_zero p (by omega)
  rw [hLP] at he1
  linear_combination he1

theorem actual_SixS_endpoint (hp : 19 ≤ p) :
    (actualSixS p hp).eval 1 = -2 * (actualC p hp).eval 1 + 6 * (actualM p).eval 1 := by
  have hCD := congrArg (fun Q : (ZMod p)[X] => Q.eval 1)
    (actual_C_division_degree p hp).1
  simp only [eval_mul, eval_sub, eval_ofNat, actualLegendreJacobi_endpoint_one,
    actualVariationField_endpoint_one, one_mul, mul_zero, sub_zero] at hCD
  have hL1 : (WPFiniteKSource.LPsrc p : (ZMod p)[X]).eval 1 = 0 := by
    change (C (WPFiniteNC122.q p : ZMod p) + evenLogPolynomial p).eval 1 = 0
    rw [eval_add, eval_C, evenLogPolynomial_endpoint_one p hp]
    dsimp only [WPFiniteNC122.q]
    ring
  have hK1 := (WPFiniteKSource.KsrcP_normalized_ends (K := ZMod p) p hp
    (fieldHarmonic p (p / 6))).1
  simp only [actualSixS, eval_add, eval_sub, eval_mul, eval_ofNat, eval_C,
    eval_pow, eval_X, one_pow, one_mul, hCD, hL1, hK1,
    actualLegendreJacobi_endpoint_one, actualVariationField_endpoint_one,
    properLegendreJacobi_endpoint_one, adjacentPrimitive_one,
    actual_OP_endpoint p hp, zero_mul, sub_zero, add_zero]
  dsimp only [actualLowConstant]
  ring

noncomputable def actualKappa (hp : 19 ≤ p) : ZMod p :=
  -residueHom p (endpointCarryIntegral p hp) +
    (actualC p hp).eval 1 / 3 - (actualM p).eval 1

noncomputable def actualPSrc (hp : 19 ≤ p) : (ZMod p)[X] :=
  C (1 / 6 : ZMod p) * (actualLegendreJacobi p * actualSixS p hp)

theorem actual_next_S_reconstruction (hp : 19 ≤ p) :
    actualSecondCarryField p hp =
      C (1 / 6 : ZMod p) * actualSixS p hp + C (actualKappa p hp) * actualLegendreJacobi p := by
  let Y := actualLegendreJacobi p
  let Z := C (1 / 6 : ZMod p) * actualSixS p hp + C (actualKappa p hp) * Y
  let D := actualSecondCarryField p hp - Z
  have h6 : (6 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 6 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have hu6 : (C (1 / 6 : ZMod p) : (ZMod p)[X]) * 6 = 1 := by
    change C (1 / 6 : ZMod p) * C (6 : ZMod p) = 1
    rw [← C_mul]
    simp [h6]
  have hZsource : legendreJacobi (p / 6) Z = actualCarryFieldSource p (by omega) := by
    dsimp only [Z, Y]
    rw [legendreJacobi_add, legendreJacobi_C_mul, legendreJacobi_C_mul,
      actual_SixS_source p hp, actualLegendreJacobi_source_zero p (by omega),
      mul_zero, add_zero]
    linear_combination actualCarryFieldSource p (by omega) * hu6
  have hZ1 : Z.eval 1 = -residueHom p (endpointCarryIntegral p hp) := by
    simp only [Z, Y, eval_add, eval_mul, eval_C, actualLegendreJacobi_endpoint_one,
      mul_one, actual_SixS_endpoint p hp]
    dsimp only [actualKappa]
    field_simp [h3, h6]
    ring
  have hZdegree : Z.natDegree ≤ p + p / 6 - 1 := by
    have hyl : (C (actualKappa p hp) * Y).natDegree ≤ p + p / 6 - 1 :=
      (natDegree_C_mul_le _ _).trans ((actualLegendreJacobi_degree p).trans (by omega))
    exact (natDegree_add_le_of_le
      ((natDegree_C_mul_le _ _).trans (actual_SixS_degree p hp))
      hyl).trans (by omega)
  have hDdegree : D.natDegree ≤ p + p / 6 - 1 :=
    (natDegree_sub_le_of_le (actualSecondCarryField_degree p hp) hZdegree).trans (by omega)
  have hDsource : legendreJacobi (p / 6) D = 0 := by
    dsimp only [D]
    rw [legendreJacobi_sub, actualSecondCarryField_source p hp, hZsource, sub_self]
  have hDlow := WPActualRankTwoFiniteLegendre.forced_legendre_degree_bound p (by omega : 7 ≤ p)
    D hDdegree (by rw [hDsource]; simp)
  have hD1 : D.eval 1 = 0 := by
    dsimp only [D]
    rw [eval_sub, actual_next_endpoint p hp, hZ1, sub_self]
  have hz := WPActualRankTwoFiniteLegendre.legendre_jacobi_kernel_zero p (p / 6)
    (by omega : 7 ≤ p) D (hDlow.trans_lt (by omega)) hD1 hDsource
  exact sub_eq_zero.mp hz

theorem actual_next_PSrc_reconstruction (hp : 19 ≤ p) :
    actualLegendreJacobi p * actualSecondCarryField p hp =
      actualPSrc p hp + C (actualKappa p hp) * actualLegendreJacobi p ^ 2 := by
  rw [actual_next_S_reconstruction p hp]
  dsimp only [actualPSrc]
  ring

theorem actual_variation_reflect (hp : 19 ≤ p) :
    (actualVariationField p (by omega)).comp (-X) =
      C ((-1 : ZMod p) ^ (p / 6)) * actualVariationField p (by omega) := by
  let d := p / 6
  let Y := actualLegendreJacobi p
  let A := actualVariationField p (by omega : 7 ≤ p)
  let s : ZMod p := (-1) ^ d
  let D := A.comp (-X) - C s * A
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hAdeg : A.natDegree ≤ d := actualVariationField_degree p (by omega)
  have hY : Y.comp (-X) = C s * Y := legendreField_reflect p d (by omega)
  have hDY : Y.derivative.comp (-X) = -C s * Y.derivative := by
    have he := congrArg Polynomial.derivative hY
    simp only [derivative_comp, derivative_neg, derivative_X, derivative_C_mul] at he
    linear_combination -he
  have hAode : legendreJacobi d A = 2 * X * Y.derivative - 2 * C (d : ZMod p) * Y := by
    linear_combination actualVariationField_ODE p (by omega : 7 ≤ p)
  have hDdeg : D.natDegree < d := by
    have hcomp : (A.comp (-X)).natDegree ≤ d := by
      exact natDegree_comp_le.trans
        ((Nat.mul_le_mul hAdeg (show (-X : (ZMod p)[X]).natDegree ≤ 1 by simp)).trans
          (by simp))
    have hb : D.natDegree ≤ d := by
      simpa only [max_self] using natDegree_sub_le_of_le hcomp
        ((natDegree_C_mul_le _ _).trans hAdeg : (C s * A).natDegree ≤ d)
    have ht : D.coeff d = 0 := by
      simp only [D, coeff_sub, coeff_comp_neg, coeff_C_mul]
      dsimp only [s]
      ring
    by_cases hz : D = 0
    · simp [hz]; omega
    · by_contra hn
      have he : D.natDegree = d := by omega
      have htop := leadingCoeff_ne_zero.mpr hz
      exact htop (by simpa only [← coeff_natDegree, he] using ht)
  have hDs : legendreJacobi d D = 0 := by
    dsimp only [D]
    rw [legendreJacobi_sub, legendreJacobi_reflect, legendreJacobi_C_mul, hAode]
    simp only [sub_comp, mul_comp, ofNat_comp, C_comp, X_comp, hY, hDY]
    ring
  have hz := actual_small_legendre_kernel p hp D hDdeg hDs
  exact sub_eq_zero.mp hz

theorem actual_next_source_reflect (hp : 19 ≤ p) :
    (actualCarryFieldSource p (by omega)).comp (-X) =
      C ((-1 : ZMod p) ^ (p / 6)) * actualCarryFieldSource p (by omega) := by
  let Y := actualLegendreJacobi p
  let A := actualVariationField p (by omega : 7 ≤ p)
  let R := actualRankDividedField p (by omega : 7 ≤ p)
  let n := properLegendreJacobi p
  let s : ZMod p := (-1) ^ (p / 6)
  have hY : Y.comp (-X) = C s * Y := legendreField_reflect p (p / 6) (by omega)
  have hA : A.comp (-X) = C s * A := actual_variation_reflect p hp
  have hR : R.comp (-X) = C s * R := actual_rank_divided_reflect p hp
  have hn : n.comp (-X) = -C s * n := actual_proper_legendre_reflect p hp
  have hDA : A.derivative.comp (-X) = -C s * A.derivative := by
    have he := congrArg Polynomial.derivative hA
    simp only [derivative_comp, derivative_neg, derivative_X, derivative_C_mul] at he
    linear_combination -he
  have hDR : R.derivative.comp (-X) = -C s * R.derivative := by
    have he := congrArg Polynomial.derivative hR
    simp only [derivative_comp, derivative_neg, derivative_X, derivative_C_mul] at he
    linear_combination -he
  have hDn : n.derivative.comp (-X) = C s * n.derivative := by
    have he := congrArg Polynomial.derivative hn
    simp only [derivative_comp, derivative_neg, derivative_X, derivative_mul,
      derivative_C] at he
    linear_combination -he
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hpred : Even (p - 1) := by
    obtain ⟨j, hj⟩ := hpodd
    exact ⟨j, by omega⟩
  have hp2 : Odd (p - 2) := by
    obtain ⟨j, hj⟩ := hpodd
    exact ⟨j - 1, by omega⟩
  dsimp only [actualCarryFieldSource]
  dsimp only [Y, A, R, n, s] at hY hA hR hn hDA hDR hDn
  simp only [add_comp, sub_comp, mul_comp, C_comp, ofNat_comp,
    neg_comp, pow_comp, one_comp, X_comp, neg_sq, hY, hA, hR, hn, hDA, hDR, hDn,
    hpodd.neg_pow, hpred.neg_pow, hp2.neg_pow]
  ring

-- This covers the original full S window, including its upper p-slots.
theorem actual_high_homogeneous_scalar (hp : 19 ≤ p) (P : (ZMod p)[X])
    (hdeg : P.natDegree ≤ p + p / 6 - 1)
    (hsource : legendreJacobi (p / 6) P = 0) :
    P = C (P.eval 1) * actualLegendreJacobi p := by
  have hlow := WPActualRankTwoFiniteLegendre.forced_legendre_degree_bound p (by omega : 7 ≤ p)
    P hdeg (by rw [hsource]; simp)
  let D := P - C (P.eval 1) * actualLegendreJacobi p
  have hydeg : (C (P.eval 1) * actualLegendreJacobi p).natDegree ≤ p - 1 - p / 6 :=
    (natDegree_C_mul_le _ _).trans ((actualLegendreJacobi_degree p).trans (by omega))
  have hDdeg : D.natDegree < p :=
    (natDegree_sub_le_of_le hlow hydeg).trans_lt (by omega)
  have hD1 : D.eval 1 = 0 := by
    simp [D, actualLegendreJacobi_endpoint_one]
  have hDs : legendreJacobi (p / 6) D = 0 := by
    dsimp only [D]
    rw [legendreJacobi_sub, legendreJacobi_C_mul, hsource,
      actualLegendreJacobi_source_zero p (by omega), mul_zero, sub_self]
  have hz := WPActualRankTwoFiniteLegendre.legendre_jacobi_kernel_zero p (p / 6)
    (by omega : 7 ≤ p) D hDdeg hD1 hDs
  exact sub_eq_zero.mp hz

theorem actual_next_S_reflect (hp : 19 ≤ p) :
    (actualSecondCarryField p hp).comp (-X) =
      C ((-1 : ZMod p) ^ (p / 6)) * actualSecondCarryField p hp := by
  let Y := actualLegendreJacobi p
  let S := actualSecondCarryField p hp
  let s : ZMod p := (-1) ^ (p / 6)
  let D := S.comp (-X) - C s * S
  have hs : (C s : (ZMod p)[X]) ^ 2 = 1 := by
    rw [← C_pow, WPActualGaussProper.negative_power_square, C_1]
  have hsn : (C s : (ZMod p)[X]) ≠ 0 := by
    apply C_ne_zero.mpr
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hY : Y.comp (-X) = C s * Y := legendreField_reflect p (p / 6) (by omega)
  have hcomp : (S.comp (-X)).natDegree ≤ p + p / 6 - 1 :=
    natDegree_comp_le.trans
      ((Nat.mul_le_mul (actualSecondCarryField_degree p hp)
        (show (-X : (ZMod p)[X]).natDegree ≤ 1 by simp)).trans (by simp))
  have hCdeg : (C s * S).natDegree ≤ p + p / 6 - 1 :=
    (natDegree_C_mul_le _ _).trans (actualSecondCarryField_degree p hp)
  have hDdegree : D.natDegree ≤ p + p / 6 - 1 := by
    simpa only [max_self] using natDegree_sub_le_of_le hcomp hCdeg
  have hDsource : legendreJacobi (p / 6) D = 0 := by
    dsimp only [D, S, s]
    rw [legendreJacobi_sub, legendreJacobi_reflect, legendreJacobi_C_mul,
      actualSecondCarryField_source p hp, actual_next_source_reflect p hp, sub_self]
  have hf := actual_high_homogeneous_scalar p hp D hDdegree hDsource
  have hDplus : D.comp (-X) = C s * D := by
    rw [hf]
    simp only [mul_comp, C_comp]
    change C (D.eval 1) * Y.comp (-X) = _
    rw [hY]
    ring
  have hDminus : D.comp (-X) = -C s * D := by
    simp only [D, sub_comp, mul_comp, C_comp, comp_assoc]
    have hi : (-X : (ZMod p)[X]).comp (-X) = X := by simp
    rw [hi, comp_X]
    linear_combination -S * hs
  have hz : (2 * C s : (ZMod p)[X]) * D = 0 := by
    linear_combination hDminus - hDplus
  have h2n : (2 : (ZMod p)[X]) ≠ 0 :=
    C_ne_zero.mpr (WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega))
  have hDz : D = 0 := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero h2n hsn)
  exact sub_eq_zero.mp hDz

theorem actual_PSrc_even (hp : 19 ≤ p) :
    (actualPSrc p hp).comp (-X) = actualPSrc p hp := by
  let Y := actualLegendreJacobi p
  let S := actualSecondCarryField p hp
  let s : ZMod p := (-1) ^ (p / 6)
  have hs : (C s : (ZMod p)[X]) ^ 2 = 1 := by
    rw [← C_pow, WPActualGaussProper.negative_power_square, C_1]
  have hY : Y.comp (-X) = C s * Y := legendreField_reflect p (p / 6) (by omega)
  have hS : S.comp (-X) = C s * S := actual_next_S_reflect p hp
  have hYS : (Y * S).comp (-X) = Y * S := by
    rw [mul_comp, hY, hS]
    linear_combination (Y * S) * hs
  have hY2 : (Y ^ 2).comp (-X) = Y ^ 2 := by
    rw [pow_comp, hY, mul_pow, hs, one_mul]
  have hr := actual_next_PSrc_reconstruction p hp
  have hc := congrArg (fun Q : (ZMod p)[X] => Q.comp (-X)) hr
  rw [hYS, add_comp, mul_comp, C_comp, hY2] at hc
  linear_combination hr - hc

theorem actual_PSrc_degree (hp : 19 ≤ p) :
    (actualPSrc p hp).natDegree ≤ p + 2 * (p / 6) - 1 := by
  exact (natDegree_C_mul_le _ _).trans
    ((natDegree_mul_le_of_le (actualLegendreJacobi_degree p)
      (actual_SixS_degree p hp)).trans (by omega))

theorem actual_PSrc_native_attachment (hp : 19 ≤ p) :
    (quadraticInverse (actualPSrc p hp)).comp (1 - X ^ 2) = actualPSrc p hp := by
  have he := even_expand_contract_two p hp (actualPSrc p hp) (actual_PSrc_even p hp)
  rw [expand_eq_comp_X_pow] at he
  rw [quadraticInverse, comp_assoc]
  convert he using 1; simp

theorem actual_PSrc_native_degree (hp : 19 ≤ p) :
    (quadraticInverse (actualPSrc p hp)).natDegree ≤ (p - 1) / 2 + p / 6 ∧
      (quadraticInverse (actualPSrc p hp)).natDegree < p := by
  have hhalf := WPFiniteWSource.half_exponent p hp
  have hdeg := actual_PSrc_degree p hp
  have hnat := NativeOriginalResidues.quadraticInverse_degree_of_le (actualPSrc p hp)
    ((p - 1) / 2 + p / 6) (by omega)
  have hdiv := Nat.div_mul_le_self p 6
  exact ⟨hnat, hnat.trans_lt (by omega)⟩

theorem actual_PSrc_projection (hp : 19 ≤ p) :
    QO p (actualLegendreJacobi p * actualSecondCarryField p hp) = QO p (actualPSrc p hp) := by
  have hYY : (actualLegendreJacobi p ^ 2).natDegree ≤ 2 * (p / 6) := by
    rw [natDegree_pow]
    have hy := actualLegendreJacobi_degree p
    omega
  have hzero : QO p (actualLegendreJacobi p ^ 2) = 0 := by
    unfold QO
    exact WPFieldAssembly.ResidualProjection.low_correction_both_projections_zero p hp _
      (NativeOriginalResidues.quadraticInverse_degree_of_le _ (p / 6) hYY) 0
  rw [actual_next_PSrc_reconstruction p hp, QO_add, QO_C_mul, hzero, mul_zero, add_zero]

theorem actual_deltaU_digit_low_next_source (hp : 19 ≤ p) :
    residueHom p (integralDeltaUDigit p hp) =
      residueHom p (hatDigitIntegral p hp) - QO p (actualPSrc p hp) / 3 +
        QO p (actualVariationField p (by omega) * actualRankDividedField p (by omega)) / 18 +
        QH p (actualLegendreJacobi p * actualVariationField p (by omega)) / 6 := by
  rw [actual_deltaU_digit_next_source p hp, actual_PSrc_projection p hp]

end WPFieldAssembly.ActualNextHermite
