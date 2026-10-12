import WPFieldAssembly.NativeStrictTail
import Mathlib.Algebra.Polynomial.FieldDivision

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPActualCMGauss WPActualGaussBottom
  WPActualGaussProper WPActualRankTwoGaussODE WPActualRankTwoLegendreField
  WPActualRankTwoProper WPActualRankTwoFiniteLegendre
  WPActualRankTwoFirstLift WPActualRankTwoLowTaylor
  WPActualRankTwoComparison WPActualRankTwoHatLift
  WPActualRankTwoResidueSource WPActualNativeSecondTaylor
  WPActualNativeCubicInvariant WPFieldAssembly.NativeFullGreen
  WPFieldAssembly.NativeSecondGreen WPFieldAssembly.NativeStrictTail
  WPFieldAssembly.ConicKernel

namespace WPFieldAssembly.NativeIR28

set_option maxHeartbeats 1800000

noncomputable def legendreField (p j : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  ((shiftedLegendre j).map (Int.castRingHom (ZMod p))).comp
    (C (1 / 2 : ZMod p) * (1 - X))

theorem legendreField_actual (p : ℕ) [Fact p.Prime] :
    legendreField p (p / 6) = actualLegendreJacobi p := rfl

theorem legendreField_degree (p j : ℕ) [Fact p.Prime] :
    (legendreField p j).natDegree ≤ j := by
  have ha : (C (1 / 2 : ZMod p) * (1 - X)).natDegree ≤ 1 := by
    compute_degree
  exact natDegree_comp_le.trans
    ((Nat.mul_le_mul (natDegree_map_le.trans (by rw [natDegree_shiftedLegendre]))
      ha).trans (by simp))

theorem legendreField_one (p j : ℕ) [Fact p.Prime] :
    (legendreField p j).eval 1 = 1 := by
  rw [legendreField, eval_comp]
  simp only [eval_mul, eval_C, eval_sub, eval_one, eval_X, sub_self, mul_zero]
  rw [← coeff_zero_eq_eval_zero, coeff_map, coeff_shiftedLegendre]
  simp

theorem legendreField_ODE (p j : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    legendreJacobi j (legendreField p j) = 0 := by
  rw [legendreField, ← legendre_coordinate j (1 / 2 : ZMod p)
    (field_half_identity p hp), ← legendreRegular_map,
    actual_integer_legendre_ODE, Polynomial.map_zero, zero_comp]

theorem legendreField_reflect (p j : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (legendreField p j).comp (-X) = C ((-1 : ZMod p) ^ j) * legendreField p j := by
  let a : (ZMod p)[X] := C (1 / 2 : ZMod p) * (1 - X)
  have hhalf : 2 * C (1 / 2 : ZMod p) = (1 : (ZMod p)[X]) := by
    simpa only [_root_.map_mul, _root_.map_ofNat, _root_.map_one] using
      congrArg (C : ZMod p → (ZMod p)[X]) (field_half_identity p hp)
  have ha : (1 - X : (ZMod p)[X]).comp a = a.comp (-X) := by
    simp only [sub_comp, one_comp, X_comp, a, mul_comp, C_comp,
      sub_comp, one_comp, X_comp]
    linear_combination -hhalf
  have h := congrArg (fun P : ℤ[X] => P.map (Int.castRingHom (ZMod p)))
    (neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq j)
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_one, Polynomial.map_comp, Polynomial.map_sub,
    Polynomial.map_X] at h
  have hc := congrArg (fun P : (ZMod p)[X] => P.comp a) h
  simp only [mul_comp, pow_comp, neg_comp, one_comp] at hc
  rw [comp_assoc, ha, ← comp_assoc] at hc
  have hsign : (-1 : (ZMod p)[X]) ^ j = C ((-1 : ZMod p) ^ j) := by
    simp
  rw [hsign] at hc
  change C ((-1 : ZMod p) ^ j) * (legendreField p j).comp (-X) =
    legendreField p j at hc
  have hs : C ((-1 : ZMod p) ^ j) * C ((-1 : ZMod p) ^ j) =
      (1 : (ZMod p)[X]) := by
    rw [← C_mul]
    have he : (-1 : ZMod p) ^ j * (-1 : ZMod p) ^ j = 1 := by
      simpa only [pow_two] using negative_power_square (K := ZMod p) j
    rw [he, C_1]
  have hh := congrArg (fun P : (ZMod p)[X] => C ((-1 : ZMod p) ^ j) * P) hc
  rwa [← mul_assoc, hs, one_mul] at hh

theorem lower_ladder_source {K : Type*} [CommRing K] (j : ℕ) (hj : 1 ≤ j)
    (P : K[X]) :
    legendreJacobi (j - 1) ((1 - X ^ 2) * P.derivative + C (j : K) * X * P) =
      (1 - X ^ 2) * (legendreJacobi j P).derivative +
        C ((j : K) - 2) * X * legendreJacobi j P := by
  simp only [legendreJacobi, derivative_mul, derivative_C,
    derivative_one, derivative_X, derivative_pow_succ,
    Nat.cast_sub hj, Nat.cast_one, _root_.map_mul, _root_.map_add,
    _root_.map_sub, _root_.map_ofNat, _root_.map_one]
  (simp; ring)

theorem raise_ladder_source {K : Type*} [CommRing K] (j : ℕ) (hj : 1 ≤ j)
    (P : K[X]) :
    legendreJacobi j ((1 - X ^ 2) * P.derivative - C (j : K) * X * P) =
      (1 - X ^ 2) * (legendreJacobi (j - 1) P).derivative -
        C ((j : K) + 2) * X * legendreJacobi (j - 1) P := by
  simp only [legendreJacobi, derivative_mul, derivative_C,
    derivative_one, derivative_X, derivative_pow_succ,
    Nat.cast_sub hj, Nat.cast_one, _root_.map_mul, _root_.map_add,
    _root_.map_sub, _root_.map_ofNat, _root_.map_one]
  (simp; ring)

theorem adjacent_lower (p j : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hj : 1 ≤ j) (hjd : j ≤ p / 6) :
    (1 - X ^ 2) * (legendreField p j).derivative +
      C (j : ZMod p) * X * legendreField p j =
      C (j : ZMod p) * legendreField p (j - 1) := by
  apply sub_eq_zero.mp
  apply legendre_jacobi_kernel_zero p (j - 1) (by omega)
  · have hP := legendreField_degree p j
    have hd := natDegree_derivative_le (legendreField p j)
    have hDP : (legendreField p j).derivative.natDegree ≤ j - 1 :=
      hd.trans (Nat.sub_le_sub_right hP 1)
    have hq : (1 - X ^ 2 : (ZMod p)[X]).natDegree ≤ 2 := by compute_degree
    have h1 : ((1 - X ^ 2) * (legendreField p j).derivative).natDegree ≤ j + 1 :=
      (natDegree_mul_le_of_le hq hDP).trans (by omega)
    have h2 : (C (j : ZMod p) * X * legendreField p j).natDegree ≤ j + 1 := by
      rw [mul_assoc]
      exact (natDegree_C_mul_le _ _).trans
        ((natDegree_mul_le_of_le natDegree_X_le hP).trans (by omega))
    have h3 : (C (j : ZMod p) * legendreField p (j - 1)).natDegree ≤ j + 1 :=
      (natDegree_C_mul_le (j : ZMod p) (legendreField p (j - 1))).trans
        ((legendreField_degree p (j - 1)).trans (by omega))
    exact (natDegree_sub_le_of_le
      (by simpa only [max_self] using natDegree_add_le_of_le h1 h2)
      h3).trans_lt (by omega)
  · simp only [eval_sub, eval_add, eval_mul, eval_one, eval_pow, eval_X,
      eval_C, one_pow, sub_self, zero_mul, mul_one, zero_add, legendreField_one]
  · rw [legendreJacobi_sub, lower_ladder_source j hj,
      legendreJacobi_C_mul, legendreField_ODE p j (by omega),
      legendreField_ODE p (j - 1) (by omega)]
    simp

theorem adjacent_raise (p j : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hj : 1 ≤ j) (hjd : j ≤ p / 6) :
    (1 - X ^ 2) * (legendreField p (j - 1)).derivative -
      C (j : ZMod p) * X * legendreField p (j - 1) =
      -C (j : ZMod p) * legendreField p j := by
  apply sub_eq_zero.mp
  rw [neg_mul, sub_neg_eq_add]
  apply legendre_jacobi_kernel_zero p j (by omega)
  · have hP := legendreField_degree p (j - 1)
    have hd := natDegree_derivative_le (legendreField p (j - 1))
    have hDP : (legendreField p (j - 1)).derivative.natDegree ≤ j - 1 :=
      hd.trans ((Nat.sub_le _ _).trans hP)
    have hq : (1 - X ^ 2 : (ZMod p)[X]).natDegree ≤ 2 := by compute_degree
    have h1 : ((1 - X ^ 2) * (legendreField p (j - 1)).derivative).natDegree ≤ j + 1 :=
      (natDegree_mul_le_of_le hq hDP).trans (by omega)
    have h2 : (C (j : ZMod p) * X * legendreField p (j - 1)).natDegree ≤ j + 1 :=
      by
        rw [mul_assoc]
        exact (natDegree_C_mul_le _ _).trans
          ((natDegree_mul_le_of_le natDegree_X_le hP).trans (by omega))
    have h3 : (C (j : ZMod p) * legendreField p j).natDegree ≤ j + 1 :=
      (natDegree_C_mul_le _ _).trans ((legendreField_degree p j).trans (by omega))
    exact (natDegree_add_le_of_le
      (by simpa only [max_self] using natDegree_sub_le_of_le h1 h2) h3).trans_lt
      (by omega)
  · simp only [eval_add, eval_sub, eval_mul, eval_one, eval_pow, eval_X,
      eval_C, one_pow, sub_self, zero_mul, mul_one, zero_sub, legendreField_one,
      neg_add_cancel]
  · rw [legendreJacobi_add, raise_ladder_source j hj,
      legendreJacobi_C_mul, legendreField_ODE p j (by omega),
      legendreField_ODE p (j - 1) (by omega)]
    simp

theorem adjacent_product_source (p j : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hj : 1 ≤ j) (hjd : j ≤ p / 6) :
    (1 - X ^ 2) * (legendreField p j * legendreField p (j - 1)).derivative =
      C (j : ZMod p) * (legendreField p (j - 1) ^ 2 - legendreField p j ^ 2) := by
  rw [derivative_mul]
  linear_combination
    legendreField p (j - 1) * adjacent_lower p j hp hj hjd +
      legendreField p j * adjacent_raise p j hp hj hjd

noncomputable def adjacentPrimitive (p m : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  -∑ j ∈ Finset.range m, C (((j + 1 : ℕ) : ZMod p)⁻¹) *
    legendreField p (j + 1) * legendreField p j

theorem adjacentPrimitive_succ (p m : ℕ) [Fact p.Prime] :
    adjacentPrimitive p (m + 1) = adjacentPrimitive p m -
      C (((m + 1 : ℕ) : ZMod p)⁻¹) * legendreField p (m + 1) * legendreField p m := by
  simp only [adjacentPrimitive, Finset.sum_range_succ]
  ring

theorem adjacentPrimitive_source (p m : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hm : m ≤ p / 6) :
    (1 - X ^ 2) * (adjacentPrimitive p m).derivative = legendreField p m ^ 2 - 1 := by
  induction m with
  | zero => simp [adjacentPrimitive, legendreField, shiftedLegendre]
  | succ m ih =>
    have hu : ((m + 1 : ℕ) : ZMod p) ≠ 0 :=
      small_cast_ne_zero p (m + 1) (by omega) (by omega)
    have hc : C (((m + 1 : ℕ) : ZMod p)⁻¹) * C ((m + 1 : ℕ) : ZMod p) =
        (1 : (ZMod p)[X]) := by
      rw [← C_mul, inv_mul_cancel₀ hu, C_1]
    have hs : (1 - X ^ 2) *
        (C (((m + 1 : ℕ) : ZMod p)⁻¹) * legendreField p (m + 1) *
          legendreField p m).derivative = legendreField p m ^ 2 - legendreField p (m + 1) ^ 2 := by
      rw [show C (((m + 1 : ℕ) : ZMod p)⁻¹) * legendreField p (m + 1) *
          legendreField p m = C (((m + 1 : ℕ) : ZMod p)⁻¹) *
          (legendreField p (m + 1) * legendreField p m) by ring,
        derivative_C_mul]
      calc
        _ = C (((m + 1 : ℕ) : ZMod p)⁻¹) *
          ((1 - X ^ 2) * (legendreField p (m + 1) * legendreField p m).derivative) := by ring
        _ = _ := by
          have hprod := adjacent_product_source p (m + 1) hp (by omega) hm
          rw [show m + 1 - 1 = m by omega] at hprod
          rw [hprod, ← mul_assoc, hc, one_mul]
    rw [adjacentPrimitive_succ, derivative_sub]
    linear_combination ih (by omega) - hs

theorem adjacentPrimitive_degree (p m : ℕ) [Fact p.Prime] :
    (adjacentPrimitive p m).natDegree ≤ 2 * m - 1 := by
  rw [adjacentPrimitive, natDegree_neg]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hjm := Finset.mem_range.mp hj
  rw [mul_assoc]
  exact (natDegree_C_mul_le _ _).trans
    ((natDegree_mul_le_of_le (legendreField_degree p (j + 1))
      (legendreField_degree p j)).trans (by omega))

theorem adjacentPrimitive_one (p m : ℕ) [Fact p.Prime] :
    (adjacentPrimitive p m).eval 1 = -fieldHarmonic p m := by
  simp only [adjacentPrimitive, fieldHarmonic, eval_neg, eval_finsetSum,
    eval_mul, eval_C, legendreField_one, mul_one, Nat.cast_add, Nat.cast_one]

theorem adjacentPrimitive_odd (p m : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (adjacentPrimitive p m).comp (-X) = -adjacentPrimitive p m := by
  have ht (j : ℕ) :
      (C (((j + 1 : ℕ) : ZMod p)⁻¹) * legendreField p (j + 1) *
        legendreField p j).comp (-X) =
      -(C (((j + 1 : ℕ) : ZMod p)⁻¹) * legendreField p (j + 1) * legendreField p j) := by
    rw [mul_comp, mul_comp, C_comp, legendreField_reflect p (j + 1) hp,
      legendreField_reflect p j hp]
    have hs : C ((-1 : ZMod p) ^ (j + 1)) * C ((-1 : ZMod p) ^ j) = -1 := by
      rw [← C_mul]
      have he : (-1 : ZMod p) ^ (j + 1) * (-1 : ZMod p) ^ j = -1 := by
        rw [pow_succ]
        linear_combination -(negative_power_square (K := ZMod p) j)
      rw [he, C_neg, C_1]
    linear_combination C (((j + 1 : ℕ) : ZMod p)⁻¹) *
      legendreField p (j + 1) * legendreField p j * hs
  simp only [adjacentPrimitive, neg_comp, sum_comp, ht, Finset.sum_neg_distrib, neg_neg]

theorem legendreJacobi_reflect {K : Type*} [CommRing K] (d : ℕ) (P : K[X]) :
    legendreJacobi d (P.comp (-X)) = (legendreJacobi d P).comp (-X) := by
  simp [legendreJacobi, derivative_comp]

theorem actual_small_legendre_kernel (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : (ZMod p)[X]) (hdegree : P.natDegree < p / 6)
    (hsource : legendreJacobi (p / 6) P = 0) : P = 0 := by
  by_contra hP
  let m := P.natDegree
  let d := p / 6
  have hm : m < d := hdegree
  have h1 := small_cast_ne_zero p (d - m) (by omega) (by omega)
  have h2 := small_cast_ne_zero p (d + m + 1) (by omega) (by omega)
  have hu : (d : ZMod p) * ((d : ZMod p) + 1) -
      (m : ZMod p) * ((m : ZMod p) + 1) ≠ 0 := by
    have he : (d : ZMod p) * ((d : ZMod p) + 1) -
        (m : ZMod p) * ((m : ZMod p) + 1) =
        ((d - m : ℕ) : ZMod p) * ((d + m + 1 : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (by omega : m ≤ d)]
      push_cast
      ring
    rw [he]
    exact mul_ne_zero h1 h2
  have hc := congrArg (fun Q : (ZMod p)[X] => Q.coeff m) hsource
  rw [legendreJacobi_coeff, coeff_zero,
    coeff_eq_zero_of_natDegree_lt (by dsimp [m]; omega), mul_zero, zero_add] at hc
  have hz := (mul_eq_zero.mp hc).resolve_left hu
  exact (leadingCoeff_ne_zero.mpr hP) (by simpa only [m, coeff_natDegree] using hz)

theorem actual_proper_legendre_reflect (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (properLegendreJacobi p).comp (-X) =
      -C ((-1 : ZMod p) ^ (p / 6)) * properLegendreJacobi p := by
  let Y := actualLegendreJacobi p
  let n := properLegendreJacobi p
  let s : ZMod p := (-1) ^ (p / 6)
  have hY : Y.comp (-X) = C s * Y := legendreField_reflect p (p / 6) (by omega)
  have hDY : Y.derivative.comp (-X) = -C s * Y.derivative := by
    have hd := congrArg Polynomial.derivative hY
    simp only [derivative_comp, derivative_neg, derivative_X, derivative_C_mul] at hd
    linear_combination -hd
  have hz : n.comp (-X) + C s * n = 0 := by
    apply actual_small_legendre_kernel p hp
    · have hdn : n.natDegree < p / 6 := properLegendreJacobi_degree p (by omega)
      have hcomp : (n.comp (-X)).natDegree ≤ n.natDegree :=
        natDegree_comp_le.trans (by simp)
      have hbound : (n.comp (-X) + C s * n).natDegree ≤ n.natDegree := by
        simpa only [max_self] using natDegree_add_le_of_le hcomp
          (natDegree_C_mul_le s n)
      exact hbound.trans_lt hdn
    · rw [legendreJacobi_add, legendreJacobi_reflect, legendreJacobi_C_mul,
        properLegendreJacobi_source p (by omega)]
      simp only [mul_comp, neg_comp, ofNat_comp]
      change -2 * Y.derivative.comp (-X) + C s * (-2 * Y.derivative) = 0
      rw [hDY]
      ring
  linear_combination hz

theorem actual_rank_divided_reflect (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualRankDividedField p (by omega)).comp (-X) =
      C ((-1 : ZMod p) ^ (p / 6)) * actualRankDividedField p (by omega) := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hE : (evenLogPolynomial p).comp (-X) = evenLogPolynomial p := by
    simp only [evenLogPolynomial, mul_comp, C_comp, add_comp, comp_assoc,
      neg_comp, X_comp, neg_neg, comp_X]
    ring
  have hXp : (-X : (ZMod p)[X]) ^ p = -X ^ p := by
    rw [hpodd.neg_pow]
  rw [actual_rankDividedField_eq_hat p hp, rankHatField]
  simp only [sub_comp, mul_comp, add_comp, C_comp, pow_comp, X_comp,
    actual_proper_legendre_reflect p hp, hE, hXp]
  rw [← legendreField_actual, legendreField_reflect p (p / 6) (by omega)]
  ring

theorem actual_legendre_exact_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualLegendreJacobi p).natDegree = p / 6 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (actualLegendreJacobi_degree p)
  intro hz
  have ht := actual_rank_top_product p hp
  rw [hz, mul_zero, zero_mul] at ht
  norm_num at ht

theorem fullLogNumerator_expansion (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    fullLogNumerator p hp =
      2 * (fullC2Integral p hp).map (residueHom p) -
        4 * actualRankDividedField p (by omega) ^ 2 := by
  simp only [fullLogNumerator, fullQField, fullQIntegral,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat,
    Polynomial.map_pow]
  change 2 * _ - 2 * actualRankDividedField p (by omega) ^ 2 -
    2 * actualRankDividedField p (by omega) ^ 2 = _
  ring

theorem fullLogNumerator_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullLogNumerator p hp).natDegree ≤ 2 * fullCutoff p := by
  have hR := actualRankDividedField_degree p (by omega)
  have hR2 : (actualRankDividedField p (by omega) ^ 2).natDegree ≤ 2 * fullCutoff p :=
    natDegree_pow_le_of_le 2 hR
  simpa only [fullLogNumerator, C_ofNat, max_self] using natDegree_sub_le_of_le
    (fullQField_degree p hp)
    ((natDegree_C_mul_le (2 : ZMod p) _).trans hR2)

theorem fullLogNumerator_even (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullLogNumerator p hp).comp (-X) = fullLogNumerator p hp := by
  have hC2 : (fullC2Integral p hp).comp (-X) = fullC2Integral p hp := by
    simp only [fullC2Integral, comp_assoc, sub_comp, one_comp, pow_comp,
      X_comp]
    congr 1
    ring
  have hC2f := congrArg (Polynomial.map (residueHom p)) hC2
  simp only [Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X] at hC2f
  have hs : C ((-1 : ZMod p) ^ (p / 6)) ^ 2 = (1 : (ZMod p)[X]) := by
    rw [← C_pow, negative_power_square, C_1]
  rw [fullLogNumerator_expansion, sub_comp, mul_comp, ofNat_comp,
    mul_comp, ofNat_comp, pow_comp, hC2f, actual_rank_divided_reflect p hp,
    mul_pow, hs, one_mul]
  norm_num only [Nat.cast_ofNat]

theorem fullC2Field_one (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((fullC2Integral p hp).map (residueHom p)).eval 1 = 0 := by
  have hv := congrArg (fun P : ℚ[X] => P.eval 1) (fullC2Integral_value p hp)
  have hrat : (fullC2 p).eval 1 = 0 := by
    simp [fullC2, eval_comp, nativeSecondJetAt_origin]
  rw [hrat] at hv
  change ((fullC2Integral p hp).map (integralRationals p).subtype).eval
    ((integralRationals p).subtype 1) = 0 at hv
  rw [eval_map_apply] at hv
  have hi : (fullC2Integral p hp).eval 1 = 0 := Subtype.ext hv
  rw [← (residueHom p).map_one]
  rw [eval_map_apply, hi, _root_.map_zero]

theorem fullLogNumerator_one (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullLogNumerator p hp).eval 1 = 0 := by
  rw [fullLogNumerator_expansion]
  simp [fullC2Field_one p hp, actualRankDividedField_endpoint_one]

theorem fullLogNumerator_neg_one (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullLogNumerator p hp).eval (-1) = 0 := by
  have h := congrArg (fun P : (ZMod p)[X] => P.eval 1) (fullLogNumerator_even p hp)
  simpa only [eval_comp, eval_neg, eval_X, fullLogNumerator_one p hp] using h

theorem actual_adjacent_primitive_data (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1 - X ^ 2) * (adjacentPrimitive p (p / 6)).derivative =
        actualLegendreJacobi p ^ 2 - 1 ∧
      (adjacentPrimitive p (p / 6)).natDegree ≤ 2 * (p / 6) - 1 ∧
      (adjacentPrimitive p (p / 6)).comp (-X) = -adjacentPrimitive p (p / 6) ∧
      (adjacentPrimitive p (p / 6)).eval 1 = (properLegendreJacobi p).eval 1 := by
  exact ⟨adjacentPrimitive_source p (p / 6) hp le_rfl,
    adjacentPrimitive_degree p (p / 6),
    adjacentPrimitive_odd p (p / 6) (by omega), by
      rw [adjacentPrimitive_one, properLegendreJacobi_endpoint_one]⟩

theorem quadraticGreen_first_factor {K : Type*} [CommRing K] (Y L : K[X]) :
    (1 - X ^ 2) *
      (Y * ((1 - X ^ 2) * (Y * L.derivative - 2 * Y.derivative * L)).derivative -
        Y.derivative * ((1 - X ^ 2) * (Y * L.derivative - 2 * Y.derivative * L))) =
      quadraticGreen Y L := by
  simp [quadraticGreen, derivative_mul]
  ring

theorem actual_full_IR28_first_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1 - X ^ 2) *
      (actualLegendreJacobi p * (fullLogNumerator p hp).derivative -
        2 * (actualLegendreJacobi p).derivative * fullLogNumerator p hp) =
      4 * (adjacentPrimitive p (p / 6) * actualLegendreJacobi p -
        properLegendreJacobi p) := by
  let d := p / 6
  let e := fullCutoff p
  let Y := actualLegendreJacobi p
  let n := properLegendreJacobi p
  let B := adjacentPrimitive p d
  let L := fullLogNumerator p hp
  let q : (ZMod p)[X] := 1 - X ^ 2
  let s : ZMod p := (-1) ^ d
  let A := q * (Y * L.derivative - 2 * Y.derivative * L)
  let P := 4 * (B * Y - n)
  let D := A - P
  have hde : d + e + 1 = p := by dsimp [d, e, fullCutoff]; omega
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hde' : d ≤ e := by dsimp [d, e, fullCutoff]; omega
  have he : 1 ≤ e := by omega
  have hq : q.comp (-X) = q := by simp [q]
  have hqdeg : q.natDegree ≤ 2 := by dsimp [q]; compute_degree
  have hqne : q ≠ 0 := by
    intro hz
    have hc := congrArg (fun P : (ZMod p)[X] => P.coeff 2) hz
    norm_num [q, coeff_one] at hc
  have hYdeg : Y.natDegree ≤ d := actualLegendreJacobi_degree p
  have hLdeg : L.natDegree ≤ 2 * e := fullLogNumerator_degree p hp
  have hndeg : n.natDegree < d := properLegendreJacobi_degree p (by omega)
  have hBdeg : B.natDegree ≤ 2 * d - 1 := adjacentPrimitive_degree p d
  have hY1 : Y.eval 1 = 1 := actualLegendreJacobi_endpoint_one p
  have hYne : Y ≠ 0 := by
    intro hz
    have h := congrArg (fun P : (ZMod p)[X] => P.eval 1) hz
    rw [hY1] at h
    simp at h
  have hY : Y.comp (-X) = C s * Y := legendreField_reflect p d (by omega)
  have hn : n.comp (-X) = -C s * n := actual_proper_legendre_reflect p hp
  have hB : B.comp (-X) = -B := adjacentPrimitive_odd p d (by omega)
  have hL : L.comp (-X) = L := fullLogNumerator_even p hp
  have hB1 : B.eval 1 = n.eval 1 := (actual_adjacent_primitive_data p hp).2.2.2
  have hBs : q * B.derivative = Y ^ 2 - 1 := (actual_adjacent_primitive_data p hp).1
  have hnW : q * (Y * n.derivative - Y.derivative * n) = 1 - Y ^ 2 :=
    properLegendreJacobi_wronskian p (by omega)
  have hDY : Y.derivative.comp (-X) = -C s * Y.derivative := by
    have h := congrArg Polynomial.derivative hY
    simp only [derivative_comp, derivative_neg, derivative_X, derivative_C_mul] at h
    linear_combination -h
  have hDL : L.derivative.comp (-X) = -L.derivative := by
    have h := congrArg Polynomial.derivative hL
    simp only [derivative_comp, derivative_neg, derivative_X] at h
    linear_combination -h
  have hAodd : A.comp (-X) = -C s * A := by
    simp only [A, mul_comp, sub_comp, ofNat_comp, hq, hY, hDY, hDL, hL]
    norm_num only [Nat.cast_ofNat]
    ring
  have hPodd : P.comp (-X) = -C s * P := by
    simp only [P, mul_comp, sub_comp, ofNat_comp, hB, hY, hn]
    norm_num only [Nat.cast_ofNat]
    ring
  have hDodd : D.comp (-X) = -C s * D := by
    dsimp only [D]
    rw [sub_comp, hAodd, hPodd]
    ring
  have hD1 : D.eval 1 = 0 := by
    simp only [D, A, P, q, eval_sub, eval_mul, eval_ofNat, eval_pow,
      eval_one, eval_X, one_pow, sub_self, zero_mul, hY1, mul_one, hB1]
    ring
  have hDYdeg : Y.derivative.natDegree ≤ d - 1 := by
    have h := natDegree_derivative_le Y
    omega
  have hDLdeg : L.derivative.natDegree ≤ 2 * e - 1 := by
    have h := natDegree_derivative_le L
    omega
  have hAdeg : A.natDegree ≤ d + 2 * e + 1 := by
    have h1 : (Y * L.derivative).natDegree ≤ d + 2 * e - 1 :=
      (natDegree_mul_le_of_le hYdeg hDLdeg).trans (by omega)
    have h2 : (2 * Y.derivative * L).natDegree ≤ d + 2 * e - 1 := by
      rw [mul_assoc]
      exact (natDegree_C_mul_le _ _).trans
        ((natDegree_mul_le_of_le hDYdeg hLdeg).trans (by omega))
    exact (natDegree_mul_le_of_le hqdeg
      (by simpa only [max_self] using natDegree_sub_le_of_le h1 h2)).trans (by omega)
  have hPdeg : P.natDegree ≤ 3 * d - 1 := by
    apply (natDegree_C_mul_le (4 : ZMod p) _).trans
    have hBY : (B * Y).natDegree ≤ 3 * d - 1 :=
      (natDegree_mul_le_of_le hBdeg hYdeg).trans (by omega)
    simpa only [max_self] using natDegree_sub_le_of_le hBY
      (show n.natDegree ≤ 3 * d - 1 by omega)
  have hDdeg : D.natDegree < 2 * p := by
    have h := natDegree_sub_le_of_le hAdeg
      (hPdeg.trans (by omega : 3 * d - 1 ≤ d + 2 * e + 1))
    dsimp only [D]
    exact h.trans_lt (by omega)
  have hPs : q * (Y * P.derivative - Y.derivative * P) = 4 * (Y ^ 4 - 1) := by
    dsimp only [P]
    simp only [derivative_mul, derivative_sub, derivative_ofNat, zero_mul, zero_add]
    linear_combination 4 * Y ^ 2 * hBs - 4 * hnW
  have hDs : q * (Y * D.derivative - Y.derivative * D) = 0 := by
    dsimp only [D]
    simp only [derivative_sub]
    linear_combination quadraticGreen_first_factor Y L +
      actual_full_log_numerator_Green p hp - hPs
  have hzero : Y * D.derivative - Y.derivative * D = 0 :=
    (mul_eq_zero.mp hDs).resolve_left hqne
  have hbez : Y * (q * n.derivative + Y) - Y.derivative * (q * n) = 1 := by
    linear_combination hnW
  let H := (q * n.derivative + Y) * D - q * n * D.derivative
  have hfactor : D = Y * H := by
    dsimp only [H]
    linear_combination -D * hbez + q * n * hzero
  have hHder : H.derivative = 0 := by
    have hz : Y ^ 2 * H.derivative = 0 := by
      rw [hfactor] at hzero
      simp only [derivative_mul] at hzero
      linear_combination hzero
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hYne)
  have hHdeg : H.natDegree < 2 * p := by
    by_cases hz : H = 0
    · simp [hz]; omega
    · rw [hfactor, natDegree_mul hYne hz] at hDdeg
      omega
  have hs : s ≠ 0 := by
    have hsq : s ^ 2 = (1 : ZMod p) := negative_power_square (K := ZMod p) d
    intro hz
    rw [hz] at hsq
    norm_num at hsq
  have hHodd : H.comp (-X) = -H := by
    have hf := congrArg (fun P : (ZMod p)[X] => P.comp (-X)) hfactor
    rw [mul_comp, hY, hDodd, hfactor] at hf
    apply mul_left_cancel₀ (mul_ne_zero (C_ne_zero.mpr hs) hYne)
    linear_combination -hf
  have hH1 : H.eval 1 = 0 := by
    have hf := congrArg (fun P : (ZMod p)[X] => P.eval 1) hfactor
    rw [hD1, eval_mul, hY1, one_mul] at hf
    exact hf.symm
  have hkernel := derivative_zero_two_digits p H hHdeg hHder
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have hH0 : H.coeff 0 = 0 := by
    have hc := congrArg (fun P : (ZMod p)[X] => P.coeff 0) hHodd
    rw [coeff_comp_neg, coeff_neg] at hc
    norm_num only [pow_zero, mul_one] at hc
    have hz : (2 : ZMod p) * H.coeff 0 = 0 := by linear_combination hc
    exact (mul_eq_zero.mp hz).resolve_left h2
  have hHp : H.coeff p = 0 := by
    have hc := congrArg (fun P : (ZMod p)[X] => P.eval 1) hkernel
    simp only [hH1, eval_add, eval_C, eval_mul, eval_pow, eval_X,
      one_pow, mul_one, hH0, zero_add] at hc
    exact hc.symm
  have hHz : H = 0 := by rw [hkernel, hH0, hHp]; simp
  have hDz : D = 0 := by rw [hfactor, hHz, mul_zero]
  change A = P
  exact sub_eq_zero.mp hDz

theorem actual_full_IR28_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullLogNumerator p hp).natDegree ≤ 2 * (p / 6) := by
  let d := p / 6
  let e := fullCutoff p
  let Y := actualLegendreJacobi p
  let B := adjacentPrimitive p d
  let n := properLegendreJacobi p
  let L := fullLogNumerator p hp
  let q : (ZMod p)[X] := 1 - X ^ 2
  let S := L / Y ^ 2
  let T := L % Y ^ 2
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hYdeg : Y.natDegree = d := actual_legendre_exact_degree p hp
  have hY1 : Y.eval 1 = 1 := actualLegendreJacobi_endpoint_one p
  have hYne : Y ≠ 0 := by
    intro hz
    have h := congrArg (fun P : (ZMod p)[X] => P.eval 1) hz
    rw [hY1] at h
    simp at h
  have hYtop : Y.coeff d ≠ 0 := by
    rw [← hYdeg, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hYne
  have hY2deg : (Y ^ 2).natDegree = 2 * d := by rw [natDegree_pow, hYdeg]
  have hY3deg : (Y ^ 3).natDegree = 3 * d := by rw [natDegree_pow, hYdeg]
  have hqdeg : q.natDegree = 2 := by dsimp [q]; (compute_degree; norm_num)
  have hqne : q ≠ 0 := by intro hz; simp [hz] at hqdeg
  have hLdeg : L.natDegree ≤ 2 * e := fullLogNumerator_degree p hp
  have hLeven : L.comp (-X) = L := fullLogNumerator_even p hp
  have hBdeg : B.natDegree ≤ 2 * d - 1 := adjacentPrimitive_degree p d
  have hndeg : n.natDegree < d := properLegendreJacobi_degree p (by omega)
  have hTdeg : T.natDegree < 2 * d := by
    simpa only [T, hY2deg] using
      natDegree_mod_lt L (show (Y ^ 2).natDegree ≠ 0 by rw [hY2deg]; omega)
  have heq : L = Y ^ 2 * S + T := by
    simpa only [S, T, mul_comm] using (EuclideanDomain.div_add_mod L (Y ^ 2)).symm
  have hfirst := actual_full_IR28_first_source p hp
  change q * (Y * L.derivative - 2 * Y.derivative * L) = 4 * (B * Y - n) at hfirst
  have hSd : q * Y ^ 3 * S.derivative =
      4 * (B * Y - n) - q * (Y * T.derivative - 2 * Y.derivative * T) := by
    rw [heq] at hfirst
    simp only [derivative_add, derivative_mul, derivative_pow_succ] at hfirst
    norm_num only [Nat.cast_one, one_add_one_eq_two, C_ofNat, pow_one] at hfirst
    linear_combination hfirst
  have hDYdeg : Y.derivative.natDegree ≤ d - 1 := by
    have h := natDegree_derivative_le Y
    omega
  have hDTdeg : T.derivative.natDegree ≤ 2 * d - 2 := by
    have h := natDegree_derivative_le T
    omega
  have hPdeg : (4 * (B * Y - n)).natDegree ≤ 3 * d := by
    apply (natDegree_C_mul_le (4 : ZMod p) _).trans
    have h1 : (B * Y).natDegree ≤ 3 * d :=
      (natDegree_mul_le_of_le hBdeg (le_of_eq hYdeg)).trans (by omega)
    simpa only [max_self] using natDegree_sub_le_of_le h1
      (show n.natDegree ≤ 3 * d by omega)
  have hTsource : (q * (Y * T.derivative - 2 * Y.derivative * T)).natDegree ≤ 3 * d := by
    have h1 : (Y * T.derivative).natDegree ≤ 3 * d - 2 :=
      (natDegree_mul_le_of_le (le_of_eq hYdeg) hDTdeg).trans (by omega)
    have h2 : (2 * Y.derivative * T).natDegree ≤ 3 * d - 2 := by
      rw [mul_assoc]
      exact (natDegree_C_mul_le _ _).trans
        ((natDegree_mul_le_of_le hDYdeg (show T.natDegree ≤ 2 * d - 1 by omega)).trans
          (by omega))
    exact (natDegree_mul_le_of_le (le_of_eq hqdeg)
      (by simpa only [max_self] using natDegree_sub_le_of_le h1 h2)).trans (by omega)
  have hSder : S.derivative = 0 := by
    by_contra hz
    have hb : (q * Y ^ 3 * S.derivative).natDegree ≤ 3 * d := by
      rw [hSd]
      simpa only [max_self] using natDegree_sub_le_of_le hPdeg hTsource
    rw [natDegree_mul (mul_ne_zero hqne (pow_ne_zero 3 hYne)) hz,
      natDegree_mul hqne (pow_ne_zero 3 hYne), hqdeg, hY3deg] at hb
    omega
  have hSdeg : S.natDegree < 2 * p := by
    have h : S.natDegree ≤ 2 * e :=
      natDegree_le_of_degree_le ((degree_div_le L (Y ^ 2)).trans
        (degree_le_of_natDegree_le hLdeg))
    dsimp [e, fullCutoff] at h
    omega
  have hS := derivative_zero_two_digits p S hSdeg hSder
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hsign : (-1 : ZMod p) ^ (2 * d + p) = -1 := by
    rw [pow_add, pow_mul]
    norm_num only [neg_one_sq, one_pow, one_mul]
    exact hpodd.neg_one_pow
  have hLodd : L.coeff (2 * d + p) = 0 := by
    have hc := congrArg (fun P : (ZMod p)[X] => P.coeff (2 * d + p)) hLeven
    rw [coeff_comp_neg, hsign] at hc
    have hz : (2 : ZMod p) * L.coeff (2 * d + p) = 0 := by linear_combination -hc
    exact (mul_eq_zero.mp hz).resolve_left h2
  have hY2top : (Y ^ 2).coeff (2 * d) = Y.coeff d ^ 2 := by
    rw [pow_two, show 2 * d = d + d by omega,
      coeff_mul_add_eq_of_natDegree_le (le_of_eq hYdeg) (le_of_eq hYdeg)]
    ring
  have hhigh : L.coeff (2 * d + p) = S.coeff p * Y.coeff d ^ 2 := by
    conv_lhs => rw [heq, hS]
    have he : Y ^ 2 * (C (S.coeff 0) + C (S.coeff p) * X ^ p) + T =
        C (S.coeff 0) * Y ^ 2 + C (S.coeff p) * (Y ^ 2 * X ^ p) + T := by ring
    have hY2zero : (Y ^ 2).coeff (2 * d + p) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [hY2deg]; omega)
    have hTzero : T.coeff (2 * d + p) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    rw [he, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul,
      hY2zero, hTzero, mul_zero, add_zero, zero_add, coeff_mul_X_pow, hY2top]
  have hSp : S.coeff p = 0 := by
    have hz : S.coeff p * Y.coeff d ^ 2 = 0 := by rw [← hhigh, hLodd]
    exact (mul_eq_zero.mp hz).resolve_right (pow_ne_zero 2 hYtop)
  have hSc : S = C (S.coeff 0) := by rw [hS, hSp]; simp
  change L.natDegree ≤ 2 * d
  rw [heq, hSc]
  have h1 : (Y ^ 2 * C (S.coeff 0)).natDegree ≤ 2 * d := by
    rw [mul_comm]
    exact (natDegree_C_mul_le _ _).trans (le_of_eq hY2deg)
  simpa only [max_self] using natDegree_add_le_of_le h1 (le_of_lt hTdeg)

theorem even_expand_contract_two (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : (ZMod p)[X]) (heven : P.comp (-X) = P) :
    expand (ZMod p) 2 (contract 2 P) = P := by
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  ext j
  rw [coeff_expand (by norm_num : 0 < 2)]
  by_cases hj : 2 ∣ j
  · rw [if_pos hj, coeff_contract (by norm_num : 2 ≠ 0), Nat.div_mul_cancel hj]
  · rw [if_neg hj]
    have hm : j % 2 = 1 := by
      have hlt := Nat.mod_lt j (by norm_num : 0 < 2)
      have hne : j % 2 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hj
      omega
    have hodd : Odd j := ⟨j / 2, by have h := Nat.mod_add_div j 2; omega⟩
    have hc := congrArg (fun P : (ZMod p)[X] => P.coeff j) heven
    rw [coeff_comp_neg, hodd.neg_one_pow] at hc
    have hz : (2 : ZMod p) * P.coeff j = 0 := by linear_combination -hc
    exact ((mul_eq_zero.mp hz).resolve_left h2).symm

noncomputable def fullIR28NativeLow (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (ZMod p)[X] :=
  (contract 2 (fullLogNumerator p hp)).comp (1 - X)

theorem actual_full_IR28_native_attachment (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullIR28NativeLow p hp).comp (1 - X ^ 2) = fullLogNumerator p hp := by
  have he := even_expand_contract_two p hp (fullLogNumerator p hp)
    (fullLogNumerator_even p hp)
  rw [expand_eq_comp_X_pow] at he
  rw [fullIR28NativeLow, comp_assoc]
  (convert he using 1; simp)

theorem actual_full_IR28_native_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullIR28NativeLow p hp).natDegree ≤ p / 6 := by
  have he := even_expand_contract_two p hp (fullLogNumerator p hp)
    (fullLogNumerator_even p hp)
  have hd := actual_full_IR28_degree p hp
  have hh : (contract 2 (fullLogNumerator p hp)).natDegree * 2 ≤ 2 * (p / 6) := by
    rw [← natDegree_expand 2, he]
    exact hd
  have hc : (contract 2 (fullLogNumerator p hp)).natDegree ≤ p / 6 := by omega
  have ha : (1 - X : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
  exact natDegree_comp_le.trans ((Nat.mul_le_mul hc ha).trans (by simp))

theorem actual_full_IR28_native_origin (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullIR28NativeLow p hp).eval 0 = 0 := by
  have h := congrArg (fun P : (ZMod p)[X] => P.eval 1)
    (actual_full_IR28_native_attachment p hp)
  simpa only [eval_comp, eval_sub, eval_one, eval_pow, eval_X,
    one_pow, sub_self, fullLogNumerator_one p hp] using h

theorem seventyTwo_ne_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (72 : ZMod p) ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := small_cast_ne_zero p 3 (by omega) (by omega)
  rw [show (72 : ZMod p) = 2 ^ 3 * 3 ^ 2 by ring]
  exact mul_ne_zero (pow_ne_zero 3 h2) (pow_ne_zero 2 h3)

theorem actual_native_IR28_full_low_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeIR28DifferenceFull p hp).natDegree ≤ 2 * (p / 6) := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  have hc := congrArg (fun P : (ZMod p)[X] => P.coeff j)
    (actual_native_IR28_models p hp)
  rw [coeff_ofNat_mul, coeff_ofNat_mul,
    coeff_eq_zero_of_natDegree_lt ((actual_full_IR28_degree p hp).trans_lt hj),
    mul_zero] at hc
  exact (mul_eq_zero.mp hc).resolve_left (seventyTwo_ne_zero p hp)

theorem actual_native_IR28_full_q_witness (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ∃ l : (ZMod p)[X], l.natDegree ≤ p / 6 ∧ l.eval 0 = 0 ∧
      nativeIR28DifferenceFull p hp = l.comp (1 - X ^ 2) := by
  let l : (ZMod p)[X] := C (5 / 72 : ZMod p) * fullIR28NativeLow p hp
  refine ⟨l, (natDegree_C_mul_le _ _).trans (actual_full_IR28_native_degree p hp), ?_, ?_⟩
  · simp [l, actual_full_IR28_native_origin p hp]
  · have h72 := seventyTwo_ne_zero p hp
    have hunit : C (72 : ZMod p) * C (5 / 72 : ZMod p) = C (5 : ZMod p) := by
      rw [← C_mul]
      congr 1
      field_simp [h72]
    apply mul_left_cancel₀ (C_ne_zero.mpr h72)
    rw [show C (72 : ZMod p) * nativeIR28DifferenceFull p hp =
        72 * nativeIR28DifferenceFull p hp by rfl,
      actual_native_IR28_models p hp]
    simp only [l, mul_comp, C_comp]
    rw [← mul_assoc, hunit, actual_full_IR28_native_attachment p hp]
    rfl

end WPFieldAssembly.NativeIR28
