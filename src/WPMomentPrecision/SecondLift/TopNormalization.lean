import WPMomentPrecision.SecondLift.TwoNodeTaylor

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPNativeParameterTaylor WPActualNativeParameter
  WPActualNativeFirstJet WPActualNativeJetRecurrence WPActualRankTwoParameter
  WPMomentPrecision.FullNativeTaylor WPActualRankTwoLowTaylor

namespace WPMomentPrecision.TopNormalization

set_option maxHeartbeats 1200000

/-- The two exceptional factors alone fix the top native first/second ratio. -/
theorem centered_double_factor_quotient (a : ℚ) (ha : a ≠ 0) (B D : ℚ[X])
    (hD : D.eval 0 ≠ 0) :
    quotientJet (X * (2 * X + C (2 * a / 3)) * B) D 0 / a -
        quotientFullSecondJet (X * (2 * X + C (2 * a / 3)) * B) D 0 / 6 =
      -(2 * a / 9) * quotientJet B D 0 := by
  simp only [quotientJet, quotientFullSecondJet, derivative_mul, derivative_add,
    derivative_C, derivative_X, derivative_ofNat,
    eval_mul, eval_add, eval_C, eval_X, eval_ofNat, zero_mul, mul_zero,
    zero_add, add_zero, one_mul, mul_one]
  field_simp [ha, hD]
  ring

theorem quotientJet_taylor (A D : ℚ[X]) (t : ℚ) :
    quotientJet (taylor t A) (taylor t D) 0 = quotientJet A D t := by
  simp only [quotientJet, derivative_taylor_rational, taylor_eval, zero_add]

theorem quotientFullSecondJet_taylor (A D : ℚ[X]) (t : ℚ) :
    quotientFullSecondJet (taylor t A) (taylor t D) 0 = quotientFullSecondJet A D t := by
  simp only [quotientFullSecondJet, derivative_taylor_rational, taylor_eval, zero_add]

theorem low_upper_factor_node_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (upperFactor (integralRationals p) (p / 6)).eval (integralNode p (by omega)) = 0 := by
  apply Subtype.ext
  simp only [Subring.coe_zero]
  rw [evaluate_subtype, upperFactor_map, integralNode_value]
  simp only [upperFactor, eval_mul, eval_add, eval_C, eval_ofNat, eval_X]
  rcases prime_six_classes p (by omega) with hp1 | hp5
  · have hq : (p : ℚ) = 6 * ((p / 6 : ℕ) : ℚ) + 1 := by exact_mod_cast hp1
    rw [hq]
    ring
  · have hq : (p : ℚ) = 6 * ((p / 6 : ℕ) : ℚ) + 5 := by exact_mod_cast hp5
    rw [hq]
    ring

/-- The original top numerator has the centered d and N factors over the integral subring. -/
theorem actual_top_centered_factors (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ∃ B : (integralRationals p)[X],
      taylor (integralNode p (by omega))
          (clearedNumerator (integralRationals p) (p - 1 - p / 6)) =
        X * (2 * X + C (4 * (p : integralRationals p) * integralSixth p (by omega))) * B := by
  classical
  let d := p / 6
  let N := (p - 1) / 2
  let e := p - 1 - p / 6
  let t := integralNode p (by omega)
  let S := Finset.range e
  have hd := Nat.div_mul_le_self p 6
  have hh := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  have hdS : d ∈ S := Finset.mem_range.mpr (by dsimp [d, e]; omega)
  have hNS : N ∈ S.erase d := by
    apply Finset.mem_erase.mpr
    constructor
    · dsimp [N, d]
      omega
    · apply Finset.mem_range.mpr
      dsimp [N, e]
      omega
  have hP : clearedNumerator (integralRationals p) e =
      upperFactor (integralRationals p) d * upperFactor (integralRationals p) N *
        ∏ j ∈ (S.erase d).erase N, upperFactor (integralRationals p) j := by
    change (∏ j ∈ S, upperFactor (integralRationals p) j) = _
    rw [← Finset.mul_prod_erase S (upperFactor (integralRationals p)) hdS,
      ← Finset.mul_prod_erase (S.erase d) (upperFactor (integralRationals p)) hNS]
    ring
  have hlow : (X : (integralRationals p)[X]) ∣
      taylor t (upperFactor (integralRationals p) d) := by
    apply X_dvd_iff.mpr
    rw [taylor_coeff_zero]
    exact low_upper_factor_node_zero p hp
  obtain ⟨B₀, hB₀⟩ := hlow
  let B₁ : (integralRationals p)[X] :=
    taylor t (C (6 * (N : integralRationals p) + 1) + 6 * X) *
      taylor t (C (6 * (N : integralRationals p) + 5) + 6 * X)
  have hmid : 2 * (N : integralRationals p) + 1 + 2 * t =
      4 * (p : integralRationals p) * integralSixth p (by omega) := by
    apply Subtype.ext
    change 2 * (N : ℚ) + 1 + 2 * (integralNode p (by omega)).val =
      4 * (p : ℚ) * (1 / 6 : ℚ)
    rw [integralNode_value]
    have hq : 2 * (N : ℚ) + 1 = (p : ℚ) := by exact_mod_cast hh
    linear_combination hq
  have hB₁ : taylor t (upperFactor (integralRationals p) N) =
      (2 * X + C (4 * (p : integralRationals p) * integralSixth p (by omega))) * B₁ := by
    have hmiddle : taylor t (C (2 * (N : integralRationals p) + 1) + 2 * X) =
        2 * X + C (4 * (p : integralRationals p) * integralSixth p (by omega)) := by
      simp only [taylor_apply, add_comp, mul_comp, C_comp, ofNat_comp, X_comp]
      have hc := congrArg (C : integralRationals p → (integralRationals p)[X]) hmid
      simp only [map_add, map_mul, map_ofNat, map_one] at hc ⊢
      linear_combination hc
    simp only [upperFactor, taylor_mul]
    rw [hmiddle]
    dsimp only [B₁]
    ring
  refine ⟨B₀ * B₁ * taylor t
    (∏ j ∈ (S.erase d).erase N, upperFactor (integralRationals p) j), ?_⟩
  change taylor t (clearedNumerator (integralRationals p) e) = _
  rw [hP, taylor_mul, taylor_mul, hB₀, hB₁]
  ring

/-- The actual top first jet is divided over Q; its ratio to the full K has an integral p error. -/
theorem actual_top_first_second_ratio (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ∃ r : integralRationals p,
      parameterJet (p - 1 - p / 6) (-(p : ℚ) / 6) / (p : ℚ) -
        nativeFullSecondJetCoefficient p (p - 1 - p / 6) / 6 = (p : ℚ) * r.val := by
  let e := p - 1 - p / 6
  let t := integralNode p (by omega)
  let D := taylor t (clearedDenominator (integralRationals p) e)
  obtain ⟨B, hB⟩ := actual_top_centered_factors p hp
  have ht := denominator_node_unit p e (by omega) (by dsimp [e]; omega)
  have hDe : D.eval 0 = (clearedDenominator (integralRationals p) e).eval t := by
    simp [D, taylor_eval]
  have hD0 : (D.eval 0).val ≠ 0 := by rw [hDe]; exact ht.1
  have hiD0 : (D.eval 0).val⁻¹ ∈ integralRationals p := by rw [hDe]; exact ht.2
  let u : integralRationals p := ⟨(D.eval 0).val⁻¹, hiD0⟩
  let j : integralRationals p := WPActualNativeSecondJet.firstJetOver B D 0 u
  have hj : j.val = quotientJet (B.map (integralRationals p).subtype)
      (D.map (integralRationals p).subtype) 0 := by
    change (B.derivative.eval 0).val * (D.eval 0).val⁻¹ -
      (B.eval 0).val * (D.derivative.eval 0).val * ((D.eval 0).val⁻¹) ^ 2 = _
    rw [derivative_evaluate_subtype, derivative_evaluate_subtype,
      evaluate_subtype, evaluate_subtype, Subring.coe_zero]
    have hDQ : (D.map (integralRationals p).subtype).eval 0 ≠ 0 := by
      simpa only [evaluate_subtype, Subring.coe_zero] using hD0
    exact WPActualNativeSecondJet.firstJetOver_rational _ _ _ hDQ
  refine ⟨-8 * integralSixth p (by omega) ^ 2 * j, ?_⟩
  have hBQ := congrArg (fun P : (integralRationals p)[X] =>
    P.map (integralRationals p).subtype) hB
  rw [Polynomial.map_taylor, clearedNumerator_map] at hBQ
  change taylor (integralNode p (by omega)).val (clearedNumerator ℚ e) =
    (X * (2 * X + C (4 * (p : integralRationals p) *
      integralSixth p (by omega))) * B).map (integralRationals p).subtype at hBQ
  rw [integralNode_value] at hBQ
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_ofNat, Polynomial.map_C] at hBQ
  have hscalar : (4 * (p : integralRationals p) * integralSixth p (by omega)).val =
      2 * (p : ℚ) / 3 := by
    change 4 * (p : ℚ) * (1 / 6 : ℚ) = 2 * (p : ℚ) / 3
    ring
  change (integralRationals p).subtype
    (4 * (p : integralRationals p) * integralSixth p (by omega)) = _ at hscalar
  rw [hscalar] at hBQ
  have hDQ : D.map (integralRationals p).subtype =
      taylor (-(p : ℚ) / 6) (clearedDenominator ℚ e) := by
    dsimp only [D, t]
    rw [Polynomial.map_taylor, clearedDenominator_map]
    change taylor (integralNode p (by omega)).val (clearedDenominator ℚ e) = _
    rw [integralNode_value]
  have hDen : (taylor (-(p : ℚ) / 6) (clearedDenominator ℚ e)).eval 0 ≠ 0 := by
    have h := hD0
    rw [evaluate_subtype, Subring.coe_zero, hDQ] at h
    exact h
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h := centered_double_factor_quotient (p : ℚ) hpq
    (B.map (integralRationals p).subtype)
    (taylor (-(p : ℚ) / 6) (clearedDenominator ℚ e)) hDen
  rw [← hBQ, quotientJet_taylor, quotientFullSecondJet_taylor] at h
  change quotientJet (clearedNumerator ℚ e) (clearedDenominator ℚ e)
        (-(p : ℚ) / 6) / (p : ℚ) -
      quotientFullSecondJet (clearedNumerator ℚ e) (clearedDenominator ℚ e)
        (-(p : ℚ) / 6) / 6 =
      (p : ℚ) * ((-8 * integralSixth p (by omega) ^ 2 * j).val)
  rw [← hDQ] at h
  rw [← hj] at h
  change _ = (p : ℚ) * (-8 * (1 / 6 : ℚ) ^ 2 * j.val)
  linear_combination h

theorem actual_top_first_divided_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    parameterJet (p - 1 - p / 6) (-(p : ℚ) / 6) / (p : ℚ) ∈ integralRationals p := by
  obtain ⟨r, hr⟩ := actual_top_first_second_ratio p hp
  let k : integralRationals p := ⟨nativeFullSecondJetCoefficient p (p - 1 - p / 6),
    nativeFullSecondJetCoefficient_integral p (by omega) _ (by omega)⟩
  let z := integralSixth p (by omega) * k + (p : integralRationals p) * r
  have hz : z.val = parameterJet (p - 1 - p / 6) (-(p : ℚ) / 6) / (p : ℚ) := by
    change (1 / 6 : ℚ) * nativeFullSecondJetCoefficient p (p - 1 - p / 6) +
      (p : ℚ) * r.val = _
    linear_combination -hr
  rw [← hz]
  exact z.property

/-- The actual rational top quotient reduces to the full K coefficient divided by six. -/
theorem actual_top_first_second_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((parameterJet (p - 1 - p / 6) (-(p : ℚ) / 6) / (p : ℚ) : ℚ) : ZMod p) =
      (nativeFullSecondJetCoefficient p (p - 1 - p / 6) : ZMod p) / 6 := by
  obtain ⟨r, hr⟩ := actual_top_first_second_ratio p hp
  let k : integralRationals p := ⟨nativeFullSecondJetCoefficient p (p - 1 - p / 6),
    nativeFullSecondJetCoefficient_integral p (by omega) _ (by omega)⟩
  let z := integralSixth p (by omega) * k + (p : integralRationals p) * r
  have hz : z.val = parameterJet (p - 1 - p / 6) (-(p : ℚ) / 6) / (p : ℚ) := by
    change (1 / 6 : ℚ) * nativeFullSecondJetCoefficient p (p - 1 - p / 6) +
      (p : ℚ) * r.val = _
    linear_combination -hr
  rw [← hz]
  change WPPIntegralReduction.residueHom p z = _
  simp only [z, map_add, map_mul, map_natCast, ZMod.natCast_self,
    zero_mul, add_zero, integralSixth_field]
  change (1 / 6 : ZMod p) * (nativeFullSecondJetCoefficient p (p - 1 - p / 6) : ZMod p) = _
  simp only [div_eq_mul_inv, one_mul, mul_comm]

/- The next attachment transports the proved J_e/p-K_e/6 integral p error
   through q=1-T² to the actual degree-2e coefficient. Together with the full
   two-node carry normalization, it fixes the actual quadratic Green top row
   at +4, using the retained R Wronskian for its leading coefficient.
   No field division by p, endpoint scalar, or factorial-value premise is used. -/

end WPMomentPrecision.TopNormalization
