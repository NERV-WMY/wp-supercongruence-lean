import WPFieldAssembly.NativeOriginalResidues
import WPFirstResidue.NC59Export
import WPActualNativeCanonicalPart

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial WPPIntegralReduction WPActualPullbackSource WPActualEtaPole
  WPActualCentralResidueSource WPActualNativeJetODE WPActualNativeCanonicalPart
  WPFieldAssembly.NativeFullGreen WPFieldAssembly.NativeOriginalResidues
  WPFieldAssembly.ActualNC77Chart WPFieldAssembly.OriginalLaurentDensity
  WPFieldAssembly.ResidualProjection

namespace WPFieldAssembly.ActualR0Node
set_option maxHeartbeats 1200000

noncomputable def unitEuler {K : Type*} [Field K] (p : ℕ) (G : K[X]) : K[X] :=
  ∑ n ∈ Finset.range p, monomial n (G.coeff n / (n : K))

theorem unitEuler_coeff {K : Type*} [Field K] (p : ℕ) (G : K[X]) (n : ℕ) :
    (unitEuler p G).coeff n = if n < p then G.coeff n / (n : K) else 0 := by
  classical
  simp only [unitEuler, finsetSum_coeff, coeff_monomial]
  by_cases hn : n < p
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro m _ hmn; simp [hmn]
    · simp [Finset.mem_range, hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro m hm
    have hmn : m ≠ n := by have := Finset.mem_range.mp hm; omega
    simp [hmn]

theorem unitEuler_add {K : Type*} [Field K] (p : ℕ) (A B : K[X]) :
    unitEuler p (A + B) = unitEuler p A + unitEuler p B := by
  ext n
  simp only [unitEuler_coeff, coeff_add]
  by_cases hn : n < p <;> simp [hn, add_div]

theorem unitEuler_C_mul {K : Type*} [Field K] (p : ℕ) (a : K) (G : K[X]) :
    unitEuler p (C a * G) = C a * unitEuler p G := by
  ext n
  rw [unitEuler_coeff, coeff_C_mul, coeff_C_mul, unitEuler_coeff]
  by_cases hn : n < p <;> simp [hn, mul_div_assoc]

theorem unitEuler_native (p e : ℕ) (he : e < p) :
    unitEuler p (WPReview.nativePolynomial (e + 1)) = Hpolynomial e := by
  ext n
  rw [unitEuler_coeff, WPReview.nativePolynomial_coeff, Hpolynomial_coeff]
  by_cases hn : n < e + 1
  · have hnp : n < p := by omega
    simp [hn, hnp]
  · simp [hn]

theorem unitEuler_field_eq (p : ℕ) [Fact p.Prime] (G : (ZMod p)[X])
    (hG : G.natDegree < p) :
    unitEuler p G = WPActualPositivePair.eulerPrimitive p G := by
  ext n
  rw [unitEuler_coeff, WPActualPositivePair.eulerPrimitive_coeff]
  by_cases hn : n < p
  · rw [if_pos hn]
  · rw [if_neg hn, coeff_eq_zero_of_natDegree_lt (by omega), zero_div]

variable (p : ℕ) [Fact p.Prime]

noncomputable def indexInverse (_hp : 19 ≤ p) (n : Fin p) : integralRationals p :=
  ⟨1 / (n.val : ℚ), by
    by_cases hn : n.val = 0
    · simp [hn]
    · exact WPFiniteConductorPolynomial.small_inverse_integral p n.val
        (by omega) (by have := n.isLt; omega)⟩

theorem indexInverse_value (hp : 19 ≤ p) (n : Fin p) :
    (indexInverse p hp n).val = 1 / (n.val : ℚ) := rfl

theorem indexInverse_field (hp : 19 ≤ p) (n : Fin p) :
    residueHom p (indexInverse p hp n) = 1 / (n.val : ZMod p) := by
  change (((1 / (n.val : ℚ) : ℚ) : ZMod p)) = _
  simpa only [one_div] using (Rat.cast_inv_nat (α := ZMod p) n.val)

noncomputable def unitEulerIntegral (hp : 19 ≤ p)
    (G : (integralRationals p)[X]) : (integralRationals p)[X] :=
  ∑ n : Fin p, monomial n.val (G.coeff n.val * indexInverse p hp n)

theorem unitEulerIntegral_value (hp : 19 ≤ p) (G : (integralRationals p)[X]) :
    (unitEulerIntegral p hp G).map (integralRationals p).subtype =
      unitEuler p (G.map (integralRationals p).subtype) := by
  simp only [unitEulerIntegral, Polynomial.map_sum, map_monomial, _root_.map_mul,
    Subring.coe_subtype, indexInverse_value]
  simpa only [unitEuler, coeff_map, Subring.coe_subtype, div_eq_mul_inv, one_mul] using
    (Fin.sum_univ_eq_sum_range
      (fun n => monomial n ((G.map (integralRationals p).subtype).coeff n / (n : ℚ))) p)

theorem unitEulerIntegral_field (hp : 19 ≤ p) (G : (integralRationals p)[X]) :
    (unitEulerIntegral p hp G).map (residueHom p) =
      unitEuler p (G.map (residueHom p)) := by
  simp only [unitEulerIntegral, Polynomial.map_sum, map_monomial, _root_.map_mul,
    indexInverse_field]
  simpa only [unitEuler, coeff_map, div_eq_mul_inv, one_mul] using
    (Fin.sum_univ_eq_sum_range
      (fun n => monomial n ((G.map (residueHom p)).coeff n / (n : ZMod p))) p)

noncomputable def eulerValueIntegral (hp : 19 ≤ p) (G : (integralRationals p)[X]) :
    integralRationals p :=
  (unitEulerIntegral p hp G).eval (4 * inverse125 p hp)

theorem eulerValueIntegral_value (hp : 19 ≤ p) (G : (integralRationals p)[X]) :
    (eulerValueIntegral p hp G).val =
      (unitEuler p (G.map (integralRationals p).subtype)).eval (4 / 125 : ℚ) := by
  change (integralRationals p).subtype
    ((unitEulerIntegral p hp G).eval (4 * inverse125 p hp)) = _
  rw [← eval_map_apply, unitEulerIntegral_value]
  congr 1
  change (4 : ℚ) * (1 / 125) = 4 / 125
  ring

theorem eulerValueIntegral_field (hp : 19 ≤ p) (G : (integralRationals p)[X]) :
    residueHom p (eulerValueIntegral p hp G) =
      (unitEuler p (G.map (residueHom p))).eval (4 / 125 : ZMod p) := by
  rw [eulerValueIntegral, ← eval_map_apply, unitEulerIntegral_field]
  congr 1
  rw [_root_.map_mul, _root_.map_ofNat, inverse125_field]
  ring

theorem projectionIntegral_original_value (hp : 19 ≤ p) (j : ℕ)
    (G : (integralRationals p)[X]) :
    (projectionIntegral p hp j G).val = O p j (G.map (integralRationals p).subtype) := by
  rw [O_eq_Ij, projectionIntegral_value]

noncomputable def r0NodeBaseline : ℚ :=
  -2 * O p 0 (mixedQ p) - (1 / 2 : ℚ) *
    (unitEuler p (squareQ p)).eval (4 / 125 : ℚ)

/-- Both the node lift and the integer Fermat quotient lift remain over Q. -/
noncomputable def actualDeltaU : ℚ :=
  r0NodeBaseline p - WPFirstResidue.LiteralNormalization.literalR0 p

noncomputable def actualDeltaUDigit : ℚ := actualDeltaU p / (p : ℚ)

noncomputable def r0NodeBaselineIntegral (hp : 19 ≤ p) : integralRationals p :=
  -2 * projectionIntegral p hp 0 (integralMixedQ p (by omega)) -
    WPFirstResidue.LiteralNormalization.integralHalf p hp *
      eulerValueIntegral p hp (squareQIntegral p hp)

noncomputable def actualDeltaUIntegral (hp : 19 ≤ p) : integralRationals p :=
  r0NodeBaselineIntegral p hp -
    WPFirstResidue.LiteralNormalization.integralLiteralR0 p hp

noncomputable def actualR0Integral (hp : 19 ≤ p) : integralRationals p :=
  ⟨WPFirstResidue.LiteralNormalization.actualFirstResidue p,
    WPFirstResidue.LiteralNormalization.actualFirstResidue_integral p hp⟩

theorem r0NodeBaselineIntegral_value (hp : 19 ≤ p) :
    (r0NodeBaselineIntegral p hp).val = r0NodeBaseline p := by
  change -2 * (projectionIntegral p hp 0 (integralMixedQ p (by omega))).val -
    (1 / 2 : ℚ) * (eulerValueIntegral p hp (squareQIntegral p hp)).val = _
  rw [projectionIntegral_original_value, integralMixedQ_value,
    eulerValueIntegral_value, squareQIntegral_value]
  rfl

theorem actualDeltaUIntegral_value (hp : 19 ≤ p) :
    (actualDeltaUIntegral p hp).val = actualDeltaU p := by
  change (r0NodeBaselineIntegral p hp).val -
    (WPFirstResidue.LiteralNormalization.integralLiteralR0 p hp).val = _
  rw [r0NodeBaselineIntegral_value,
    WPFirstResidue.LiteralNormalization.integralLiteralR0_value]
  rfl

theorem actual_deltaU_integral (hp : 19 ≤ p) :
    actualDeltaU p ∈ integralRationals p := by
  rw [← actualDeltaUIntegral_value p hp]
  exact (actualDeltaUIntegral p hp).property

/-- Whole rational r0 transport, retaining the full correction's Euler primitive. -/
theorem actual_r0_node_source (hp : 19 ≤ p) :
    WPFirstResidue.LiteralNormalization.actualFirstResidue p =
      r0NodeBaseline p - (p : ℚ) *
        ((unitEuler p (mixedQ p)).eval (4 / 125 : ℚ) + O p 0 (fullCq p hp)) -
      (p : ℚ) ^ 2 / 2 * (unitEuler p (fullCq p hp)).eval (4 / 125 : ℚ) := by
  have hpq : (p : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he : fullCutoff p < p := by
    dsimp [fullCutoff]
    have := (Fact.out : p.Prime).pos
    omega
  have hr := actual_central_residue_formula p ((p - 1) / 2) (fullCutoff p)
  rw [actual_HX_constant] at hr
  have hR : WPFirstResidue.LiteralNormalization.actualFirstResidue p =
      -(1 / 2 : ℚ) * (Hpolynomial (fullCutoff p)).eval (4 / 125 : ℚ) -
        (1 / (p : ℚ)) * O p 0 (WPReview.nativePolynomial (fullCutoff p + 1)) := by
    simpa only [WPFirstResidue.LiteralNormalization.actualFirstResidue,
      fullCutoff, O, Fpull, Nat.cast_zero, neg_zero, zero_mul, zero_sub] using hr
  have hH : (Hpolynomial (fullCutoff p)).eval (4 / 125 : ℚ) =
      (unitEuler p (squareQ p)).eval (4 / 125 : ℚ) +
      (2 * (p : ℚ)) * (unitEuler p (mixedQ p)).eval (4 / 125 : ℚ) +
      (p : ℚ) ^ 2 * (unitEuler p (fullCq p hp)).eval (4 / 125 : ℚ) := by
    rw [← unitEuler_native p (fullCutoff p) he, actual_full_native_q_source p hp]
    simp only [unitEuler_add, unitEuler_C_mul, eval_add, eval_mul, eval_C]
  have hO : O p 0 (WPReview.nativePolynomial (fullCutoff p + 1)) =
      2 * (p : ℚ) * O p 0 (mixedQ p) + (p : ℚ) ^ 2 * O p 0 (fullCq p hp) := by
    simpa only [O_eq_Ij] using actual_full_native_projection p hp 0
  rw [hR, hH, hO, r0NodeBaseline]
  field_simp [hpq]
  ring

/-- Integral witness for the entire rational source, before p is divided. -/
theorem actual_r0_node_integral_source (hp : 19 ≤ p) :
    actualR0Integral p hp = r0NodeBaselineIntegral p hp -
      (p : integralRationals p) *
        (eulerValueIntegral p hp (integralMixedQ p (by omega)) +
          projectionIntegral p hp 0 (fullCqIntegral p hp)) -
      (p : integralRationals p) ^ 2 *
        WPFirstResidue.LiteralNormalization.integralHalf p hp *
          eulerValueIntegral p hp (fullCqIntegral p hp) := by
  apply Subtype.ext
  change WPFirstResidue.LiteralNormalization.actualFirstResidue p =
    (r0NodeBaselineIntegral p hp).val - (p : ℚ) *
      ((eulerValueIntegral p hp (integralMixedQ p (by omega))).val +
        (projectionIntegral p hp 0 (fullCqIntegral p hp)).val) -
    (p : ℚ) ^ 2 * (1 / 2 : ℚ) *
      (eulerValueIntegral p hp (fullCqIntegral p hp)).val
  rw [r0NodeBaselineIntegral_value, eulerValueIntegral_value,
    integralMixedQ_value, projectionIntegral_original_value, eulerValueIntegral_value]
  change WPFirstResidue.LiteralNormalization.actualFirstResidue p =
    r0NodeBaseline p - (p : ℚ) *
      ((unitEuler p (mixedQ p)).eval (4 / 125 : ℚ) + O p 0 (fullCq p hp)) -
    (p : ℚ) ^ 2 * (1 / 2 : ℚ) *
      (unitEuler p (fullCq p hp)).eval (4 / 125 : ℚ)
  convert actual_r0_node_source p hp using 1; ring

theorem actual_deltaU_residue_zero (hp : 19 ≤ p) :
    residueHom p (actualDeltaUIntegral p hp) = 0 := by
  have h := congrArg (residueHom p) (actual_r0_node_integral_source p hp)
  simp only [_root_.map_sub, _root_.map_mul, _root_.map_add, _root_.map_pow, _root_.map_natCast,
    ZMod.natCast_self, zero_mul,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at h
  have hlit : residueHom p (actualR0Integral p hp) =
      residueHom p (WPFirstResidue.LiteralNormalization.integralLiteralR0 p hp) := by
    change (WPFirstResidue.LiteralNormalization.actualFirstResidue p : ZMod p) =
      ((WPFirstResidue.LiteralNormalization.integralLiteralR0 p hp).val : ZMod p)
    rw [WPFirstResidue.LiteralNormalization.integralLiteralR0_value]
    exact WPFirstResidue.NativeResidue.actual_first_residue_literal_field p hp
  change residueHom p (r0NodeBaselineIntegral p hp -
    WPFirstResidue.LiteralNormalization.integralLiteralR0 p hp) = 0
  rw [_root_.map_sub, ← h]
  exact sub_eq_zero.mpr hlit

theorem actual_deltaU_digit_integral (hp : 19 ≤ p) :
    actualDeltaUDigit p ∈ integralRationals p := by
  unfold actualDeltaUDigit
  apply WPActualChiSource.divide_prime_integral p _
  · exact actual_deltaU_integral p hp
  · rw [← actualDeltaUIntegral_value p hp]
    change residueHom p (actualDeltaUIntegral p hp) = 0
    exact actual_deltaU_residue_zero p hp

noncomputable def integralDeltaUDigit (hp : 19 ≤ p) : integralRationals p :=
  ⟨actualDeltaUDigit p, actual_deltaU_digit_integral p hp⟩

theorem integralDeltaUDigit_value (hp : 19 ≤ p) :
    (integralDeltaUDigit p hp).val = actualDeltaU p / (p : ℚ) := rfl

/-- Source-relative rho over Q, with its p times integral primitive retained. -/
theorem actual_rho_node_source (hp : 19 ≤ p) :
    WPFirstResidue.actualRho p = actualDeltaUDigit p -
      (unitEuler p (mixedQ p)).eval (4 / 125 : ℚ) - O p 0 (fullCq p hp) -
      (p : ℚ) / 2 * (unitEuler p (fullCq p hp)).eval (4 / 125 : ℚ) := by
  have hpq : (p : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold WPFirstResidue.actualRho actualDeltaUDigit actualDeltaU
  rw [actual_r0_node_source p hp]
  field_simp [hpq]
  ring

theorem actual_rho_node_integral_source (hp : 19 ≤ p) :
    WPFirstResidue.integralActualRho p hp = integralDeltaUDigit p hp -
      eulerValueIntegral p hp (integralMixedQ p (by omega)) -
      projectionIntegral p hp 0 (fullCqIntegral p hp) -
      (p : integralRationals p) *
        WPFirstResidue.LiteralNormalization.integralHalf p hp *
          eulerValueIntegral p hp (fullCqIntegral p hp) := by
  apply Subtype.ext
  change WPFirstResidue.actualRho p = actualDeltaUDigit p -
    (eulerValueIntegral p hp (integralMixedQ p (by omega))).val -
    (projectionIntegral p hp 0 (fullCqIntegral p hp)).val -
    (p : ℚ) * (1 / 2 : ℚ) * (eulerValueIntegral p hp (fullCqIntegral p hp)).val
  rw [eulerValueIntegral_value, integralMixedQ_value,
    projectionIntegral_original_value, eulerValueIntegral_value]
  change WPFirstResidue.actualRho p = actualDeltaUDigit p -
    (unitEuler p (mixedQ p)).eval (4 / 125 : ℚ) - O p 0 (fullCq p hp) -
    (p : ℚ) * (1 / 2 : ℚ) * (unitEuler p (fullCq p hp)).eval (4 / 125 : ℚ)
  convert actual_rho_node_source p hp using 1; ring

/-- The exact 12 YU normalization is transported through the entire primitive. -/
theorem actual_mixed_euler_value_scale (hp : 19 ≤ p) :
    (12 : ZMod p) * residueHom p
      (eulerValueIntegral p hp (integralMixedQ p (by omega))) =
      (nativeHJet p).eval (4 / 125 : ZMod p) := by
  have h := congrArg (unitEuler p) (actual_mixed_field_source p hp)
  have hJ : unitEuler p (nativeJetField p) = nativeHJet p := by
    change unitEuler p (nativeJetField p) =
      WPActualPositivePair.eulerPrimitive p (nativeJetField p)
    apply unitEuler_field_eq
    have hd := nativeJetField_degree p
    omega
  simp only [show (12 : (ZMod p)[X]) = C (12 : ZMod p) from rfl,
    unitEuler_C_mul] at h
  rw [hJ] at h
  have hv := congrArg (fun P : (ZMod p)[X] => P.eval (4 / 125 : ZMod p)) h
  simp only [eval_mul, eval_C] at hv
  rw [eulerValueIntegral_field]
  exact hv

theorem actual_mixed_euler_value (hp : 19 ≤ p) :
    residueHom p (eulerValueIntegral p hp (integralMixedQ p (by omega))) =
      (nativeHJet p).eval (4 / 125 : ZMod p) / 12 := by
  have h12 : (12 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 12 (by omega) (by omega)
  apply (eq_div_iff h12).mpr
  simpa only [mul_comm] using actual_mixed_euler_value_scale p hp

/-- Actual rho correction: full norm retained until the separately proved IR28 drop. -/
theorem actual_rho_norm_source (hp : 19 ≤ p) :
    residueHom p (WPFirstResidue.integralActualRho p hp) =
      residueHom p (integralDeltaUDigit p hp) -
        (nativeHJet p).eval (4 / 125 : ZMod p) / 12 -
        6 * Ij p 0 ((integralNormQ p (by omega)).map (residueHom p)) := by
  have h := congrArg (residueHom p) (actual_rho_node_integral_source p hp)
  simp only [_root_.map_sub, _root_.map_mul, _root_.map_natCast, ZMod.natCast_self,
    zero_mul, sub_zero] at h
  rw [actual_mixed_euler_value p hp, projectionIntegral_field,
    actual_full_projection_drop p hp 0] at h
  exact h

end WPFieldAssembly.ActualR0Node
