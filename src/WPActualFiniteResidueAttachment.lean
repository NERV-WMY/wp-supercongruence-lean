import WPLaurentResidue
import WPGeometricResidue
import WPNativeFiniteExpansion
import WPActualTensorContraction
import WPActualNativeConnection

open scoped LaurentSeries BigOperators
open HahnSeries Polynomial

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 1500000

theorem actual_laurent_s :
    algebraMap (RatFunc (RatFunc ℚ)) (LaurentSeries (RatFunc ℚ)) bivS =
      single (1 : ℤ) 1 := RatFunc.coe_X

theorem actual_laurent_b :
    algebraMap (RatFunc (RatFunc ℚ)) (LaurentSeries (RatFunc ℚ)) bivB =
      single (-1 : ℤ) lambda := by
  rw [bivB, bivLambda, map_div₀, rational_laurent_coefficient, actual_laurent_s]
  simp only [div_eq_mul_inv, HahnSeries.C_apply,
    HahnSeries.inv_single, inv_one, single_mul_single, zero_add, mul_one]

theorem actual_laurent_mixed_power (a b : ℕ) :
    algebraMap (RatFunc (RatFunc ℚ)) (LaurentSeries (RatFunc ℚ))
      (bivS^a*bivB^b) = single ((a : ℤ)-(b : ℤ)) (lambda^b) := by
  simp only [map_mul, map_pow, actual_laurent_s, actual_laurent_b,
    single_pow, nsmul_eq_mul, one_pow, mul_one, single_mul_single, one_mul]
  congr 1
  ring

theorem actual_mixed_pole_residue (a b : ℕ) (c : RatFunc ℚ) (hc : c≠0) :
    rationalResidue (bivS^a*bivB^b/(bivS-RatFunc.C c)) =
      if a<b then -(lambda^b*(c⁻¹)^(b-a)) else 0 := by
  rw [rationalResidue, laurentResidue, map_div₀,
    actual_laurent_mixed_power, map_sub, actual_laurent_s, rational_laurent_coefficient]
  simp only [
    div_eq_mul_inv]
  exact geometric_pole_residue a b lambda c hc

theorem actual_unit_pole_residue (a b : ℕ) :
    rationalResidue (bivS^a*bivB^b/(bivS-1)) =
      if a<b then -lambda^b else 0 := by
  simpa using actual_mixed_pole_residue a b 1 one_ne_zero

theorem actual_diagonal_pole_residue (a b : ℕ) :
    rationalResidue (bivS^a*bivB^b/(bivS-bivLambda)) =
      if a<b then -lambda^a else 0 := by
  have hl : lambda ≠ 0 := by
    unfold lambda
    exact mul_ne_zero (by norm_num) (pow_ne_zero _
      (RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero))
  rw [rationalResidue, laurentResidue, map_div₀, actual_laurent_mixed_power,
    map_sub, actual_laurent_s, bivLambda, rational_laurent_coefficient]
  simp only [div_eq_mul_inv]
  exact geometric_diagonal_pole_residue a b lambda hl

/-- The complete rectangular sum is reduced by the actual Laurent chamber. -/
theorem actual_finite_pole_residue (p : ℕ) (A B : ℕ → RatFunc ℚ)
    (c : RatFunc ℚ) (hc : c≠0) :
    rationalResidue
      ((∑ a ∈ Finset.range p, RatFunc.C (A a)*bivS^a)*
        (∑ b ∈ Finset.range p, RatFunc.C (B b)*bivB^b)/(bivS-RatFunc.C c)) =
      ∑ a ∈ Finset.range p, ∑ b ∈ Finset.range p,
        A a*B b*(if a<b then -(lambda^b*(c⁻¹)^(b-a)) else 0) := by
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_div, rationalResidue_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have ht : RatFunc.C (A a)*bivS^a*(RatFunc.C (B b)*bivB^b)/(bivS-RatFunc.C c) =
      RatFunc.C (A a*B b)*(bivS^a*bivB^b/(bivS-RatFunc.C c)) := by
    rw [map_mul]
    ring
  rw [ht, rationalResidue_coefficient_mul, actual_mixed_pole_residue a b c hc]

theorem finite_prefix_chamber (p b : ℕ) (hb : b≤p) (A : ℕ → RatFunc ℚ) :
    (∑ a ∈ Finset.range p, if a<b then A a else 0) =
      ∑ a ∈ Finset.range b, A a := by
  classical
  have hs : Finset.range b ⊆ Finset.range p := Finset.range_mono hb
  calc
    _ = ∑ a ∈ Finset.range b, if a<b then A a else 0 := by
      symm
      apply Finset.sum_subset hs
      intro a ha hab
      have h : ¬a<b := by simpa only [Finset.mem_range] using hab
      simp [h]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [if_pos (Finset.mem_range.mp ha)]

theorem finite_tail_chamber (p a : ℕ) (A : ℕ → RatFunc ℚ) :
    (∑ b ∈ Finset.range p, if a<b then A b else 0) =
      ∑ b ∈ Finset.Ico (a+1) p, A b := by
  classical
  have hs : Finset.Ico (a+1) p ⊆ Finset.range p := by
    intro b hb
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hb).2
  calc
    _ = ∑ b ∈ Finset.Ico (a+1) p, if a<b then A b else 0 := by
      symm
      apply Finset.sum_subset hs
      intro b hb hab
      have h : ¬a<b := by
        have hb' := Finset.mem_range.mp hb
        simp only [Finset.mem_Ico, not_and] at hab
        omega
      simp [h]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [if_pos (by have := (Finset.mem_Ico.mp hb).1; omega)]

theorem finite_first_residue_triangle (p : ℕ) (A B : ℕ → RatFunc ℚ) :
    (∑ a ∈ Finset.range p, ∑ b ∈ Finset.range p,
      A a*B b*(if a<b then -lambda^b else 0)) =
      -(∑ b ∈ Finset.range p, B b*lambda^b*∑ a ∈ Finset.range b, A a) := by
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    _ = ∑ a ∈ Finset.range p, (-B b*lambda^b)*(if a<b then A a else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> ring
    _ = (-B b*lambda^b)*(∑ a ∈ Finset.range p, if a<b then A a else 0) :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := by
      rw [finite_prefix_chamber p b (by have := Finset.mem_range.mp hb; omega)]
      ring

theorem finite_second_residue_triangle (p : ℕ) (A B : ℕ → RatFunc ℚ) :
    (∑ a ∈ Finset.range p, ∑ b ∈ Finset.range p,
      A a*B b*(if a<b then -lambda^a else 0)) =
      -(∑ a ∈ Finset.range p, A a*lambda^a*∑ b ∈ Finset.Ico (a+1) p, B b) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    _ = ∑ b ∈ Finset.range p, (-A a*lambda^a)*(if a<b then B b else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      split_ifs <;> ring
    _ = (-A a*lambda^a)*(∑ b ∈ Finset.range p, if a<b then B b else 0) :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := by
      rw [finite_tail_chamber]
      ring

theorem outer_native_scalar (q : ℚ) :
    algebraMap ℚ (RatFunc (RatFunc ℚ)) q = RatFunc.C (RatFunc.C q) := by
  have h : RatFunc.C q = (q : RatFunc ℚ) := by
    simpa only [Rat.cast_id] using map_ratCast (RatFunc.C : ℚ →+* RatFunc ℚ) q
  calc
    _ = (q : RatFunc (RatFunc ℚ)) := by
      simpa only [Rat.cast_id] using
        map_ratCast (algebraMap ℚ (RatFunc (RatFunc ℚ))) q
    _ = RatFunc.C (q : RatFunc ℚ) :=
      (map_ratCast (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) q).symm
    _ = _ := congrArg RatFunc.C h.symm

noncomputable def actualWeightedNativeJet (p : ℕ) (q : RatFunc (RatFunc ℚ)) :
    RatFunc (RatFunc ℚ) :=
  (5/72)*finiteNativeJet p q 0 + (23/36)*finiteNativeJet p q 1 +
    (3/2)*finiteNativeJet p q 2

theorem actual_first_native_residue (p : ℕ) (j : Fin 3) :
    rationalResidue (actualWeightedNativeJet p bivS*finiteNativeJet p bivB j/(bivS-1)) =
      pullbackValue (angularFirst p j.val) := by
  rw [actualWeightedNativeJet, finite_native_weighted_sum, finite_native_jet_sum]
  simp only [outer_native_scalar]
  have h := actual_finite_pole_residue p
    (fun a => RatFunc.C (nativeBoundaryWeight a*WPReview.nativeCoefficient a))
    (fun b => RatFunc.C ((b : ℚ)^j.val*WPReview.nativeCoefficient b)) 1 one_ne_zero
  simp only [map_one, inv_one, one_pow, mul_one] at h
  rw [h, finite_first_residue_triangle]
  change _ = pullbackHom (angularFirst p j.val)
  simp only [angularFirst, map_neg, map_sum, pullbackHom_apply,
    pullbackValue_monomial, map_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem actual_second_native_residue (p : ℕ) (i : Fin 3) :
    rationalResidue (finiteNativeJet p bivS i*actualWeightedNativeJet p bivB/
      (bivS-bivLambda)) = pullbackValue (angularSecond p i.val) := by
  rw [actualWeightedNativeJet, finite_native_weighted_sum, finite_native_jet_sum]
  simp only [outer_native_scalar]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_div, rationalResidue_sum]
  have h (a b : ℕ) :
      rationalResidue
        (RatFunc.C (RatFunc.C ((a : ℚ)^i.val*WPReview.nativeCoefficient a))*bivS^a*
          (RatFunc.C (RatFunc.C (nativeBoundaryWeight b*WPReview.nativeCoefficient b))*
            bivB^b)/(bivS-bivLambda)) =
        RatFunc.C ((a : ℚ)^i.val*WPReview.nativeCoefficient a)*
          RatFunc.C (nativeBoundaryWeight b*WPReview.nativeCoefficient b)*
            (if a<b then -lambda^a else 0) := by
    have ht : RatFunc.C (RatFunc.C ((a : ℚ)^i.val*WPReview.nativeCoefficient a))*bivS^a*
        (RatFunc.C (RatFunc.C (nativeBoundaryWeight b*WPReview.nativeCoefficient b))*
          bivB^b)/(bivS-bivLambda) =
        RatFunc.C (RatFunc.C ((a : ℚ)^i.val*WPReview.nativeCoefficient a)*
          RatFunc.C (nativeBoundaryWeight b*WPReview.nativeCoefficient b))*
            (bivS^a*bivB^b/(bivS-bivLambda)) := by
      simp only [map_mul]
      ring
    rw [ht, rationalResidue_coefficient_mul, actual_diagonal_pole_residue]
  simp_rw [h]
  rw [finite_second_residue_triangle]
  change _ = pullbackHom (angularSecond p i.val)
  simp only [angularSecond, map_neg, map_sum, pullbackHom_apply,
    pullbackValue_monomial, map_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem actual_normal_source_pairing_split (p : ℕ) :
    actualTensorPairing p bivNormalSource =
      (∑ j : Fin 3, RatFunc.C (sourceEntry ⟨j.val, by omega⟩)*
        (actualWeightedNativeJet p bivS*finiteNativeJet p bivB j/(bivS-1))) +
      (∑ i : Fin 3, RatFunc.C (sourceEntry ⟨i.val+3, by omega⟩)*
        (finiteNativeJet p bivS i*actualWeightedNativeJet p bivB/(bivS-bivLambda))) := by
  simp only [actualTensorPairing, bivNormalSource, actualNativeTensor,
    actualWeightedNativeJet, bivWeight, Fin.sum_univ_succ]
  norm_num
  have hw : (![5/72, 23/36, 3/2] : Fin 3 → RatFunc (RatFunc ℚ)) 2 = 3/2 := rfl
  simp only [hw]
  ring

/-- Both normal-form residue blocks attach to the literal finite angular state. -/
theorem actual_normal_source_residue_attachment (p : ℕ) :
    rationalResidue (actualTensorPairing p bivNormalSource) = nativeAngularSource p := by
  rw [actual_normal_source_pairing_split, rationalResidue_add]
  simp only [rationalResidue_sum, rationalResidue_coefficient_mul,
    actual_first_native_residue, actual_second_native_residue]
  norm_num [nativeAngularSource, angularSixState, Fin.sum_univ_succ]
  dsimp only [Fin.succ]
  norm_num
  have he2 : (⟨2, by omega⟩ : Fin 6) = 2 := by ext; norm_num
  rw [he2]
  ring

end

end WPForcedSourceStokes
