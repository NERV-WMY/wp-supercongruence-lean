import WPActualPositivePair
import WPActualResidueVanishing

open scoped BigOperators LaurentPolynomial
open LaurentPolynomial WPActualEtaPrimitive WPActualEtaIntegrality WPLaurentIntegralResidue
open WPPIntegralReduction WPActualChiSource WPActualCanonicalSource WPActualEtaFieldCutoff

namespace WPActualFieldPrimitive

variable (p : ℕ) [Fact p.Prime]

/-- The literal field primitive, with precisely the original zero resonance slots. -/
noncomputable def fieldPrimitive (P : (ZMod p)[T;T⁻¹]) : (ZMod p)[T;T⁻¹] :=
  AddMonoidAlgebra.ofCoeff (Finsupp.onFinset (P.coeff.support.image (fun j => j + 1))
    (fun k : ℤ => if (p : ℤ) ∣ k then 0 else P.coeff (k - 1) / (k : ZMod p)) (by
      intro k hk
      have hP : P.coeff (k - 1) ≠ 0 := by
        intro h
        simp [h] at hk
      exact Finset.mem_image.mpr ⟨k - 1, Finsupp.mem_support_iff.mpr hP, by omega⟩))

theorem fieldPrimitive_coeff (P : (ZMod p)[T;T⁻¹]) (k : ℤ) :
    (fieldPrimitive p P).coeff k =
      if (p : ℤ) ∣ k then 0 else P.coeff (k - 1) / (k : ZMod p) := by
  simp only [fieldPrimitive, Finsupp.onFinset_apply]

noncomputable def fieldDerivative : (ZMod p)[T;T⁻¹] →ₗ[ZMod p] (ZMod p)[T;T⁻¹] :=
  (Finsupp.linearCombination (ZMod p) (fun n : ℤ => C (n : ZMod p) * T (n - 1))).comp
    (AddMonoidAlgebra.coeffLinearEquiv (ZMod p)).toLinearMap

theorem fieldDerivative_monomial (c : ZMod p) (n : ℤ) :
    fieldDerivative p (C c * T n) = C (c * (n : ZMod p)) * T (n - 1) := by
  rw [← single_eq_C_mul_T]
  change Finsupp.linearCombination (ZMod p) _ (Finsupp.single n c) = _
  rw [Finsupp.linearCombination_single, smul_eq_C_mul, ← mul_assoc, ← map_mul]

theorem fieldDerivative_coeff (P : (ZMod p)[T;T⁻¹]) (j : ℤ) :
    (fieldDerivative p P).coeff j = ((j + 1 : ℤ) : ZMod p) * P.coeff (j + 1) := by
  have hc (c : ZMod p) (n k : ℤ) : (C c * T n).coeff k = if n = k then c else 0 := by
    rw [← single_eq_C_mul_T]
    exact Finsupp.single_apply
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]
    ring
  | C_mul_T n c =>
    rw [fieldDerivative_monomial, hc, hc]
    by_cases hn : n = j + 1
    · subst n
      simp only [add_sub_cancel_right, if_true]
      ring
    · have hnj : n - 1 ≠ j := by omega
      simp only [if_neg hn, if_neg hnj, mul_zero]

noncomputable def fieldResonantSource (P : (ZMod p)[T;T⁻¹]) : (ZMod p)[T;T⁻¹] :=
  AddMonoidAlgebra.ofCoeff (P.coeff.filter (fun j => (p : ℤ) ∣ j + 1))

theorem fieldResonantSource_coeff (P : (ZMod p)[T;T⁻¹]) (j : ℤ) :
    (fieldResonantSource p P).coeff j = if (p : ℤ) ∣ j + 1 then P.coeff j else 0 :=
  Finsupp.filter_apply _ _ _

theorem fieldPrimitive_derivative (P : (ZMod p)[T;T⁻¹]) :
    fieldDerivative p (fieldPrimitive p P) = P - fieldResonantSource p P := by
  ext j
  rw [fieldDerivative_coeff, fieldPrimitive_coeff,
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, fieldResonantSource_coeff,
    show j + 1 - 1 = j by omega]
  by_cases hd : (p : ℤ) ∣ j + 1
  · simp [hd]
  · have hunit : ((j + 1 : ℤ) : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hd
    simp only [if_neg hd, sub_zero]
    field_simp [hunit]

theorem fieldPrimitive_resonant_zero (P : (ZMod p)[T;T⁻¹]) (k : ℤ) :
    (fieldPrimitive p P).coeff (k * p) = 0 := by
  rw [fieldPrimitive_coeff, if_pos (dvd_mul_left _ _)]

theorem fieldPrimitive_add (P Q : (ZMod p)[T;T⁻¹]) :
    fieldPrimitive p (P + Q) = fieldPrimitive p P + fieldPrimitive p Q := by
  ext j
  simp only [fieldPrimitive_coeff, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  split_ifs <;> ring

theorem fieldPrimitive_C_mul (c : ZMod p) (P : (ZMod p)[T;T⁻¹]) :
    fieldPrimitive p (C c * P) = C c * fieldPrimitive p P := by
  have hc (Q : (ZMod p)[T;T⁻¹]) (j : ℤ) : (C c * Q).coeff j = c * Q.coeff j := by
    rw [← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  ext j
  rw [fieldPrimitive_coeff, hc, hc, fieldPrimitive_coeff]
  split_ifs <;> ring

/-- Reduction of the actual integral rational primitive, with no rational cast ring-map premise. -/
theorem canonicalPrimitive_reduction (P : ℚ[T;T⁻¹]) (hP : P ∈ integralLaurent p) :
    reduceLaurent p (canonicalPrimitive p P) = fieldPrimitive p (reduceLaurent p P) := by
  ext j
  rw [reduceLaurent_coeff, fieldPrimitive_coeff, reduceLaurent_coeff, canonicalPrimitive_coeff]
  by_cases hd : (p : ℤ) ∣ j
  · simp only [if_pos hd, Rat.cast_zero]
  · simp only [if_neg hd]
    have hj : j ≠ 0 := by intro hz; simp [hz] at hd
    have hjq : (j : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hj
    have hcanon := canonicalPrimitive_integral p P hP j
    let a : integralRationals p := ⟨(canonicalPrimitive p P).coeff j, hcanon⟩
    let b : integralRationals p := ⟨P.coeff (j - 1), hP (j - 1)⟩
    have hprod : (j : integralRationals p) * a = b := by
      apply Subtype.ext
      change (j : ℚ) * (canonicalPrimitive p P).coeff j = P.coeff (j - 1)
      rw [canonicalPrimitive_coeff, if_neg hd]
      field_simp [hjq]
    have hm := congrArg (residueHom p) hprod
    simp only [map_mul, map_intCast] at hm
    change (j : ZMod p) * ((canonicalPrimitive p P).coeff j : ZMod p) =
      (P.coeff (j - 1) : ZMod p) at hm
    rw [canonicalPrimitive_coeff, if_neg hd] at hm
    have hunit : (j : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hd
    apply (eq_div_iff hunit).mpr
    simpa only [mul_comm] using hm

/-- The whole literal Peta field source, before selecting any primitive. -/
noncomputable def literalFieldPeta (_hp : 19 ≤ p) : (ZMod p)[T;T⁻¹] :=
  reduceLaurent p (WPActualEtaPole.Peta p ((p - 1) / 2) (p - 1 - p / 6))

theorem literal_field_Aeta_primitive (hp : 19 ≤ p) :
    literalFieldAeta p hp = fieldPrimitive p (literalFieldPeta p hp) := by
  have hP := actual_Peta_integral p (p - 1 - p / 6) (by omega) (by omega) (by
    have hd := Nat.div_mul_le_self p 6
    omega)
  have hc := canonicalPrimitive_reduction p _ hP
  have hA : literalFieldAeta p hp =
      reduceLaurent p (Aeta p ((p - 1) / 2) (p - 1 - p / 6)) := by
    ext j
    rw [literalFieldAeta_coeff, reduceLaurent_coeff]
  rw [hA]
  exact hc

theorem literal_field_Aeta_derivative (hp : 19 ≤ p) :
    fieldDerivative p (literalFieldAeta p hp) =
      literalFieldPeta p hp - fieldResonantSource p (literalFieldPeta p hp) := by
  rw [literal_field_Aeta_primitive, fieldPrimitive_derivative]

/-- All original field resonances except the actual central residue are zero. -/
theorem literal_field_resonant_source (hp : 19 ≤ p) :
    fieldResonantSource p (literalFieldPeta p hp) =
      C (WPActualEtaPrimitive.actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0 : ZMod p) *
        T (-1) := by
  have hz := WPActualResidueVanishing.literal_three_residues_zero p hp
  have hm (c : ZMod p) (n j : ℤ) : (C c * T n).coeff j = if n = j then c else 0 := by
    rw [← single_eq_C_mul_T]
    exact Finsupp.single_apply
  ext j
  rw [fieldResonantSource_coeff, literalFieldPeta, reduceLaurent_coeff, hm]
  by_cases hj : j = -1
  · subst j
    simp only [neg_add_cancel, dvd_zero, if_true, WPActualEtaPrimitive.actualResidue,
      zero_mul, zero_sub]
  · have hnj : -1 ≠ j := Ne.symm hj
    rw [if_neg hnj]
    by_cases hd : (p : ℤ) ∣ j + 1
    · rw [if_pos hd]
      by_cases hc : (WPActualEtaPole.Peta p ((p - 1) / 2) (p - 1 - p / 6)).coeff j = 0
      · rw [hc, Rat.cast_zero]
      · obtain ⟨k, hk, he⟩ := actual_cutoff_resonance_indices p hp j hc hd
        rcases hk with hk | hk | hk | hk
        · subst k
          rw [he]
          simpa only [WPActualEtaPrimitive.actualResidue, neg_one_mul] using hz.1
        · subst k
          simp only [zero_mul, zero_sub] at he
          exact (hj he).elim
        · subst k
          rw [he]
          simpa only [WPActualEtaPrimitive.actualResidue, one_mul] using hz.2.1
        · subst k
          rw [he]
          exact hz.2.2
    · rw [if_neg hd]

theorem literal_field_Aeta_central_source (hp : 19 ≤ p) :
    fieldDerivative p (literalFieldAeta p hp) = literalFieldPeta p hp -
      C (WPActualEtaPrimitive.actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0 : ZMod p) *
        T (-1) := by
  rw [literal_field_Aeta_derivative, literal_field_resonant_source]

end WPActualFieldPrimitive
