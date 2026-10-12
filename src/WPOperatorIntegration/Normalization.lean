import WPResidueFrobenius.Binomial
import WPCompletedCartier.InverseTraceConstruction

noncomputable section

namespace WPOperatorIntegration

open WPResidueQuotient

theorem laurentPhi_eq_cartier_phi {R : Type*} [CommRing R] (p : ℕ)
    (P : WPResidueQuotient.LaurentPolynomial R) :
    WPResidueFrobenius.laurentPhi R p P =
      WPCompletedCartier.NumericalTerms.phi p P := by
  induction P using AddMonoidAlgebra.induction_on with
  | of x =>
      change WPResidueFrobenius.laurentPhi R p (AddMonoidAlgebra.single x 1) =
        WPCompletedCartier.NumericalTerms.phi p (AddMonoidAlgebra.single x 1)
      rw [WPResidueFrobenius.laurentPhi_single,
        WPCompletedCartier.NumericalTerms.phi_single,
        WPCartierFinite.exponentScale_eq_nsmul]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
  | smul c P hP =>
      rw [WPResidueFrobenius.laurentPhi_smul, map_smul, hP]

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)

theorem actual_G_eq :
    WPResidueFrobenius.G p hp = WPCompletedCartier.NumericalTerms.G p hp := by
  have he : WPResidueFrobenius.frobeniusDifference p hp =
      (p : ℤ_[p]) • WPCompletedCartier.NumericalTerms.G p hp := by
    unfold WPResidueFrobenius.frobeniusDifference
    rw [laurentPhi_eq_cartier_phi]
    exact (WPCompletedCartier.NumericalTerms.G_scaled p hp).symm
  have hs : (p : ℤ_[p]) • WPResidueFrobenius.G p hp =
      (p : ℤ_[p]) • WPCompletedCartier.NumericalTerms.G p hp :=
    (WPResidueFrobenius.G_integral_identity p hp).symm.trans he
  apply AddMonoidAlgebra.coeff_injective
  ext x
  have hx := congrArg
    (fun P : WPResidueQuotient.LaurentPolynomial ℤ_[p] => P.coeff x) hs
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] at hx
  exact mul_left_cancel₀ (show (p : ℤ_[p]) ≠ 0 from
    Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hx

omit [Fact p.Prime] in
theorem pullbackScalar_normalization (j k : ℕ) :
    WPResidueFrobenius.pullbackScalar p (j + 1) k =
      (p : ℚ)^5 * (j.factorial : ℚ) *
        ((-1 : ℚ)^k * ((j + k).choose k : ℚ) * (p : ℚ)^k) /
          ((p * (j + k + 1) - 1).factorial : ℚ) := by
  have hchoose := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k j)
  have hc : ((j + k).factorial : ℚ) =
      ((j + k).choose k : ℚ) * (k.factorial : ℚ) * (j.factorial : ℚ) := by
    simpa only [Nat.add_sub_cancel, Nat.cast_mul] using
      (congrArg (fun n : ℕ => (n : ℚ)) hchoose).symm
  have hindex : j + 1 + k = j + k + 1 := by omega
  have hfactor : j + 1 + k - 1 = j + k := by omega
  unfold WPResidueFrobenius.pullbackScalar
  rw [hfactor, hindex, hc, pow_add]
  field_simp [show (k.factorial : ℚ) ≠ 0 from
    by exact_mod_cast Nat.factorial_ne_zero k,
    show ((p * (j + k + 1) - 1).factorial : ℚ) ≠ 0 from
      by exact_mod_cast Nat.factorial_ne_zero (p * (j + k + 1) - 1)]

theorem actual_pullbackScalar_normalization (j : Fin 5) (k : ℕ) :
    (WPResidueFrobenius.pullbackScalar p (j.val + 1) k : ℚ_[p]) =
      (p : ℚ_[p])^5 * (j.val.factorial : ℚ_[p]) *
        (WPCompletedCartier.InverseTraceConstruction.inputCoefficient p j k : ℚ_[p]) /
          ((WPCompletedCartier.InverseTraceConstruction.inputIndex p j k).factorial : ℚ_[p]) := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[p]))
    (pullbackScalar_normalization p j.val k)
  simpa only [WPCompletedCartier.InverseTraceConstruction.inputCoefficient,
    WPCompletedCartier.InverseTraceConstruction.inputIndex,
    WPCompletedCartier.InverseTraceConstruction.inputHeight,
    Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_neg, Rat.cast_one, PadicInt.coe_mul, PadicInt.coe_pow,
    PadicInt.coe_natCast, PadicInt.coe_neg, PadicInt.coe_one] using h

end WPOperatorIntegration
