import WPResidueFrobenius.CommonPole
import Mathlib.Topology.Algebra.InfiniteSum.Module

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators Topology
open WPResidueQuotient

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

theorem rawPullbackTerm_add (r k : ℕ) (hr : 1 ≤ r)
    (P Q : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) (hQ : Q ∈ numeratorFiltration ℤ_[p] r) :
    rawPullbackTerm p hp r k hr (P+Q) ((numeratorFiltration ℤ_[p] r).add_mem hP hQ) =
      rawPullbackTerm p hp r k hr P hP + rawPullbackTerm p hp r k hr Q hQ := by
  apply Subtype.ext
  simp only [Submodule.coe_add, rawPullbackTerm_coe, numericalPhi, map_add]
  ring

theorem rawIntegralGenerator_smul (r k : ℕ) (hr : 1 ≤ r)
    (c : ℤ_[p]) (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    rawIntegralGenerator p hp r k hr (c • P) ((numeratorFiltration ℤ_[p] r).smul_mem c hP) =
      c • rawIntegralGenerator p hp r k hr P hP := by
  apply Subtype.ext
  change factorialNumeratorMap _ _ (pullbackNumerator p hp (c • P) k) =
    c • factorialNumeratorMap _ _ (pullbackNumerator p hp P k)
  rw [pullbackNumerator, laurentPhi_smul, smul_mul_assoc, map_smul]
  rfl

theorem rawPullbackTerm_smul (r k : ℕ) (hr : 1 ≤ r)
    (c : ℤ_[p]) (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    rawPullbackTerm p hp r k hr (c • P) ((numeratorFiltration ℤ_[p] r).smul_mem c hP) =
      IntegralTransport.padicCoefficientMap p c • rawPullbackTerm p hp r k hr P hP := by
  rw [rawPullbackTerm, rawIntegralGenerator_smul, map_smulₛₗ]
  rw [rawPullbackTerm, smul_comm]

include hp7 hp19 in
theorem rawPullbackCoordinates_add (r : ℕ) (hr : 1 ≤ r)
    (P Q : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) (hQ : Q ∈ numeratorFiltration ℤ_[p] r) :
    rawPullbackCoordinates p hp r hr (P+Q) ((numeratorFiltration ℤ_[p] r).add_mem hP hQ) =
      rawPullbackCoordinates p hp r hr P hP + rawPullbackCoordinates p hp r hr Q hQ := by
  unfold rawPullbackCoordinates
  conv_lhs =>
    arg 1
    ext k
    rw [rawPullbackTerm_add p hp r k hr P Q hP hQ, map_add]
  exact (rawPullbackTerm_coordinates_summable p hp hp7 hp19 r hr P hP).tsum_add
    (rawPullbackTerm_coordinates_summable p hp hp7 hp19 r hr Q hQ)

theorem rawPullbackCoordinates_smul (r : ℕ) (hr : 1 ≤ r)
    (c : ℤ_[p]) (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    rawPullbackCoordinates p hp r hr (c • P) ((numeratorFiltration ℤ_[p] r).smul_mem c hP) =
      IntegralTransport.padicCoefficientMap p c • rawPullbackCoordinates p hp r hr P hP := by
  unfold rawPullbackCoordinates
  conv_lhs =>
    arg 1
    ext k
    rw [rawPullbackTerm_smul p hp r k hr c P hP, map_smul]
  exact tsum_const_smul'' _

def plainPullbackCoordinates (r : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) : Fin 11 → ℚ_[p] :=
  ((r-1).factorial : ℚ_[p])⁻¹ • rawPullbackCoordinates p hp r hr P hP

include hp7 hp19 in
theorem plainPullbackCoordinates_raise (r : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    plainPullbackCoordinates p hp (r+1) (by omega)
      (P*torusPolynomial (Parameter.integralTenth p hp)) (numeratorFiltration_mul_f _ r hP) =
      plainPullbackCoordinates p hp r hr P hP := by
  rw [plainPullbackCoordinates, rawPullbackCoordinates_raise p hp hp7 hp19, smul_smul]
  simp only [Nat.add_sub_cancel]
  have hf : (r.factorial : ℚ_[p]) = (r : ℚ_[p])*((r-1).factorial : ℚ_[p]) := by
    have hf := Nat.factorial_succ (r-1)
    rw [show r-1+1 = r by omega] at hf
    rw [hf, Nat.cast_mul]
  have hrne : (r : ℚ_[p]) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hc : (r.factorial : ℚ_[p])⁻¹*(r : ℚ_[p]) = ((r-1).factorial : ℚ_[p])⁻¹ := by
    rw [hf, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hrne, mul_one]
  rw [hc]
  rfl

end WPResidueFrobenius
