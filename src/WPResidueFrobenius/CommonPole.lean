import WPResidueFrobenius.ExactDescent

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators Topology
open WPResidueQuotient Filter

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

theorem finiteRawPullback_raise (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (r k : ℕ) (hr : 1 ≤ r) (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    finiteRawPullback p hp (r+1) (k+1) (by omega)
        (P*torusPolynomial (Parameter.integralTenth p hp))
        (numeratorFiltration_mul_f _ r hP) -
      (r : ℚ_[p]) • finiteRawPullback p hp r (k+1) hr P hP =
        -(k+1 : ℚ_[p]) • rawPullbackTerm p hp r (k+1) hr P hP := by
  apply Subtype.ext
  simp only [Submodule.coe_sub, Submodule.coe_smul, Algebra.smul_def, map_neg,
    map_natCast, map_add, map_one]
  rw [finiteRawPullback_coe, finiteRawPullback_coe, rawPullbackTerm_coe]
  have hf : (r.factorial : NumericalRing p) = (r : NumericalRing p)*((r-1).factorial : NumericalRing p) := by
    have hf := Nat.factorial_succ (r-1)
    rw [show r-1+1 = r by omega] at hf
    rw [hf, Nat.cast_mul]
  simp only [Nat.add_sub_cancel, hf]
  have hs := finiteNumericalPullback_raise p hp P r k
  have hcQ : (r : ℚ)*binomialWeight (r+1) k = -(k+1 : ℚ)*binomialWeight r (k+1) := by
    linear_combination (binomialWeight_derivative r k hr) + (binomialWeight_raise r k hr)
  have hc := congrArg (algebraMap ℚ (NumericalRing p)) hcQ
  simp only [map_mul, map_neg, map_add, map_natCast, map_one] at hc
  linear_combination
    (p : NumericalRing p)^5*(r : NumericalRing p)*((r-1).factorial : NumericalRing p)*hs +
      (p : NumericalRing p)^5*((r-1).factorial : NumericalRing p)*numericalPhi p P*
        inverseF (1/10 : ℚ_[p])^(p*r)*numericalQ p hp^(k+1)*hc

theorem nat_mul_tendsto_zero {f : ℕ → ℚ_[p]} (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun (k : ℕ) => (k+1 : ℚ_[p])*f k) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at hf ⊢
  apply squeeze_zero (fun k => norm_nonneg _ ) _ hf
  intro k
  rw [norm_mul]
  have hn : ‖(k+1 : ℚ_[p])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := p) (k+1 : ℕ)
  simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg (f k))

include hp7 hp19 in
theorem rawPullbackCoordinates_raise (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (r : ℕ) (hr : 1 ≤ r) (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    rawPullbackCoordinates p hp (r+1) (by omega)
        (P*torusPolynomial (Parameter.integralTenth p hp))
        (numeratorFiltration_mul_f _ r hP) =
      (r : ℚ_[p]) • rawPullbackCoordinates p hp r hr P hP := by
  have ht : Tendsto (fun (k : ℕ) => -(k+1 : ℚ_[p]) •
      ActualSpecialization.tenthClosedCoordinates ℚ_[p] (rawPullbackTerm p hp r (k+1) hr P hP))
      atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro j
    have h := (rawPullbackTerm_coordinate_tendsto_zero p hp hp7 hp19 r hr P hP j).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, neg_mul, neg_zero, Function.comp_def] using
      (nat_mul_tendsto_zero p h).neg
  have hz := ht.congr' (Filter.Eventually.of_forall fun k =>
    (show ActualSpecialization.tenthClosedCoordinates ℚ_[p]
      (finiteRawPullback p hp (r+1) (k+1) (by omega)
        (P*torusPolynomial (Parameter.integralTenth p hp)) (numeratorFiltration_mul_f _ r hP)) -
      (r : ℚ_[p]) • ActualSpecialization.tenthClosedCoordinates ℚ_[p]
        (finiteRawPullback p hp r (k+1) hr P hP) = _ by
      rw [← map_smul, ← map_sub, finiteRawPullback_raise, map_smul]).symm)
  have hlim := ((finiteRawPullback_coordinates_tendsto p hp hp7 hp19
      (P*torusPolynomial (Parameter.integralTenth p hp)) (r+1) (by omega)
      (numeratorFiltration_mul_f _ r hP)).sub
      ((finiteRawPullback_coordinates_tendsto p hp hp7 hp19 P r hr hP).const_smul (r : ℚ_[p]))).comp
        (tendsto_add_atTop_nat 1)
  have he := tendsto_nhds_unique hlim hz
  exact sub_eq_zero.mp (by simpa only [sub_zero] using he)

end WPResidueFrobenius
