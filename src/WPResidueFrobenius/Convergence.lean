import WPResidueFrobenius.PullbackTerms
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Ultra

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators Topology
open Filter WPResidueQuotient

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

theorem rational_norm (q : ℚ) (hq : q ≠ 0) :
    ‖(q : ℚ_[p])‖ = (p : ℝ)^(-padicValRat p q) := by
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hq]
  simp only [Rat.cast_zpow, Rat.cast_natCast]

theorem rational_times_power_norm (q : ℚ) (hq : q ≠ 0) (gain : ℕ) :
    ‖(q : ℚ_[p])*(p : ℚ_[p])^gain‖ = (p : ℝ)^(-(padicValRat p q+gain)) := by
  rw [norm_mul, rational_norm p q hq, Padic.norm_p_pow,
    ← zpow_add₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]
  congr 1
  omega

theorem integral_factor_norm (q : ℚ) (hq : q ≠ 0) (gain : ℕ) (z : ℤ_[p]) :
    ‖(q : ℚ_[p])*(p : ℚ_[p])^gain*IntegralTransport.padicCoefficientMap p z‖ ≤
      (p : ℝ)^(-(padicValRat p q+gain)) := by
  rw [norm_mul, rational_times_power_norm p q hq gain]
  have hz : ‖IntegralTransport.padicCoefficientMap p z‖ ≤ 1 := z.property
  simpa using mul_le_mul_of_nonneg_left hz
    (zpow_nonneg (by positivity : (0 : ℝ) ≤ p) _)

theorem signed_scalar_with_gain_norm (r k : ℕ) :
    ‖(pullbackScalar p r k : ℚ_[p]) * (p : ℚ_[p])^(pullbackGain r k)‖ =
      (p : ℝ)^(-(padicValRat p (pullbackScalar p r k) + pullbackGain r k)) := by
  rw [norm_mul, rational_norm p _ (pullbackScalar_ne_zero p r k (Fact.out : p.Prime)),
    Padic.norm_p_pow, ← zpow_add₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]
  congr 1
  omega

include hp7 hp19 in
theorem rawPullbackTerm_coordinate_norm (r k : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) (i : Fin 11) :
    ‖ActualSpecialization.tenthClosedCoordinates ℚ_[p]
      (rawPullbackTerm p hp r k hr P hP) i‖ ≤
      (p : ℝ)^(-(padicValRat p (pullbackScalar p r k) + pullbackGain r k)) := by
  obtain ⟨w, hw⟩ := rawPullbackTerm_coordinates_factor p hp hp7 hp19 r k hr P hP
  rw [hw, norm_mul, signed_scalar_with_gain_norm]
  have hw1 : ‖IntegralTransport.padicCoefficientMap p (w i)‖ ≤ 1 := (w i).property
  simpa using mul_le_mul_of_nonneg_left hw1
    (zpow_nonneg (by positivity : (0 : ℝ) ≤ p) _)

include hp7 hp19 in
theorem rawPullbackTerm_coordinate_precision (r k precision : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) (i : Fin 11)
    (hgain : (precision : ℤ) ≤ padicValRat p (pullbackScalar p r k) + pullbackGain r k) :
    ‖ActualSpecialization.tenthClosedCoordinates ℚ_[p]
      (rawPullbackTerm p hp r k hr P hP) i‖ ≤ (p : ℝ)^(-(precision : ℤ)) := by
  apply le_trans (rawPullbackTerm_coordinate_norm p hp hp7 hp19 r k hr P hP i)
  apply zpow_le_zpow_right₀
  · have hx : (1 : ℕ) ≤ p := (Fact.out : p.Prime).one_lt.le
    exact_mod_cast hx
  · omega

include hp7 hp19 in
theorem rawPullbackTerm_coordinate_tendsto_zero (r : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) (i : Fin 11) :
    Tendsto (fun k => ActualSpecialization.tenthClosedCoordinates ℚ_[p]
      (rawPullbackTerm p hp r k hr P hP) i) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hb : (p : ℝ)⁻¹ < 1 := by
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨precision, hm⟩ := exists_pow_lt_of_lt_one hε hb
  obtain ⟨cutoff, hc⟩ := pullback_gain_eventual p r precision (Fact.out : p.Prime) hp hr
  refine ⟨cutoff, ?_⟩
  intro k hk
  rw [dist_zero_right]
  apply lt_of_le_of_lt
    (rawPullbackTerm_coordinate_precision p hp hp7 hp19 r k precision hr P hP i (hc k hk))
  simpa [zpow_neg, zpow_natCast, inv_pow] using hm

include hp7 hp19 in
theorem rawPullbackTerm_coordinates_summable (r : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    Summable (fun k => ActualSpecialization.tenthClosedCoordinates ℚ_[p]
      (rawPullbackTerm p hp r k hr P hP)) := by
  rw [Pi.summable]
  intro i
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using
    rawPullbackTerm_coordinate_tendsto_zero p hp hp7 hp19 r hr P hP i

/-- Actual coordinate sum for a specified finite Laurent numerator and pole.
Presentation independence is a separate obligation. -/
def rawPullbackCoordinates (r : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) : Fin 11 → ℚ_[p] :=
  ∑' k, ActualSpecialization.tenthClosedCoordinates ℚ_[p]
    (rawPullbackTerm p hp r k hr P hP)

include hp7 hp19 in
theorem rawPullbackCoordinates_hasSum (r : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    HasSum (fun k => ActualSpecialization.tenthClosedCoordinates ℚ_[p]
      (rawPullbackTerm p hp r k hr P hP)) (rawPullbackCoordinates p hp r hr P hP) :=
  (rawPullbackTerm_coordinates_summable p hp hp7 hp19 r hr P hP).hasSum

end WPResidueFrobenius
