import WPMomentPrecision.SecondLift.NativeQSource

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualNativeSecondTaylor
  WPActualPullbackSource WPActualNativeFirstJet
  WPMomentPrecision.FullNativeTaylor

namespace WPMomentPrecision.RationalEulerPrimitive

set_option maxHeartbeats 1200000

/-- The zero slot is fixed to zero by rational division; every original
positive coefficient through e is retained. -/
noncomputable def rationalEuler (e : ℕ) (P : ℚ[X]) : ℚ[X] :=
  coefficientPolynomial e (fun n => P.coeff n / (n : ℚ))

theorem rationalEuler_coeff (e : ℕ) (P : ℚ[X]) (n : ℕ) :
    (rationalEuler e P).coeff n = if n < e + 1 then P.coeff n / (n : ℚ) else 0 :=
  coefficientPolynomial_coeff _ _ _

theorem rationalEuler_degree (e : ℕ) (P : ℚ[X]) : (rationalEuler e P).natDegree ≤ e :=
  coefficientPolynomial_degree _ _

theorem rationalEuler_add (e : ℕ) (P Q : ℚ[X]) :
    rationalEuler e (P + Q) = rationalEuler e P + rationalEuler e Q := by
  ext n
  simp only [rationalEuler_coeff, coeff_add]
  split_ifs <;> ring

theorem rationalEuler_C_mul (e : ℕ) (a : ℚ) (P : ℚ[X]) :
    rationalEuler e (C a * P) = C a * rationalEuler e P := by
  ext n
  simp only [rationalEuler_coeff, coeff_C_mul]
  split_ifs <;> ring

theorem actual_Hpolynomial_Euler (e : ℕ) :
    Hpolynomial e = rationalEuler e (WPReview.nativePolynomial (e + 1)) := by
  ext n
  rw [Hpolynomial_coeff, rationalEuler_coeff, WPReview.nativePolynomial_coeff]
  split_ifs <;> simp

theorem divided_integral_coefficient (p e : ℕ) [Fact p.Prime] (_hp : 19 ≤ p)
    (he : e < p) (P : (integralRationals p)[X]) (n : ℕ) (hn : n < e + 1) :
    (P.map (integralRationals p).subtype).coeff n / (n : ℚ) ∈ integralRationals p := by
  by_cases hz : n = 0
  · subst n
    simp
  · have hi := WPFiniteConductorPolynomial.small_inverse_integral p n (by omega) (by omega)
    have hinv : (n : ℚ)⁻¹ ∈ integralRationals p := by
      change 0 ≤ padicValRat p (1 / (n : ℚ)) at hi
      change 0 ≤ padicValRat p ((n : ℚ)⁻¹)
      simpa only [one_div] using hi
    rw [coeff_map, div_eq_mul_inv]
    exact (integralRationals p).mul_mem (P.coeff n).property hinv

noncomputable def integralEuler (p e : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (he : e < p) (P : (integralRationals p)[X]) : (integralRationals p)[X] :=
  coefficientIntegralPolynomial p e
    (fun n => (P.map (integralRationals p).subtype).coeff n / (n : ℚ))
    (divided_integral_coefficient p e hp he P)

theorem integralEuler_value (p e : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (he : e < p) (P : (integralRationals p)[X]) :
    (integralEuler p e hp he P).map (integralRationals p).subtype =
      rationalEuler e (P.map (integralRationals p).subtype) :=
  coefficientIntegralPolynomial_value p e _ _

/-- The original CM argument 4/125 is integral, proved from the unit 5. -/
noncomputable def integralCMPoint (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : integralRationals p :=
  4 * (⟨1 / 5, WPFiniteConductorPolynomial.small_inverse_integral p 5
    (by norm_num) (by omega)⟩ : integralRationals p) ^ 3

theorem integralCMPoint_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralCMPoint p hp).val = (4 / 125 : ℚ) := by
  change 4 * (1 / 5 : ℚ) ^ 3 = 4 / 125
  norm_num

noncomputable def integralEulerValue (p e : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (he : e < p) (P : (integralRationals p)[X]) : integralRationals p :=
  (integralEuler p e hp he P).eval (integralCMPoint p hp)

theorem integralEulerValue_value (p e : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (he : e < p) (P : (integralRationals p)[X]) :
    (integralEulerValue p e hp he P).val =
      (rationalEuler e (P.map (integralRationals p).subtype)).eval (4 / 125 : ℚ) := by
  change (integralRationals p).subtype
    ((integralEuler p e hp he P).eval (integralCMPoint p hp)) = _
  rw [← eval_map_apply, integralEuler_value]
  change (rationalEuler e (P.map (integralRationals p).subtype)).eval
    (integralCMPoint p hp).val = _
  rw [integralCMPoint_value]

end WPMomentPrecision.RationalEulerPrimitive
