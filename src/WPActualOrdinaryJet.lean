import WPActualFiniteResidueAttachment
import Mathlib.Algebra.BigOperators.NatAntidiagonal

open scoped BigOperators
open Polynomial

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 1500000

/-- All three literal ordinary states obtained by JCG transpose from the native jets. -/
noncomputable def nativeOrdinaryPolynomial (p : ℕ) : Fin 3 → ℚ[X] :=
  ![(1-X)*thetaPower 2 (WPReview.nativePolynomial p) -
      C (1/2)*X*thetaPower 1 (WPReview.nativePolynomial p) -
      C (5/72)*X*WPReview.nativePolynomial p,
    X*(X-1)*thetaPower 1 (WPReview.nativePolynomial p),
    C 2*X^2*(1-X)*WPReview.nativePolynomial p]

theorem actual_native_ordinary_value (p : ℕ) (q : RatFunc (RatFunc ℚ)) (a : Fin 3) :
    (∑ i : Fin 3, bivJCG q i a*finiteNativeJet p q i) =
      Polynomial.aeval q (nativeOrdinaryPolynomial p a) := by
  fin_cases a
  all_goals
    norm_num [bivJCG, nativeOrdinaryPolynomial, finiteNativeJet,
      Fin.sum_univ_succ, Polynomial.aeval_def, Polynomial.eval₂_add,
      Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_X, native_algebraMap_rat]
    all_goals ring

/-- The constant and linear coefficients cancel in the actual ordinary states. -/
theorem native_ordinary_first_two_zero (p : ℕ) (hp : 2≤p) (a : Fin 3) :
    (nativeOrdinaryPolynomial p a).coeff 0 = 0 ∧
      (nativeOrdinaryPolynomial p a).coeff 1 = 0 := by
  have h0 : 0<p := by omega
  have h1 : 1<p := by omega
  fin_cases a
  all_goals
    constructor
    all_goals
      norm_num [nativeOrdinaryPolynomial, coeff_add, coeff_sub, coeff_mul,
        Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, thetaPower_coeff,
        WPReview.nativePolynomial_coeff, h0, h1, WPReview.nativeCoefficient]

theorem native_ordinary_X_squared_dvd (p : ℕ) (hp : 2≤p) (a : Fin 3) :
    (X : ℚ[X])^2 ∣ nativeOrdinaryPolynomial p a := by
  rw [X_pow_dvd_iff]
  intro d hd
  have h := native_ordinary_first_two_zero p hp a
  interval_cases d
  · exact h.1
  · exact h.2

/-- The literal actual conductor residue expressed through all three ordinary states. -/
theorem actual_conductor_ordinary_pairing (p : ℕ) :
    actualTensorPairing p bivConductorR =
      ∑ a : Fin 3, ∑ b : Fin 3,
        bivBsDivU a b * Polynomial.aeval bivS (nativeOrdinaryPolynomial p a) *
          Polynomial.aeval bivB (nativeOrdinaryPolynomial p b) := by
  simp only [← actual_native_ordinary_value, actualTensorPairing,
    actualNativeTensor, bivConductorR, Fin.sum_univ_succ, Fin.sum_univ_zero]
  ring

end

end WPForcedSourceStokes
