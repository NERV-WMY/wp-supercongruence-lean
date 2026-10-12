import WPFullNativeSixState
import Mathlib.Algebra.Polynomial.Derivation

open scoped BigOperators
open Polynomial

namespace WPForcedSourceStokes

noncomputable section

theorem native_operator_expanded (P : ℚ[X]) :
    WPReview.nativeOperator P = thetaPower 3 P - X *
      (thetaPower 3 P + C (3/2)*thetaPower 2 P + C (23/36)*thetaPower 1 P + C (5/72)*P) := by
  ext k
  rcases k with (_ | k)
  · simp [WPReview.nativeOperator, thetaPower_coeff, WPReview.nativeTheta_coeff]
  · simp only [WPReview.nativeOperator, WPReview.nativeShift, coeff_sub, coeff_X_mul,
      coeff_add, coeff_C_mul, WPReview.nativeTheta_coeff, thetaPower_coeff]
    ring

section Field

variable {K : Type*} [Field K] [Algebra ℚ K]

omit [Algebra ℚ K] in
theorem integer_derivation_ratCast (D : Derivation ℤ K K) (q : ℚ) : D (q : K) = 0 := by
  rw [Rat.cast_def]
  simp [Derivation.leibniz_div, Derivation.map_natCast, Derivation.map_intCast,
    smul_eq_mul]

@[simp] theorem native_algebraMap_rat (q : ℚ) : algebraMap ℚ K q = (q : K) := by
  exact map_ratCast (algebraMap ℚ K) q

@[simp] theorem native_thetaPower_zero (P : ℚ[X]) : thetaPower 0 P = P := rfl

/-- The actual integer-base derivations are rational linear. -/
noncomputable def rationalLinearDerivation (D : Derivation ℤ K K) : Derivation ℚ K K where
  toLinearMap :=
    { toFun := D
      map_add' := D.map_add
      map_smul' := by
        intro q a
        rw [Algebra.smul_def, Algebra.smul_def, Derivation.leibniz]
        have hq : algebraMap ℚ K q = (q : K) := by
          exact native_algebraMap_rat q
        rw [hq, integer_derivation_ratCast]
        simp only [RingHom.id_apply, hq, smul_eq_mul, mul_zero, add_zero] }
  leibniz' := D.leibniz
  map_one_eq_zero' := D.map_one_eq_zero

noncomputable def finiteNativeJet (p : ℕ) (q : K) (i : Fin 3) : K :=
  aeval q (thetaPower i.val (WPReview.nativePolynomial p))

noncomputable def finiteNativeMatrix (q : K) : Fin 3 → Fin 3 → K :=
  ![![0, 1, 0], ![0, 0, 1],
    ![q/(1-q)*(5/72), q/(1-q)*(23/36), q/(1-q)*(3/2)]]

theorem finite_native_euler_jet (D : Derivation ℚ K K) (p k : ℕ) (q : K) :
    q * D (aeval q (thetaPower k (WPReview.nativePolynomial p))) =
      D q * aeval q (thetaPower (k+1) (WPReview.nativePolynomial p)) := by
  have hs : thetaPower (k+1) (WPReview.nativePolynomial p) =
      WPReview.nativeTheta (thetaPower k (WPReview.nativePolynomial p)) := by
    rw [thetaPower, Function.iterate_succ_apply']
    rfl
  rw [Derivation.map_aeval, hs]
  simp only [WPReview.nativeTheta, map_mul, aeval_X, smul_eq_mul]
  ring

theorem finite_native_evaluated_residual (p : ℕ) (hp : 0 < p) (q : K) :
    (1-q)*aeval q (thetaPower 3 (WPReview.nativePolynomial p)) - q*
      ((5/72)*finiteNativeJet p q 0 + (23/36)*finiteNativeJet p q 1 +
        (3/2)*finiteNativeJet p q 2) =
      -algebraMap ℚ K (WPReview.nativeEndpoint p)*q^p := by
  have h := congrArg (aeval q) (WPReview.native_truncation_residual p hp)
  rw [native_operator_expanded] at h
  simp only [map_sub, map_add, map_mul, aeval_X, aeval_C, aeval_monomial,
    map_neg] at h
  change _ = _
  norm_num [finiteNativeJet] at h ⊢
  linear_combination h

/-- The complete finite jet keeps the literal upper residual. -/
theorem finite_native_jet_derivative (D : Derivation ℚ K K) (p : ℕ) (hp : 0 < p)
    (q : K) (hq : q ≠ 0) (h1 : 1-q ≠ 0) (i : Fin 3) :
    D (finiteNativeJet p q i) = (D q/q)*
      ((∑ j : Fin 3, finiteNativeMatrix q i j*finiteNativeJet p q j) -
        if i = 2 then algebraMap ℚ K (WPReview.nativeEndpoint p)*q^p/(1-q) else 0) := by
  have h0 := finite_native_euler_jet D p 0 q
  have h2 := finite_native_euler_jet D p 1 q
  have h3 := finite_native_euler_jet D p 2 q
  have hr := finite_native_evaluated_residual p hp q
  fin_cases i
  · simp [finiteNativeMatrix, Fin.sum_univ_succ, finiteNativeJet, -Derivation.map_aeval]
    field_simp [hq]
    simp only [native_thetaPower_zero] at h0
    linear_combination h0
  · simp [finiteNativeMatrix, Fin.sum_univ_succ, finiteNativeJet, -Derivation.map_aeval]
    field_simp [hq]
    linear_combination h2
  · norm_num [finiteNativeMatrix, Fin.sum_univ_succ, finiteNativeJet,
      -Derivation.map_aeval] at hr ⊢
    rw [if_pos (show (⟨2, by omega⟩ : Fin 3) = 2 from rfl)]
    field_simp [hq, h1]
    linear_combination (1-q)*h3 + D q*hr

end Field

end

end WPForcedSourceStokes
