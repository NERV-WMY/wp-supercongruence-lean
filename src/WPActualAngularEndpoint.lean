import WPActualEtaPolynomial
import WPActualEndpointSplit
import WPFiniteLaurentEndpoint

open scoped BigOperators
open Polynomial

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 2000000

noncomputable def nativeJetCoefficientPolynomial (p : ℕ) (i : Fin 3) :
    Polynomial (RatFunc ℚ) :=
  (thetaPower i.val (WPReview.nativePolynomial p)).map (RatFunc.C (K := ℚ))

theorem native_jet_coefficient_extension (p : ℕ) (i : Fin 3) :
    Polynomial.aeval bivS (nativeJetCoefficientPolynomial p i) =
      finiteNativeJet p bivS i := by
  have hq (q : ℚ) :
      algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ)) (RatFunc.C q) =
        algebraMap ℚ (RatFunc (RatFunc ℚ)) q := by
    rw [outer_native_scalar]
    rfl
  rw [nativeJetCoefficientPolynomial, theta_native_polynomial_sum,
    finite_native_jet_sum]
  simp only [Polynomial.map_sum, Polynomial.map_monomial, map_sum,
    Polynomial.aeval_monomial, hq]

theorem native_jet_coefficient_evaluation (p : ℕ) (i : Fin 3) :
    (nativeJetCoefficientPolynomial p i).eval lambda =
      pullbackValue (thetaPower i.val (WPReview.nativePolynomial p)) := by
  rw [nativeJetCoefficientPolynomial, theta_native_polynomial_sum]
  change _ = pullbackHom _
  simp only [Polynomial.map_sum, Polynomial.map_monomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    map_sum, pullbackHom_apply, pullbackValue_monomial]

/-- Multiplication by s cubed makes the complete actual last-column pairing polynomial. -/
noncomputable def actualEtaNativePolynomial (p : ℕ) : Polynomial (RatFunc ℚ) :=
  ∑ i : Fin 3, etaClearedPolynomial i 2*nativeJetCoefficientPolynomial p i

theorem actual_eta_native_polynomial (p : ℕ) :
    Polynomial.aeval bivS (actualEtaNativePolynomial p) =
      bivS^3 * ∑ i : Fin 3, bivEta i 2*finiteNativeJet p bivS i := by
  simp only [actualEtaNativePolynomial, map_sum, map_mul,
    actual_eta_cleared_polynomial, native_jet_coefficient_extension,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The actual high angular coefficients contain only the last three native coefficients. -/
theorem actual_angular_high_coefficient (p a : ℕ) (hp : 3≤p) (ha : p+3≤a) :
    (actualEtaNativePolynomial p).coeff a =
      ∑ i : Fin 3, ∑ n ∈ Finset.range p,
        if p-3≤n then (etaClearedPolynomial i 2).coeff (a-n) *
          RatFunc.C ((n : ℚ)^i.val*WPReview.nativeCoefficient n) else 0 := by
  classical
  simp only [actualEtaNativePolynomial, nativeJetCoefficientPolynomial,
    theta_native_polynomial_sum, Polynomial.map_sum, Polynomial.map_monomial,
    Finset.mul_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n<p := Finset.mem_range.mp hn
  have hna : n≤a := by omega
  have hshift : a = (a-n)+n := by omega
  rw [hshift, coeff_mul_monomial, Nat.add_sub_cancel_right]
  by_cases hh : p-3≤n
  · rw [if_pos hh]
  · rw [if_neg hh]
    have hk : 6<a-n := by omega
    have hz : (etaClearedPolynomial i 2).coeff (a-n)=0 :=
      coeff_eq_zero_of_degree_lt ((actual_eta_cleared_degree i 2).trans_lt
        (by exact_mod_cast hk))
    rw [hz, zero_mul]

/-- The exact high tail of the full angular Laurent polynomial. -/
noncomputable def actualAngularHighError (p : ℕ) : RatFunc ℚ :=
  ∑ a ∈ Finset.range ((actualEtaNativePolynomial p).natDegree+1),
    if p+3≤a then (actualEtaNativePolynomial p).coeff a*lambda^a/lambda^3 else 0

theorem actual_last_column_high_tail (p : ℕ) :
    actualLastColumnEndpoint p =
      -(actualEtaNativePolynomial p).eval lambda/lambda^3+actualAngularHighError p := by
  have hc := actual_eta_native_polynomial p
  have hsum : (∑ i : Fin 3, bivEta i 2*finiteNativeJet p bivS i) =
      Polynomial.aeval bivS (actualEtaNativePolynomial p)/bivS^3 := by
    apply (eq_div_iff (pow_ne_zero _ bivS_ne_zero)).2
    simpa only [mul_comm] using hc.symm
  unfold actualLastColumnEndpoint
  rw [hsum]
  have hf :
      (Polynomial.aeval bivS (actualEtaNativePolynomial p)/bivS^3) /
          (bivS^p*(bivS-bivLambda)) =
      Polynomial.aeval bivS (actualEtaNativePolynomial p) /
          (bivS^(p+3)*(bivS-bivLambda)) := by
    rw [div_div, pow_add]
    congr 1
    ring
  rw [hf]
  exact finite_laurent_diagonal_endpoint p
    ((actualEtaNativePolynomial p).natDegree+1) (actualEtaNativePolynomial p)
      (Nat.lt_succ_self _)

/-- The finite angular evaluation cancels the actual complete native endpoint correction. -/
theorem actual_angular_endpoint_correction (p : ℕ) :
    nativeEndpointCorrection p = RatFunc.C (WPReview.nativeEndpoint p) *
      ((actualEtaNativePolynomial p).eval lambda/lambda^3) := by
  have he : (actualEtaNativePolynomial p).eval lambda/lambda^3 =
      ∑ i : Fin 3, actualEtaAtLambda i *
        pullbackValue (thetaPower i.val (WPReview.nativePolynomial p)) := by
    simp only [actualEtaNativePolynomial, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, native_jet_coefficient_evaluation, Finset.sum_div,
      actualEtaAtLambda]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [he]
  simp only [actual_eta_last_column_evaluation]
  unfold nativeEndpointCorrection
  congr 1
  norm_num [nativeEndpointState, Fin.sum_univ_succ, thetaPower]
  all_goals simp only [pullbackValue, cubicPullback, Polynomial.zero_comp,
    map_zero, mul_zero, zero_add]
  all_goals rfl

/-- The original source retains precisely the conductor and both finite high errors. -/
theorem actual_total_source_endpoint_split (p : ℕ) (hp : 0<p) :
    actualTotalSource p = RatFunc.C (WPReview.nativeEndpoint p) *
      (actualBetaFunctional p+actualFirstEndpointError p+actualAngularHighError p) := by
  rw [actualTotalSource, actual_delta_endpoint_split p hp,
    actual_last_column_high_tail, actual_angular_endpoint_correction]
  ring

end

end WPForcedSourceStokes
