import WPActualOrdinaryJet
import WPFiniteQuadraticResidue
import WPActualIntegratedSource
import WPFiniteConductorPolynomial
import Mathlib.Algebra.Polynomial.BigOperators

open scoped BigOperators
open Polynomial WPForcedSourceStokes WPFiniteConductorPolynomial

namespace WPLiteralAdapter

noncomputable section

set_option maxHeartbeats 2000000

local notation "ρ" => algebraMap ℚ[X] (RatFunc ℚ)

/-- Literal LP after its actual collision factor, retaining all nine entries. -/
noncomputable def residueLPbar : Fin 3 → Fin 3 → ℚ[X] :=
  let A : ℚ[X] := 81*X^2-198*X+80
  let B : ℚ[X] := 243*X^3-1053*X^2+1266*X-400
  let c : ℚ[X] := C (1953125/209952)
  let d : ℚ[X] := C (244140625/944784)
  ![![0, 0, c*A*B], ![0, 0, -(d*A)], ![-(c*A*B), d*A, 0]]

noncomputable def residueRP : Fin 3 → Fin 3 → ℚ[X] :=
  let B : ℚ[X] := 243*X^3-1053*X^2+1266*X-400
  let d : ℚ[X] := C (244140625/944784)
  ![![0, 0, RP20], ![0, C (3906250/6561)*X*(99*X-50), -(d*B)],
    ![RP20, -(d*B), C (30517578125/8503056)]]

noncomputable def residueAbar (i j : Fin 3) : ℚ[X] := -m*residueLPbar i j+ell*residueRP i j
noncomputable def residueMatrix (e : ℕ) (i j : Fin 3) : ℚ[X] :=
  if e=0 then residueAbar i j else residueLPbar i j

theorem residue_mean_map : RatFunc.C (ρ m)=bivMean := by
  norm_num [m, bivMean, bivX, symbol, map_mul, map_add, map_sub, map_pow,
    map_div₀, RatFunc.algebraMap_C, RatFunc.algebraMap_X, _root_.map_ofNat]

theorem residue_ell_map : RatFunc.C (ρ ell)=bivEll := by
  norm_num [ell, bivEll, bivX, symbol, map_mul, map_sub, map_div₀,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X, _root_.map_ofNat]

theorem residue_lam_map : ρ lam=lambda := by
  norm_num [lam, lambda, symbol, map_mul, map_pow, RatFunc.algebraMap_C,
    RatFunc.algebraMap_X, map_div₀, _root_.map_ofNat]

theorem residue_lp_actual (i j : Fin 3) :
    bivLP i j=bivCollision*RatFunc.C (ρ (residueLPbar i j)) := by
  fin_cases i <;> fin_cases j
  all_goals norm_num [bivLP, residueLPbar, bivCollision, bivX, symbol, map_add,
    map_sub, map_mul, map_neg, map_pow, map_div₀, RatFunc.algebraMap_C,
    RatFunc.algebraMap_X, _root_.map_ofNat]
  all_goals ring

theorem residue_rp_actual (i j : Fin 3) : bivRP i j=RatFunc.C (ρ (residueRP i j)) := by
  fin_cases i <;> fin_cases j
  all_goals norm_num [bivRP, residueRP, RP20, bivX, symbol, map_add, map_sub,
    map_mul, map_neg, map_pow, map_div₀, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
    _root_.map_ofNat]
  all_goals ring

theorem residue_abar_actual (i j : Fin 3) :
    RatFunc.C (ρ (residueAbar i j)) = -bivMean*RatFunc.C (ρ (residueLPbar i j))+
      bivEll*bivRP i j := by
  simp only [residueAbar, map_add, map_neg, map_mul, residue_mean_map,
    residue_ell_map, ← residue_rp_actual]

theorem residue_matrix_degree (e : ℕ) (i j : Fin 3) : (residueMatrix e i j).natDegree≤8 := by
  unfold residueMatrix
  split_ifs
  · fin_cases i <;> fin_cases j
    all_goals norm_num [residueAbar, residueLPbar, residueRP, RP20, m, ell]
    all_goals compute_degree!
  · fin_cases i <;> fin_cases j
    all_goals norm_num [residueLPbar]
    all_goals compute_degree!

/-- Cancellation of the actual collision factor in the complete ordinary-state row. -/
theorem residue_bs_actual (i j : Fin 3) :
    bivBsDivU i j=RatFunc.C (2/ρ (X^4*escape^2))*
      (RatFunc.C (ρ (residueAbar i j))+RatFunc.C (ρ (residueLPbar i j))*bivS)/
        bivConductor := by
  have hM : bivCollision≠0 := by
    rw [bivCollision, show 25-9*bivX=-(9*bivX-25) by ring]
    exact neg_ne_zero.mpr biv_collision_ne_zero
  rw [bivBsDivU, residue_lp_actual, residue_rp_actual, residue_abar_actual, bivSourceDivisor]
  rw [residue_rp_actual]
  norm_num [map_mul, map_pow, map_div₀, RatFunc.algebraMap_X, symbol, bivX,
    escape, bivEscape, _root_.map_ofNat]
  field_simp [bivX_ne_zero, hM, biv_escape_ne_zero, bivConductor_ne_zero]
  ring

noncomputable def residueInverseNumerator : ℕ → ℚ[X]
  | 0 => 1
  | 1 => 2*m
  | k+2 => 2*m*residueInverseNumerator (k+1)-lam*residueInverseNumerator k

theorem residue_inverse_numerator_degree (k : ℕ) :
    (residueInverseNumerator k).natDegree≤3*k := by
  have hm : m.natDegree≤3 := by norm_num [m]; compute_degree!
  have hl : lam.natDegree≤3 := by norm_num [lam]
  have h2m : (2*m).natDegree≤3 := by
    change (C (2 : ℚ)*m).natDegree≤3
    exact (natDegree_C_mul_le _ _).trans hm
  induction k using Nat.twoStepInduction with
  | zero => simp [residueInverseNumerator]
  | one => simpa [residueInverseNumerator] using h2m
  | more k hk hk1 =>
    rw [residueInverseNumerator]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_mul_le.trans ((add_le_add h2m hk1).trans (by omega))
    · exact natDegree_mul_le.trans ((add_le_add hl hk).trans (by omega))

theorem residue_quadratic_inverse_recurrence (m₀ l : RatFunc ℚ) (hl : l≠0) (k : ℕ) :
    PowerSeries.coeff (k+2) (finiteQuadraticInverse m₀ l) =
      (2*m₀*PowerSeries.coeff (k+1) (finiteQuadraticInverse m₀ l)-
        PowerSeries.coeff k (finiteQuadraticInverse m₀ l))/l := by
  have hp := PowerSeries.mul_inv_cancel (finiteQuadraticSeries m₀ l)
    (by simpa only [finite_quadratic_constant] using hl)
  change finiteQuadraticSeries m₀ l*finiteQuadraticInverse m₀ l=1 at hp
  have he : finiteQuadraticSeries m₀ l*finiteQuadraticInverse m₀ l =
      PowerSeries.X^2*finiteQuadraticInverse m₀ l-
      PowerSeries.C (2*m₀)*(PowerSeries.X*finiteQuadraticInverse m₀ l)+
      PowerSeries.C l*finiteQuadraticInverse m₀ l := by
    simp only [finiteQuadraticSeries, finiteQuadraticPolynomial, Polynomial.coe_add,
      Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C,
      Polynomial.coe_X]
    ring
  have hc := congrArg (PowerSeries.coeff (k+2)) hp
  rw [he, map_add, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul] at hc
  norm_num [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C_mul] at hc
  apply (eq_div_iff hl).2
  linear_combination hc

theorem residue_lambda_ne_zero : lambda≠0 := by
  unfold lambda
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ (RatFunc.algebraMap_ne_zero X_ne_zero))

theorem residue_inverse_coefficient (k : ℕ) :
    PowerSeries.coeff k (finiteQuadraticInverse (ρ m) lambda) =
      ρ (residueInverseNumerator k)/lambda^(k+1) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [finite_quadratic_inverse_zero, residueInverseNumerator]
  | one =>
    rw [finite_quadratic_inverse_one, residueInverseNumerator]
    simp only [map_mul, _root_.map_ofNat]
    field_simp [residue_lambda_ne_zero]
  | more k hk hk1 =>
    rw [residue_quadratic_inverse_recurrence _ _ residue_lambda_ne_zero k, hk1, hk,
      residueInverseNumerator]
    simp only [map_sub, map_mul, _root_.map_ofNat, residue_lam_map, pow_succ]
    field_simp [residue_lambda_ne_zero]

theorem residue_conductor_polynomial : bivConductor=
    algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
      (finiteQuadraticPolynomial (ρ m) lambda) := by
  simp only [finiteQuadraticPolynomial, map_add, map_sub, map_mul, map_pow,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X, _root_.map_ofNat, residue_mean_map]
  rw [bivConductor, bivLam_literal]
  rfl

noncomputable def residueNumeratorTerm (p : ℕ) (i j : Fin 3) (a b e : ℕ) : ℚ[X] :=
  if 2≤a ∧ a+e+1≤b then
    C (2*(nativeOrdinaryPolynomial p i).coeff a*(nativeOrdinaryPolynomial p j).coeff b*
      (729/15625 : ℚ)^(a+e))*X^(3*(a+e)-4)*residueMatrix e i j*
      residueInverseNumerator (b-a-e-1)
  else 0

noncomputable def actualResidueNumerator (p : ℕ) : ℚ[X] :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ b∈Finset.range (p+3), ∑ a∈Finset.range (p+3),
    (residueNumeratorTerm p i j a b 0+residueNumeratorTerm p i j a b 1)

theorem residue_numerator_term_X_squared (p : ℕ) (i j : Fin 3) (a b e : ℕ) :
    (X : ℚ[X])^2∣residueNumeratorTerm p i j a b e := by
  unfold residueNumeratorTerm
  split_ifs with h
  · refine ⟨C (2*(nativeOrdinaryPolynomial p i).coeff a*
      (nativeOrdinaryPolynomial p j).coeff b*(729/15625 : ℚ)^(a+e))*
      X^(3*(a+e)-6)*residueMatrix e i j*residueInverseNumerator (b-a-e-1), ?_⟩
    rw [show 3*(a+e)-4=2+(3*(a+e)-6) by omega, pow_add]
    ring
  · exact dvd_zero _

theorem actual_residue_numerator_X_squared (p : ℕ) : (X : ℚ[X])^2∣actualResidueNumerator p := by
  classical
  unfold actualResidueNumerator
  apply Finset.dvd_sum
  intro i _hi
  apply Finset.dvd_sum
  intro j _hj
  apply Finset.dvd_sum
  intro b _hb
  apply Finset.dvd_sum
  intro a _ha
  exact dvd_add (residue_numerator_term_X_squared p i j a b 0)
    (residue_numerator_term_X_squared p i j a b 1)

theorem residue_numerator_term_degree (p : ℕ) (i j : Fin 3) (a b e : ℕ) (hb : b<p+3) :
    (residueNumeratorTerm p i j a b e).natDegree≤3*p+7 := by
  unfold residueNumeratorTerm
  split_ifs with h
  · have hdeg : (C (2*(nativeOrdinaryPolynomial p i).coeff a*
      (nativeOrdinaryPolynomial p j).coeff b*(729/15625 : ℚ)^(a+e))*
      X^(3*(a+e)-4)*residueMatrix e i j*residueInverseNumerator (b-a-e-1)).natDegree≤
        (3*(a+e)-4)+8+3*(b-a-e-1) := by
      calc
        _≤(C (2*(nativeOrdinaryPolynomial p i).coeff a*
          (nativeOrdinaryPolynomial p j).coeff b*(729/15625 : ℚ)^(a+e))*
          X^(3*(a+e)-4)*residueMatrix e i j).natDegree+
          (residueInverseNumerator (b-a-e-1)).natDegree := natDegree_mul_le
        _≤(C (2*(nativeOrdinaryPolynomial p i).coeff a*
          (nativeOrdinaryPolynomial p j).coeff b*(729/15625 : ℚ)^(a+e))*
          X^(3*(a+e)-4)).natDegree+(residueMatrix e i j).natDegree+
          (residueInverseNumerator (b-a-e-1)).natDegree := by gcongr; exact natDegree_mul_le
        _≤(3*(a+e)-4)+8+3*(b-a-e-1) :=
          add_le_add (add_le_add (natDegree_C_mul_X_pow_le _ _) (residue_matrix_degree e i j))
            (residue_inverse_numerator_degree _)
    exact hdeg.trans (by omega)
  · simp

theorem actual_residue_numerator_degree (p : ℕ) : (actualResidueNumerator p).natDegree≤3*p+7 := by
  classical
  unfold actualResidueNumerator
  apply natDegree_sum_le_of_forall_le
  intro i _hi
  apply natDegree_sum_le_of_forall_le
  intro j _hj
  apply natDegree_sum_le_of_forall_le
  intro b hb
  apply natDegree_sum_le_of_forall_le
  intro a _ha
  exact (natDegree_add_le _ _).trans (max_le
    (residue_numerator_term_degree p i j a b 0 (Finset.mem_range.mp hb))
    (residue_numerator_term_degree p i j a b 1 (Finset.mem_range.mp hb)))

end

end WPLiteralAdapter
