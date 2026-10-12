import WPFieldAssembly.ActualBalancedNodeAttachment
import Mathlib.Algebra.Polynomial.Coeff
import WPActualHalfHarmonic
import WPFiniteDSource

open scoped BigOperators Polynomial
open Polynomial WPFieldAssembly.ActualTC1Family
  WPFieldAssembly.ActualBalancedNodeAttachment
  WPFieldAssembly.ActualDeltaUNextSource

namespace WPFieldAssembly.ActualCauchyMoment

open WPPIntegralReduction WPActualRankTwoParameter WPActualRankTwoLowTaylor
  WPActualRankTwoHatLift WPActualRankTwoLegendreField WPActualGaussBottom
  WPActualGaussProper WPNativeParameterTaylor WPFieldAssembly.ActualBalancedCarry
  WPFieldAssembly.ResidualProjection WPFieldAssembly.NativeQuadraticInverse
  WPFiniteKSource WPFiniteAffineLog
  WPActualEvenLogCarry WPActualRankTwoCarrySource

noncomputable def cauchyC (t : ℚ) : ℕ → ℚ
  | 0 => (1 - t)⁻¹
  | j + 1 => (((2 * j + 1 : ℕ) : ℚ) /
      (((2 * j + 3 : ℕ) : ℚ) - t)) * cauchyC t j

noncomputable def momentWeight (t : ℚ) (n : ℕ) : ℚ :=
  if n % 2 = 0 then cauchyC t (n / 2) else 0

noncomputable def moment (t : ℚ) : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum fun n =>
    { toFun := fun a => a * momentWeight t n
      map_add' := by intro a b; ring
      map_smul' := by
        intro a b
        simp only [smul_eq_mul, RingHom.id_apply]
        ring }

noncomputable def secondKindBasis (t : ℚ) (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range n, monomial (n - 1 - k) (momentWeight t k)

noncomputable def secondKind (t : ℚ) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  Polynomial.lsum fun n =>
    { toFun := fun a => a • secondKindBasis t n
      map_add' := by intro a b; simp only [add_smul]
      map_smul' := by
        intro a b
        simp only [smul_eq_mul, RingHom.id_apply, smul_smul] }

@[simp] theorem moment_monomial (t a : ℚ) (n : ℕ) :
    moment t (monomial n a) = a * momentWeight t n := by
  change (monomial n a).sum (fun i b => b * momentWeight t i) = _
  exact sum_monomial_index a _ (by simp)

@[simp] theorem secondKind_monomial (t a : ℚ) (n : ℕ) :
    secondKind t (monomial n a) = a • secondKindBasis t n := by
  change (monomial n a).sum (fun i b => b • secondKindBasis t i) = _
  exact sum_monomial_index a _ (by simp)

@[simp] theorem momentWeight_even (t : ℚ) (j : ℕ) :
    momentWeight t (2 * j) = cauchyC t j := by
  have hmod : (2 * j) % 2 = 0 := by omega
  have hdiv : (2 * j) / 2 = j := by omega
  simp only [momentWeight, hmod, hdiv, ite_true]

@[simp] theorem momentWeight_odd (t : ℚ) (j : ℕ) :
    momentWeight t (2 * j + 1) = 0 := by
  have hmod : (2 * j + 1) % 2 = 1 := by omega
  simp only [momentWeight, hmod, Nat.one_ne_zero, if_false]

def Nonresonant (t : ℚ) : Prop :=
  ∀ n : ℕ, (((n + 1 : ℕ) : ℚ) - t) ≠ 0

@[simp] theorem moment_C_mul (t a : ℚ) (P : ℚ[X]) :
    moment t (C a * P) = a * moment t P := by
  simpa only [smul_eq_C_mul, smul_eq_mul] using (moment t).map_smul a P

@[simp] theorem secondKind_C_mul (t a : ℚ) (P : ℚ[X]) :
    secondKind t (C a * P) = C a * secondKind t P := by
  simpa only [smul_eq_C_mul] using (secondKind t).map_smul a P

@[simp] theorem moment_X_pow (t : ℚ) (n : ℕ) :
    moment t (X ^ n) = momentWeight t n := by
  simpa only [← C_mul_X_pow_eq_monomial, C_1, one_mul] using
    moment_monomial t 1 n

@[simp] theorem secondKind_C (t a : ℚ) : secondKind t (C a) = 0 := by
  simpa only [monomial_zero_left, secondKindBasis, Finset.range_zero,
    Finset.sum_empty, smul_zero] using secondKind_monomial t a 0

private theorem momentWeight_step (t : ℚ) (ht : Nonresonant t) (n : ℕ) :
    ((((n + 3 : ℕ) : ℚ) - t)) * momentWeight t (n + 2) =
      (((n + 1 : ℕ) : ℚ)) * momentWeight t n := by
  have hn : n = 2 * (n / 2) ∨ n = 2 * (n / 2) + 1 := by omega
  rcases hn with hn | hn
  · let j := n / 2
    have hn' : n = 2 * j := hn
    rw [hn', show 2 * j + 2 = 2 * (j + 1) by omega,
      momentWeight_even, momentWeight_even, cauchyC]
    have hden : (((2 * j + 3 : ℕ) : ℚ) - t) ≠ 0 :=
      ht (2 * j + 2)
    field_simp [hden]
  · let j := n / 2
    have hn' : n = 2 * j + 1 := hn
    rw [hn', show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by omega,
      momentWeight_odd, momentWeight_odd]
    ring

theorem pearson (t : ℚ) (ht : Nonresonant t) (P : ℚ[X]) :
    moment t ((1 - X ^ 2) * P.derivative - C (2 - t) * X * P) = 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ =>
      have he : (1 - X ^ 2) * (P + Q).derivative - C (2 - t) * X * (P + Q) =
          ((1 - X ^ 2) * P.derivative - C (2 - t) * X * P) +
          ((1 - X ^ 2) * Q.derivative - C (2 - t) * X * Q) := by
        rw [derivative_add]
        ring
      rw [he, _root_.map_add, ihP, ihQ, add_zero]
  | monomial n a =>
      cases n with
      | zero =>
          have he : (1 - X ^ 2) * (monomial 0 a).derivative -
              C (2 - t) * X * monomial 0 a = monomial 1 (-(2 - t) * a) := by
            rw [monomial_zero_left, derivative_C, mul_zero, zero_sub,
              ← C_mul_X_pow_eq_monomial, pow_one, _root_.map_mul, _root_.map_neg]
            ring
          rw [he, moment_monomial]
          have hw : momentWeight t 1 = 0 := by
            simpa using momentWeight_odd t 0
          rw [hw, mul_zero]
      | succ n =>
          have he : (1 - X ^ 2) * (monomial (n + 1) a).derivative -
              C (2 - t) * X * monomial (n + 1) a =
              monomial n (a * ((n + 1 : ℕ) : ℚ)) -
              monomial (n + 2) (a * (((n + 3 : ℕ) : ℚ) - t)) := by
            rw [derivative_monomial_succ]
            simp only [← C_mul_X_pow_eq_monomial, _root_.map_mul, _root_.map_sub,
              _root_.map_add, _root_.map_natCast, _root_.map_one, _root_.map_ofNat,
              pow_add, pow_one, pow_two]
            push_cast
            ring
          rw [he, _root_.map_sub, moment_monomial, moment_monomial]
          linear_combination -a * momentWeight_step t ht n

private theorem secondKindBasis_succ (t : ℚ) (n : ℕ) :
    secondKindBasis t (n + 1) = X * secondKindBasis t n + C (momentWeight t n) := by
  simp only [secondKindBasis, Finset.sum_range_succ, Nat.add_sub_cancel,
    Nat.sub_self, monomial_zero_left, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [X_mul_monomial, show n - 1 - k + 1 = n - k by omega]

theorem secondKind_X_mul (t : ℚ) (P : ℚ[X]) :
    secondKind t (X * P) = X * secondKind t P + C (moment t P) := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ =>
      simp only [mul_add, _root_.map_add, ihP, ihQ]
      ring
  | monomial n a =>
      simp only [X_mul_monomial, secondKind_monomial, secondKindBasis_succ,
        moment_monomial, smul_eq_C_mul, _root_.map_mul]
      ring

noncomputable def jacobi0 (t : ℚ) (P : ℚ[X]) : ℚ[X] :=
  (1 - X ^ 2) * P.derivative.derivative - C (2 - t) * X * P.derivative

theorem pearson_self_adjoint (t : ℚ) (ht : Nonresonant t) (P Q : ℚ[X]) :
    moment t (P * jacobi0 t Q) = moment t (Q * jacobi0 t P) := by
  have h1 := pearson t ht (P * Q.derivative)
  have h2 := pearson t ht (Q * P.derivative)
  have he1 : (1 - X ^ 2) * (P * Q.derivative).derivative -
      C (2 - t) * X * (P * Q.derivative) =
      P * jacobi0 t Q + (1 - X ^ 2) * P.derivative * Q.derivative := by
    rw [derivative_mul]
    unfold jacobi0
    ring
  have he2 : (1 - X ^ 2) * (Q * P.derivative).derivative -
      C (2 - t) * X * (Q * P.derivative) =
      Q * jacobi0 t P + (1 - X ^ 2) * P.derivative * Q.derivative := by
    rw [derivative_mul]
    unfold jacobi0
    ring
  rw [he1, _root_.map_add] at h1
  rw [he2, _root_.map_add] at h2
  linear_combination h1 - h2

theorem parameterA_eq_jacobi0 (d : ℕ) (t : ℚ) (P : ℚ[X]) :
    parameterA d t P = jacobi0 t P + C ((d : ℚ) * ((d : ℚ) + 1 - t)) * P := by
  dsimp only [parameterA, jacobi0, WPActualRankTwoGaussODE.legendreJacobi]
  simp only [_root_.map_mul, _root_.map_sub, _root_.map_add, _root_.map_natCast,
    _root_.map_one, _root_.map_ofNat]
  ring

theorem jacobi0_X_pow (t : ℚ) (k : ℕ) :
    jacobi0 t (X ^ k) =
      C ((k : ℚ) * ((k - 1 : ℕ) : ℚ)) * X ^ (k - 2) -
      C ((k : ℚ) * ((k : ℚ) + 1 - t)) * X ^ k := by
  cases k with
  | zero => simp [jacobi0]
  | succ k =>
      cases k with
      | zero => norm_num [jacobi0, _root_.map_ofNat]
      | succ k =>
          have hk2 : k + 1 + 1 - 2 = k := by omega
          simp only [jacobi0, derivative_X_pow_succ, derivative_C_mul,
            Nat.add_sub_cancel, hk2]
          simp only [Nat.cast_add, Nat.cast_one, _root_.map_mul, _root_.map_add,
            _root_.map_sub, _root_.map_natCast, _root_.map_one, _root_.map_ofNat]
          simp only [pow_add, pow_one]
          ring

theorem moment_orthogonal (t : ℚ) (ht : Nonresonant t)
    (d : ℕ) (Y : ℚ[X]) (hY : parameterA d t Y = 0) :
    ∀ k, k < d → moment t (Y * X ^ k) = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hkd
      have hs := congrArg (fun P : ℚ[X] => moment t (X ^ k * P)) hY
      rw [parameterA_eq_jacobi0] at hs
      have he : X ^ k * (jacobi0 t Y +
          C ((d : ℚ) * ((d : ℚ) + 1 - t)) * Y) =
          X ^ k * jacobi0 t Y +
          C ((d : ℚ) * ((d : ℚ) + 1 - t)) * (Y * X ^ k) := by ring
      rw [he, _root_.map_add, moment_C_mul, mul_zero, _root_.map_zero,
        pearson_self_adjoint t ht, jacobi0_X_pow] at hs
      have hm : Y * (C ((k : ℚ) * ((k - 1 : ℕ) : ℚ)) * X ^ (k - 2) -
          C ((k : ℚ) * ((k : ℚ) + 1 - t)) * X ^ k) =
          C ((k : ℚ) * ((k - 1 : ℕ) : ℚ)) * (Y * X ^ (k - 2)) -
          C ((k : ℚ) * ((k : ℚ) + 1 - t)) * (Y * X ^ k) := by ring
      rw [hm, _root_.map_sub, moment_C_mul, moment_C_mul] at hs
      have hprev : (k : ℚ) * ((k - 1 : ℕ) : ℚ) *
          moment t (Y * X ^ (k - 2)) = 0 := by
        by_cases hk2 : 2 ≤ k
        · rw [ih (k - 2) (by omega) (by omega), mul_zero]
        · have hk : k = 0 ∨ k = 1 := by omega
          rcases hk with rfl | rfl <;> norm_num
      have hgap : (d : ℚ) * ((d : ℚ) + 1 - t) -
          (k : ℚ) * ((k : ℚ) + 1 - t) ≠ 0 := by
        have hdk : (d : ℚ) - (k : ℚ) ≠ 0 := by
          apply sub_ne_zero.mpr
          exact_mod_cast (Nat.ne_of_gt hkd)
        have hden : (d : ℚ) + (k : ℚ) + 1 - t ≠ 0 := by
          simpa only [Nat.cast_add, Nat.cast_one] using ht (d + k)
        have he : (d : ℚ) * ((d : ℚ) + 1 - t) -
            (k : ℚ) * ((k : ℚ) + 1 - t) =
            ((d : ℚ) - (k : ℚ)) * ((d : ℚ) + (k : ℚ) + 1 - t) := by ring
        rw [he]
        exact mul_ne_zero hdk hden
      have hz : ((d : ℚ) * ((d : ℚ) + 1 - t) -
          (k : ℚ) * ((k : ℚ) + 1 - t)) * moment t (Y * X ^ k) = 0 := by
        linear_combination hs - hprev
      exact (mul_eq_zero.mp hz).resolve_left hgap

theorem secondKind_mul_X_pow_of_orthogonal (t : ℚ) (P : ℚ[X])
    (d : ℕ) (horth : ∀ k, k < d → moment t (P * X ^ k) = 0) :
    ∀ n, n ≤ d → secondKind t (P * X ^ n) = X ^ n * secondKind t P := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro hn
      have he : P * X ^ (n + 1) = X * (P * X ^ n) := by
        rw [pow_succ]
        ring
      rw [he, secondKind_X_mul, ih (by omega), horth n (by omega), C_0, add_zero]
      rw [pow_succ]
      ring

theorem secondKind_mul_of_orthogonal (t : ℚ) (P Q : ℚ[X])
    (d : ℕ) (hQ : Q.natDegree ≤ d)
    (horth : ∀ k, k < d → moment t (P * X ^ k) = 0) :
    secondKind t (P * Q) = Q * secondKind t P := by
  have he : P * Q = ∑ n ∈ Q.support, C (Q.coeff n) * (P * X ^ n) := by
    conv_lhs => arg 2; rw [Q.as_sum_support_C_mul_X_pow]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [he, map_sum]
  simp only [secondKind_C_mul]
  calc
    (∑ n ∈ Q.support, C (Q.coeff n) * secondKind t (P * X ^ n)) =
        ∑ n ∈ Q.support, C (Q.coeff n) * (X ^ n * secondKind t P) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [secondKind_mul_X_pow_of_orthogonal t P d horth n
        ((le_natDegree_of_mem_supp n hn).trans hQ)]
    _ = Q * secondKind t P := by
      conv_rhs => arg 1; rw [Q.as_sum_support_C_mul_X_pow]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      ring

theorem secondKind_square (t : ℚ) (ht : Nonresonant t)
    (d : ℕ) (Y : ℚ[X]) (hdeg : Y.natDegree ≤ d)
    (hY : parameterA d t Y = 0) :
    secondKind t (Y ^ 2) = Y * secondKind t Y := by
  rw [pow_two]
  exact secondKind_mul_of_orthogonal t Y Y d hdeg (moment_orthogonal t ht d Y hY)

noncomputable def rationalInverse (j : ℕ) : ℚ := 1 / (j : ℚ)

private theorem rational_units (m : ℕ) : UnitsTo rationalInverse m := by
  intro j hj hjm
  exact mul_one_div_cancel (by exact_mod_cast (Nat.ne_of_gt hj))

noncomputable def scaledQ (t : ℚ) (j : ℕ) : ℚ[X] :=
  (scaledEta rationalInverse j).eval (C t)
noncomputable def properQ (t : ℚ) (j : ℕ) : ℚ[X] :=
  (properEta rationalInverse j).eval (C t)

private theorem scaledQ_step (t : ℚ) (j : ℕ) :
    scaledQ t (j + 2) = C (1 / ((j + 2 : ℕ) : ℚ)) *
      (C (((2 * j + 3 : ℕ) : ℚ) - t) * X * scaledQ t (j + 1) -
       C (((j + 1 : ℕ) : ℚ) - t) * scaledQ t j) := by
  simp only [scaledQ, scaledEta, etaStep, rationalInverse, cc, tx, ActualTC1Family.eta,
    eval_mul, eval_sub, eval_C, eval_X, eval_natCast, _root_.map_sub, _root_.map_natCast]

private theorem properQ_step (t : ℚ) (j : ℕ) :
    properQ t (j + 2) = C (1 / ((j + 2 : ℕ) : ℚ)) *
      (C (((2 * j + 3 : ℕ) : ℚ) - t) * X * properQ t (j + 1) -
       C (((j + 1 : ℕ) : ℚ) - t) * properQ t j) := by
  simp only [properQ, properEta, etaStep, rationalInverse, cc, tx, ActualTC1Family.eta,
    eval_mul, eval_sub, eval_C, eval_X, eval_natCast, _root_.map_sub, _root_.map_natCast]

private theorem scaledQ_cleared (t : ℚ) (j : ℕ) :
    C ((j + 2 : ℕ) : ℚ) * scaledQ t (j + 2) =
      C (((2 * j + 3 : ℕ) : ℚ) - t) * X * scaledQ t (j + 1) -
      C (((j + 1 : ℕ) : ℚ) - t) * scaledQ t j := by
  rw [scaledQ_step, ← mul_assoc, ← C_mul,
    mul_one_div_cancel (by positivity : ((j + 2 : ℕ) : ℚ) ≠ 0), C_1, one_mul]

private theorem properQ_cleared (t : ℚ) (j : ℕ) :
    C ((j + 2 : ℕ) : ℚ) * properQ t (j + 2) =
      C (((2 * j + 3 : ℕ) : ℚ) - t) * X * properQ t (j + 1) -
      C (((j + 1 : ℕ) : ℚ) - t) * properQ t j := by
  rw [properQ_step, ← mul_assoc, ← C_mul,
    mul_one_div_cancel (by positivity : ((j + 2 : ℕ) : ℚ) ≠ 0), C_1, one_mul]

theorem scaledQ_equation (t : ℚ) (j : ℕ) : parameterA j t (scaledQ t j) = 0 := by
  exact scaledEta_eval_equation rationalInverse j (rational_units j) t

theorem scaledQ_degree (t : ℚ) (j : ℕ) : (scaledQ t j).natDegree ≤ j :=
  (eval_C_degree _ _).trans (scaledEta_T_degree _ _)

theorem moment_scaledQ_zero (t : ℚ) (ht : Nonresonant t)
    (j : ℕ) (hj : 0 < j) : moment t (scaledQ t j) = 0 := by
  have h := congrArg (moment t) (scaledQ_equation t j)
  rw [parameterA_eq_jacobi0, _root_.map_add, moment_C_mul, _root_.map_zero] at h
  have hp := pearson t ht (scaledQ t j).derivative
  change moment t (jacobi0 t (scaledQ t j)) = 0 at hp
  rw [hp, zero_add] at h
  have hn : (j : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hjt : (j : ℚ) + 1 - t ≠ 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using ht j
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hn hjt)

@[simp] theorem secondKind_X (t : ℚ) :
    secondKind t (X : ℚ[X]) = C (cauchyC t 0) := by
  simpa [← C_mul_X_pow_eq_monomial, secondKindBasis, momentWeight] using
    secondKind_monomial t 1 1

theorem properQ_eq_neg_secondKind (t : ℚ) (ht : Nonresonant t) (m : ℕ) :
    properQ t m = -secondKind t (scaledQ t m) := by
  induction m using Nat.twoStepInduction with
  | zero =>
      have hz : secondKind t (1 : ℚ[X]) = 0 := by
        simpa only [C_1] using secondKind_C t 1
      simp [properQ, properEta, scaledQ, scaledEta, hz]
  | one =>
      simp only [properQ, properEta, scaledQ, scaledEta, ActualTC1Family.eta, tx,
        eval_neg, eval_one, eval_mul, eval_sub, eval_X, eval_C]
      have he : (1 - C t : ℚ[X]) = C (1 - t) := by rw [_root_.map_sub, _root_.map_one]
      have ht0 : (1 - t) ≠ 0 := by
        simpa only [Nat.zero_add, Nat.cast_one] using ht 0
      rw [he, secondKind_C_mul, secondKind_X, cauchyC, ← C_mul,
        mul_inv_cancel₀ ht0, C_1]
  | more j ih0 ih1 =>
      have ha := congrArg (secondKind t) (scaledQ_cleared t j)
      have hn := properQ_cleared t j
      have hs0 : secondKind t (scaledQ t j) = -properQ t j := by
        linear_combination ih0
      have hs1 : secondKind t (scaledQ t (j + 1)) = -properQ t (j + 1) := by
        linear_combination ih1
      rw [(secondKind t).map_sub] at ha
      simp only [mul_assoc, secondKind_C_mul, secondKind_X_mul] at ha
      rw [moment_scaledQ_zero t ht (j + 1) (by omega), C_0, add_zero, hs0, hs1] at ha
      apply mul_left_cancel₀
        (show C ((j + 2 : ℕ) : ℚ) ≠ (0 : ℚ[X]) from C_ne_zero.mpr (by positivity))
      linear_combination hn + ha

noncomputable def metricQ (t : ℚ) (d : ℕ) : ℚ :=
  ∏ j ∈ Finset.range d, (1 - t / ((j + 1 : ℕ) : ℚ))

private theorem metricQ_ne_zero (t : ℚ) (ht : Nonresonant t) (d : ℕ) :
    metricQ t d ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hjq : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have he : 1 - t / ((j + 1 : ℕ) : ℚ) =
      ((((j + 1 : ℕ) : ℚ) - t) / ((j + 1 : ℕ) : ℚ)) := by field_simp [hjq]
  rw [he]
  exact div_ne_zero (ht j) hjq

noncomputable def normalizedY (t : ℚ) (d : ℕ) : ℚ[X] :=
  C ((metricQ t d)⁻¹) * scaledQ t d

private theorem scaledQ_eq_metric_mul_normalizedY
    (t : ℚ) (ht : Nonresonant t) (d : ℕ) :
    scaledQ t d = C (metricQ t d) * normalizedY t d := by
  rw [normalizedY, ← mul_assoc, ← C_mul,
    mul_inv_cancel₀ (metricQ_ne_zero t ht d), C_1, one_mul]

theorem normalizedY_equation (t : ℚ) (d : ℕ) :
    parameterA d t (normalizedY t d) = 0 := by
  have hs := scaledQ_equation t d
  rw [parameterA_eq_jacobi0] at hs ⊢
  unfold normalizedY
  simp only [jacobi0, derivative_C_mul] at hs ⊢
  linear_combination C ((metricQ t d)⁻¹) * hs

theorem normalizedY_degree (t : ℚ) (d : ℕ) :
    (normalizedY t d).natDegree ≤ d := by
  unfold normalizedY
  exact (natDegree_C_mul_le _ _).trans (scaledQ_degree t d)

theorem literal_proper_Cauchy_part (t : ℚ) (ht : Nonresonant t) (d : ℕ) :
    normalizedY t d * properQ t d =
      -C (metricQ t d) * secondKind t (normalizedY t d ^ 2) := by
  rw [properQ_eq_neg_secondKind t ht d,
    scaledQ_eq_metric_mul_normalizedY t ht d, secondKind_C_mul,
    secondKind_square t ht d (normalizedY t d)
      (normalizedY_degree t d) (normalizedY_equation t d)]
  ring

open WPPIntegralReduction WPActualNativeParameter

variable (p : ℕ) [Fact p.Prime]

theorem scaled_eval_subtype (m : ℕ) (hm : m < p) (t : integralRationals p) :
    ((scaledEta (fun j => smallIntegralInverse p j) m).eval (C t)).map
        (integralRationals p).subtype = scaledQ t.val m := by
  have h : ∀ m, m < p → ∀ t : integralRationals p,
      ((scaledEta (fun j => smallIntegralInverse p j) m).eval (C t)).map
        (integralRationals p).subtype = scaledQ t.val m := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero => intro hm t; simp [scaledEta, scaledQ]
    | one => intro hm t; simp [scaledEta, scaledQ, ActualTC1Family.eta, tx]
    | more j ih0 ih1 =>
        intro hm t
        rw [scaledQ_step]
        simp only [scaledEta, etaStep, cc, tx, ActualTC1Family.eta, eval_mul, eval_sub,
          eval_C, eval_X, eval_natCast, Polynomial.map_mul, Polynomial.map_sub,
          Polynomial.map_C, Polynomial.map_X, Polynomial.map_natCast,
          _root_.map_natCast, _root_.map_sub]
        simp only [Subring.subtype_apply]
        rw [smallIntegralInverse_value p (j + 2) (by omega) (by omega),
          ih0 (by omega) t, ih1 (by omega) t]
  exact h m hm t

theorem proper_eval_subtype (m : ℕ) (hm : m < p) (t : integralRationals p) :
    ((properEta (fun j => smallIntegralInverse p j) m).eval (C t)).map
        (integralRationals p).subtype = properQ t.val m := by
  have h : ∀ m, m < p → ∀ t : integralRationals p,
      ((properEta (fun j => smallIntegralInverse p j) m).eval (C t)).map
        (integralRationals p).subtype = properQ t.val m := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero => intro hm t; simp [properEta, properQ]
    | one => intro hm t; simp [properEta, properQ]
    | more j ih0 ih1 =>
        intro hm t
        rw [properQ_step]
        simp only [properEta, etaStep, cc, tx, ActualTC1Family.eta, eval_mul, eval_sub,
          eval_C, eval_X, eval_natCast, Polynomial.map_mul, Polynomial.map_sub,
          Polynomial.map_C, Polynomial.map_X, Polynomial.map_natCast,
          _root_.map_natCast, _root_.map_sub]
        simp only [Subring.subtype_apply]
        rw [smallIntegralInverse_value p (j + 2) (by omega) (by omega),
          ih0 (by omega) t, ih1 (by omega) t]
  exact h m hm t

theorem metricStar_value (hp : 19 ≤ p) :
    (metricStar p hp).val = metricQ ((p : ℚ) / 3) (p / 6) := by
  change (integralRationals p).subtype (metricStar p hp) = _
  rw [metricStar, map_prod, metricQ]
  apply Finset.prod_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  simp only [_root_.map_sub, _root_.map_one, _root_.map_mul]
  simp only [Subring.subtype_apply]
  rw [smallIntegralInverse_value p (j + 1) (by omega) (by omega), etaStar_value]
  ring

theorem actual_eta_nonresonant (hp : 19 ≤ p) : Nonresonant ((p : ℚ) / 3) := by
  intro n hz
  have hq : (p : ℚ) = 3 * ((n + 1 : ℕ) : ℚ) := by linear_combination -3 * hz
  have hn : p = 3 * (n + 1) := by exact_mod_cast hq
  have h3 : 3 ∣ p := ⟨n + 1, hn⟩
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h3 with h | h <;> omega

theorem actual_normalizedY_value (hp : 19 ≤ p) :
    normalizedY ((p : ℚ) / 3) (p / 6) = WPActualRankTwoParameter.rankJacobiNode p 1 := by
  rw [← balancedFirstIntegral_value p hp]
  simp only [balancedFirstIntegral, Polynomial.map_mul, Polynomial.map_C]
  rw [scaledStar, scaled_eval_subtype p (p / 6) (by omega), etaStar_value]
  unfold normalizedY
  change C ((metricQ ((p : ℚ) / 3) (p / 6))⁻¹) *
      scaledQ ((p : ℚ) / 3) (p / 6) =
    C ((metricStar p hp).val⁻¹) * scaledQ ((p : ℚ) / 3) (p / 6)
  rw [metricStar_value]

theorem actual_properQ_value (hp : 19 ≤ p) :
    properQ ((p : ℚ) / 3) (p / 6) = balancedProperQ p hp := by
  rw [balancedProperQ, balancedProper_literal,
    proper_eval_subtype p (p / 6) (by omega), etaStar_value]

theorem actual_SB82a (hp : 19 ≤ p) :
    WPActualRankTwoParameter.rankJacobiNode p 1 * balancedProperQ p hp =
      -C ((metricStar p hp).val) * secondKind ((p : ℚ) / 3)
        (WPActualRankTwoParameter.rankJacobiNode p 1 ^ 2) := by
  have h := literal_proper_Cauchy_part ((p : ℚ) / 3)
    (actual_eta_nonresonant p hp) (p / 6)
  rw [actual_normalizedY_value p hp, actual_properQ_value p hp] at h
  rw [← metricStar_value p hp] at h
  exact h

noncomputable def finiteUnitWindow (t : ℚ) (p : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (p - 1), monomial (p - 1 - k) (momentWeight t k)

noncomputable def finiteTailBasis (t : ℚ) (p l : ℕ) : ℚ[X] :=
  ∑ s ∈ Finset.range (l + 1), monomial (l - s) (momentWeight t (p - 1 + s))

noncomputable def finiteTail (t : ℚ) (p : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  Polynomial.lsum fun l =>
    { toFun := fun a => a • finiteTailBasis t p l
      map_add' := by intros; simp only [add_smul]
      map_smul' := by
        intros; simp only [smul_eq_mul, RingHom.id_apply, smul_smul] }

noncomputable def momentKernel (t : ℚ) (P : ℚ[X]) (p : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range p, monomial (p - 1 - k) (moment t (P * X ^ k))

@[simp] theorem finiteTail_monomial (t : ℚ) (p l : ℕ) (a : ℚ) :
    finiteTail t p (monomial l a) = a • finiteTailBasis t p l := by
  change (monomial l a).sum _ = _
  exact sum_monomial_index a _ (by simp)

theorem secondKindBasis_window (t : ℚ) (p l : ℕ) (hp : 0 < p) :
    secondKindBasis t (l + p) =
      X ^ l * finiteUnitWindow t p + finiteTailBasis t p l := by
  have hn : l + p = (p - 1) + (l + 1) := by omega
  unfold secondKindBasis
  rw [hn, Finset.sum_range_add]
  unfold finiteUnitWindow finiteTailBasis
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have he : (p - 1 + (l + 1)) - 1 - k = l + (p - 1 - k) := by omega
    rw [he, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, pow_add]
    ring
  · apply Finset.sum_congr rfl
    intro s hs
    have hs' := Finset.mem_range.mp hs
    have he : (p - 1 + (l + 1)) - 1 - (p - 1 + s) = l - s := by omega
    rw [he]

theorem secondKind_shift_window (t : ℚ) (P : ℚ[X]) (p : ℕ) (hp : 0 < p) :
    secondKind t (P * X ^ p) =
      P * finiteUnitWindow t p + finiteTail t p P := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ =>
      simp only [add_mul, _root_.map_add, ihP, ihQ]
      ring
  | monomial l a =>
      rw [monomial_mul_X_pow, secondKind_monomial,
        secondKindBasis_window t p l hp, finiteTail_monomial]
      simp only [smul_eq_C_mul, ← C_mul_X_pow_eq_monomial]
      ring

theorem momentKernel_succ (t : ℚ) (P : ℚ[X]) (p : ℕ) :
    momentKernel t P (p + 1) =
      X * momentKernel t P p + C (moment t (P * X ^ p)) := by
  unfold momentKernel
  rw [Finset.sum_range_succ, Finset.mul_sum]
  simp only [Nat.add_sub_cancel, Nat.sub_self, monomial_zero_left]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [X_mul_monomial, show p - 1 - k + 1 = p - k by omega]

theorem secondKind_shift_kernel (t : ℚ) (P : ℚ[X]) (p : ℕ) :
    secondKind t (P * X ^ p) =
      X ^ p * secondKind t P + momentKernel t P p := by
  induction p with
  | zero => simp [momentKernel]
  | succ p ih =>
      have he : P * X ^ (p + 1) = X * (P * X ^ p) := by
        rw [pow_succ]; ring
      rw [he, secondKind_X_mul, ih, momentKernel_succ, pow_succ]
      ring

/-- Exact finite Cauchy identity, including every high moment. -/
theorem finite_Cauchy_window_identity (t : ℚ) (P : ℚ[X]) (p : ℕ) (hp : 0 < p) :
    X ^ p * secondKind t P + momentKernel t P p =
      P * finiteUnitWindow t p + finiteTail t p P := by
  rw [← secondKind_shift_kernel, secondKind_shift_window t P p hp]

theorem finiteTail_degree (t : ℚ) (p : ℕ) (P : ℚ[X]) :
    (finiteTail t p P).natDegree ≤ P.natDegree := by
  change (P.sum (fun l a => a • finiteTailBasis t p l)).natDegree ≤ _
  rw [Polynomial.sum_def]
  apply natDegree_sum_le_of_forall_le
  intro l hl
  have hl' := le_natDegree_of_mem_supp l hl
  rw [smul_eq_C_mul]
  apply (natDegree_C_mul_le _ _).trans
  unfold finiteTailBasis
  apply natDegree_sum_le_of_forall_le
  intro s hs
  exact (natDegree_monomial_le _).trans ((Nat.sub_le l s).trans hl')

private theorem sum_range_even_odd {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (N : ℕ) :
    (∑ k ∈ Finset.range (2 * N), f k) =
      (∑ r ∈ Finset.range N, f (2 * r)) +
      ∑ r ∈ Finset.range N, f (2 * r + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 2 by omega, Finset.sum_range_add, ih]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.add_zero, zero_add]
      ac_rfl

noncomputable def unitWindow (t : ℚ) (N : ℕ) : ℚ[X] :=
  ∑ r ∈ Finset.range N, C (cauchyC t r) * X ^ (2 * (N - r))

theorem finiteUnitWindow_eq_unitWindow (t : ℚ) (N : ℕ) :
    finiteUnitWindow t (2 * N + 1) = unitWindow t N := by
  unfold finiteUnitWindow unitWindow
  rw [Nat.add_sub_cancel, sum_range_even_odd]
  have ho : (∑ r ∈ Finset.range N,
      monomial (2 * N - (2 * r + 1)) (momentWeight t (2 * r + 1))) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [momentWeight_odd, monomial_zero_right]
  rw [ho, add_zero]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  rw [momentWeight_even, show 2 * N - 2 * r = 2 * (N - r) by omega,
    ← C_mul_X_pow_eq_monomial]

noncomputable def kernelLow (t : ℚ) (P : ℚ[X]) (p D : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (p - 1 - D),
    monomial (p - 1 - k) (moment t (P * X ^ k))

noncomputable def kernelHigh (t : ℚ) (P : ℚ[X]) (p D : ℕ) : ℚ[X] :=
  ∑ s ∈ Finset.range (D + 1),
    monomial (D - s) (moment t (P * X ^ (p - 1 - D + s)))

theorem momentKernel_split (t : ℚ) (P : ℚ[X])
    (p D : ℕ) (hD : D ≤ p - 1) (hp : 0 < p) :
    momentKernel t P p = kernelLow t P p D + kernelHigh t P p D := by
  have hn : p = (p - 1 - D) + (D + 1) := by omega
  unfold momentKernel kernelLow kernelHigh
  conv_lhs => arg 1; rw [hn]
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hs' := Finset.mem_range.mp hs
  rw [show p - 1 - (p - 1 - D + s) = D - s by omega]

theorem kernelHigh_degree (t : ℚ) (P : ℚ[X]) (p D : ℕ) :
    (kernelHigh t P p D).natDegree ≤ D := by
  unfold kernelHigh
  apply natDegree_sum_le_of_forall_le
  intro s hs
  exact (natDegree_monomial_le _).trans (Nat.sub_le D s)

private theorem QO_low_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : ℚ[X]) (hP : P.natDegree ≤ 2 * (p / 6)) : QO p P = 0 := by
  unfold QO
  apply low_correction_both_projections_zero p hp
  exact NativeOriginalResidues.quadraticInverse_degree_of_le _ _ hP

/-- Both discarded bands are annihilated over Q, before eta is evaluated. -/
theorem rational_strict_window_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (t : ℚ) (P : ℚ[X]) (hP : P.natDegree ≤ 2 * (p / 6)) :
    QO p (X ^ p * secondKind t P) +
      QO p (kernelLow t P p (2 * (p / 6))) =
        QO p (P * finiteUnitWindow t p) := by
  have hD : 2 * (p / 6) ≤ p - 1 := by omega
  have ht := QO_low_zero p hp (finiteTail t p P)
    ((finiteTail_degree t p P).trans hP)
  have hk := QO_low_zero p hp (kernelHigh t P p (2 * (p / 6)))
    (kernelHigh_degree t P p (2 * (p / 6)))
  have he := congrArg (QO p) (finite_Cauchy_window_identity t P p (by omega))
  rw [momentKernel_split t P p _ hD (by omega), QO_add, QO_add,
    QO_add, hk, ht, add_zero, add_zero] at he
  exact he

noncomputable def fullUnitG (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : ℚ :=
  (metricStar p hp).val * QO p
    (kernelLow ((p : ℚ) / 3) (rankJacobiNode p 1 ^ 2) p (2 * (p / 6)))

/-- Actual full unit-window identity; the literal proper numerator is retained. -/
theorem actual_SB82c (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    QO p (X ^ p * (rankJacobiNode p 1 * balancedProperQ p hp)) =
      fullUnitG p hp - (metricStar p hp).val * QO p
        (rankJacobiNode p 1 ^ 2 * unitWindow ((p : ℚ) / 3) ((p - 1) / 2)) := by
  have hdeg : (rankJacobiNode p 1 ^ 2).natDegree ≤ 2 * (p / 6) := by
    rw [← actual_normalizedY_value p hp]
    simpa only [pow_two, two_mul] using natDegree_mul_le_of_le
      (normalizedY_degree ((p : ℚ) / 3) (p / 6))
      (normalizedY_degree ((p : ℚ) / 3) (p / 6))
  have he := rational_strict_window_source p hp ((p : ℚ) / 3)
    (rankJacobiNode p 1 ^ 2) hdeg
  have hn : p = 2 * ((p - 1) / 2) + 1 := by
    have hh := prime_half_identity p (by omega : 7 ≤ p)
    omega
  have hu : finiteUnitWindow ((p : ℚ) / 3) p =
      unitWindow ((p : ℚ) / 3) ((p - 1) / 2) := by
    conv_lhs => arg 2; rw [hn]
    exact finiteUnitWindow_eq_unitWindow _ _
  rw [hu] at he
  rw [actual_SB82a p hp]
  have hm : X ^ p * (-C (metricStar p hp).val *
      secondKind ((p : ℚ) / 3) (rankJacobiNode p 1 ^ 2)) =
      C (-(metricStar p hp).val) *
        (X ^ p * secondKind ((p : ℚ) / 3) (rankJacobiNode p 1 ^ 2)) := by
    rw [_root_.map_neg]; ring
  rw [hm, QO_C_mul]
  unfold fullUnitG
  linear_combination -(metricStar p hp).val * he

section ReciprocalProducts
variable {R : Type*} [CommRing R]

noncomputable def reciprocalParameter (u : ℕ → R) (m : ℕ) : R[X] :=
  ∏ r ∈ Finset.range m, (1 - C (u r) * X)

@[simp] theorem reciprocalParameter_coeff_zero (u : ℕ → R) (m : ℕ) :
    (reciprocalParameter u m).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero]
  simp [reciprocalParameter, eval_prod]

theorem reciprocalParameter_coeff_one (u : ℕ → R) (m : ℕ) :
    (reciprocalParameter u m).coeff 1 = -(∑ r ∈ Finset.range m, u r) := by
  induction m with
  | zero => simp [reciprocalParameter, coeff_one]
  | succ m ih =>
      have he : reciprocalParameter u (m + 1) = reciprocalParameter u m -
          C (u m) * (reciprocalParameter u m * X) := by
        rw [reciprocalParameter, Finset.prod_range_succ]
        unfold reciprocalParameter
        ring
      rw [he, coeff_sub, coeff_C_mul, coeff_mul_X, ih,
        reciprocalParameter_coeff_zero, mul_one, Finset.sum_range_succ]
      ring
end ReciprocalProducts

noncomputable def metricParameter (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  reciprocalParameter (fun r => smallIntegralInverse p (r + 1)) (p / 6)
noncomputable def oddDenParameter (p j : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  reciprocalParameter (fun r => smallIntegralInverse p (2 * r + 1)) (j + 1)
noncomputable def oddSumIntegral (p j : ℕ) [Fact p.Prime] : integralRationals p :=
  ∑ r ∈ Finset.range (j + 1), smallIntegralInverse p (2 * r + 1)
noncomputable def cauchyLinear (p j : ℕ) [Fact p.Prime] : integralRationals p :=
  oddSumIntegral p j - integralHarmonic p (p / 6)
noncomputable def cauchyNumerator (p j : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  metricParameter p - oddDenParameter p j * (1 + C (cauchyLinear p j) * X)
noncomputable def cauchyRemainderParameter (p j : ℕ) [Fact p.Prime] :
    (integralRationals p)[X] := (cauchyNumerator p j).divX.divX

theorem cauchyNumerator_coeff_zero (p j : ℕ) [Fact p.Prime] :
    (cauchyNumerator p j).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero]
  simp [cauchyNumerator, metricParameter, oddDenParameter, reciprocalParameter, eval_prod]

theorem cauchyNumerator_coeff_one (p j : ℕ) [Fact p.Prime] :
    (cauchyNumerator p j).coeff 1 = 0 := by
  have he : oddDenParameter p j * (1 + C (cauchyLinear p j) * X) =
      oddDenParameter p j + C (cauchyLinear p j) * (oddDenParameter p j * X) := by ring
  rw [cauchyNumerator, he, coeff_sub, coeff_add, coeff_C_mul, coeff_mul_X]
  simp only [metricParameter, oddDenParameter, reciprocalParameter_coeff_zero,
    reciprocalParameter_coeff_one, mul_one]
  unfold cauchyLinear oddSumIntegral integralHarmonic
  ring

noncomputable def oddDenStar (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (j : ℕ) :
    integralRationals p := (oddDenParameter p j).eval (etaStar p hp)

theorem oddDenStar_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (j : ℕ) :
    residueHom p (oddDenStar p hp j) = 1 := by
  simp only [oddDenStar, oddDenParameter, reciprocalParameter, eval_prod,
    eval_sub, eval_one, eval_mul, eval_C, eval_X, map_prod, _root_.map_sub,
    _root_.map_one, _root_.map_mul, etaStar_field, mul_zero, sub_zero, Finset.prod_const_one]

theorem oddDenStar_unit (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (j : ℕ) :
    (oddDenStar p hp j).val ≠ 0 ∧
      (oddDenStar p hp j).val⁻¹ ∈ integralRationals p := by
  apply integral_inverse_of_residue_ne_zero
  rw [oddDenStar_field]
  exact one_ne_zero

noncomputable def oddDenStarInverse (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (j : ℕ) :
    integralRationals p :=
  ⟨(oddDenStar p hp j).val⁻¹, (oddDenStar_unit p hp j).2⟩

theorem oddDenStar_mul_inverse (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (j : ℕ) :
    oddDenStar p hp j * oddDenStarInverse p hp j = 1 := by
  apply Subtype.ext
  exact mul_inv_cancel₀ (oddDenStar_unit p hp j).1

noncomputable def weightedCauchyIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (j : ℕ) : integralRationals p :=
  metricStar p hp * smallIntegralInverse p (2 * j + 1) * oddDenStarInverse p hp j
noncomputable def weightedCauchyRemainder (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (j : ℕ) : integralRationals p :=
  smallIntegralInverse p (2 * j + 1) * (2 * integralSixth p (by omega)) ^ 2 *
    (cauchyRemainderParameter p j).eval (etaStar p hp) * oddDenStarInverse p hp j

theorem metricParameter_star (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (metricParameter p).eval (etaStar p hp) = metricStar p hp := by
  simp only [metricParameter, reciprocalParameter, eval_prod, eval_sub,
    eval_one, eval_mul, eval_C, eval_X, metricStar]

/-- Exact integral p² expansion, with a fixed divX² remainder. -/
theorem actual_weighted_cauchy_Taylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (j : ℕ) :
    weightedCauchyIntegral p hp j = smallIntegralInverse p (2 * j + 1) +
      (p : integralRationals p) * (smallIntegralInverse p (2 * j + 1) *
        (2 * integralSixth p (by omega)) * cauchyLinear p j) +
      (p : integralRationals p) ^ 2 * weightedCauchyRemainder p hp j := by
  have he := polynomial_two_term_eval (cauchyNumerator p j) (etaStar p hp)
  rw [cauchyNumerator_coeff_zero, cauchyNumerator_coeff_one,
    mul_zero, zero_add, zero_add] at he
  change (cauchyNumerator p j).eval (etaStar p hp) =
    (etaStar p hp) ^ 2 * (cauchyRemainderParameter p j).eval (etaStar p hp) at he
  simp only [cauchyNumerator, eval_sub, eval_mul, eval_add, eval_one,
    eval_C, eval_X, metricParameter_star] at he
  change metricStar p hp - oddDenStar p hp j *
      (1 + cauchyLinear p j * etaStar p hp) =
    etaStar p hp ^ 2 * (cauchyRemainderParameter p j).eval (etaStar p hp) at he
  have hm := congrArg (fun x : integralRationals p =>
    smallIntegralInverse p (2 * j + 1) * oddDenStarInverse p hp j * x) he
  have hc : smallIntegralInverse p (2 * j + 1) * oddDenStarInverse p hp j *
      (oddDenStar p hp j * (1 + cauchyLinear p j * etaStar p hp)) =
      smallIntegralInverse p (2 * j + 1) *
        (1 + cauchyLinear p j * etaStar p hp) := by
    calc
      _ = smallIntegralInverse p (2 * j + 1) *
          (oddDenStar p hp j * oddDenStarInverse p hp j) *
          (1 + cauchyLinear p j * etaStar p hp) := by ring
      _ = _ := by rw [oddDenStar_mul_inverse, mul_one]
  rw [mul_sub, hc] at hm
  unfold weightedCauchyIntegral weightedCauchyRemainder
  rw [etaStar] at hm ⊢
  linear_combination hm

noncomputable def oddDenQ (t : ℚ) (j : ℕ) : ℚ :=
  ∏ r ∈ Finset.range (j + 1), (1 - t / ((2 * r + 1 : ℕ) : ℚ))

private theorem oddDenQ_ne_zero (t : ℚ) (ht : Nonresonant t) (j : ℕ) :
    oddDenQ t j ≠ 0 := by
  unfold oddDenQ
  apply Finset.prod_ne_zero_iff.mpr
  intro r hr
  have ha : ((2 * r + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hb : ((2 * r + 1 : ℕ) : ℚ) - t ≠ 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using ht (2 * r)
  have he : 1 - t / ((2 * r + 1 : ℕ) : ℚ) =
      (((2 * r + 1 : ℕ) : ℚ) - t) / ((2 * r + 1 : ℕ) : ℚ) := by field_simp [ha]
  rw [he]
  exact div_ne_zero hb ha

theorem cauchyC_mul_oddDen (t : ℚ) (ht : Nonresonant t) (j : ℕ) :
    cauchyC t j * oddDenQ t j = 1 / ((2 * j + 1 : ℕ) : ℚ) := by
  induction j with
  | zero =>
      simp only [oddDenQ, Finset.prod_range_succ, Finset.prod_range_zero,
        Nat.mul_zero, Nat.zero_add, Nat.cast_one, div_one, one_mul, cauchyC]
      exact inv_mul_cancel₀ (ht 0)
  | succ j ih =>
      have hb : ((2 * j + 3 : ℕ) : ℚ) ≠ 0 := by positivity
      have hbt : ((2 * j + 3 : ℕ) : ℚ) - t ≠ 0 := by
        simpa only [show 2 * j + 2 + 1 = 2 * j + 3 by omega] using ht (2 * j + 2)
      have hf : (((2 * j + 1 : ℕ) : ℚ) /
          (((2 * j + 3 : ℕ) : ℚ) - t)) *
          (1 - t / ((2 * j + 3 : ℕ) : ℚ)) =
          ((2 * j + 1 : ℕ) : ℚ) / ((2 * j + 3 : ℕ) : ℚ) := by
        field_simp [hb, hbt]
      have hd : oddDenQ t (j + 1) = oddDenQ t j *
          (1 - t / ((2 * j + 3 : ℕ) : ℚ)) := by
        unfold oddDenQ
        rw [Finset.prod_range_succ]
        congr 1
      rw [hd, cauchyC]
      calc
        _ = ((((2 * j + 1 : ℕ) : ℚ) /
            (((2 * j + 3 : ℕ) : ℚ) - t)) *
            (1 - t / ((2 * j + 3 : ℕ) : ℚ))) *
            (cauchyC t j * oddDenQ t j) := by ring
        _ = (((2 * j + 1 : ℕ) : ℚ) / ((2 * j + 3 : ℕ) : ℚ)) *
            (1 / ((2 * j + 1 : ℕ) : ℚ)) := by rw [hf, ih]
        _ = _ := by
          have ha : ((2 * j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
          rw [show 2 * (j + 1) + 1 = 2 * j + 3 by omega]
          field_simp [ha, hb]

theorem cauchyC_product_value (t : ℚ) (ht : Nonresonant t) (j : ℕ) :
    cauchyC t j = (1 / ((2 * j + 1 : ℕ) : ℚ)) * (oddDenQ t j)⁻¹ := by
  have he := cauchyC_mul_oddDen t ht j
  have hd := oddDenQ_ne_zero t ht j
  apply (eq_div_iff hd).mpr
  simpa only [div_eq_mul_inv] using he

theorem oddDenStar_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℕ) (hj : j < (p - 1) / 2) :
    (oddDenStar p hp j).val = oddDenQ ((p : ℚ) / 3) j := by
  change (integralRationals p).subtype ((oddDenParameter p j).eval (etaStar p hp)) = _
  simp only [oddDenParameter, reciprocalParameter, eval_prod, eval_sub,
    eval_one, eval_mul, eval_C, eval_X, map_prod, _root_.map_sub, _root_.map_one, _root_.map_mul,
    oddDenQ]
  apply Finset.prod_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  simp only [Subring.subtype_apply]
  rw [smallIntegralInverse_value p (2 * r + 1) (by omega) (by omega), etaStar_value]
  ring

/-- Only the strict unit window is transported into Z_(p). -/
theorem actual_weighted_cauchy_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℕ) (hj : j < (p - 1) / 2) :
    (weightedCauchyIntegral p hp j).val =
      (metricStar p hp).val * cauchyC ((p : ℚ) / 3) j := by
  change (metricStar p hp).val * (smallIntegralInverse p (2 * j + 1)).val *
    (oddDenStar p hp j).val⁻¹ = _
  rw [smallIntegralInverse_value p (2 * j + 1) (by omega) (by omega),
    oddDenStar_value p hp j hj,
    cauchyC_product_value _ (actual_eta_nonresonant p hp)]
  ring

noncomputable def fieldOdd (p m : ℕ) : ZMod p :=
  ∑ r ∈ Finset.range m, ((2 * r + 1 : ℕ) : ZMod p)⁻¹

@[simp] theorem fieldOdd_succ (p m : ℕ) :
    fieldOdd p (m + 1) = fieldOdd p m + ((2 * m + 1 : ℕ) : ZMod p)⁻¹ := by
  simp only [fieldOdd, Finset.sum_range_succ]

theorem fieldOdd_half (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    fieldOdd p ((p - 1) / 2) =
      (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
  let N := (p - 1) / 2
  have hn : 2 * N = p - 1 := by
    have hh := prime_half_identity p (by omega : 7 ≤ p)
    dsimp [N]; omega
  have hs : fieldHarmonic p (2 * N) =
      fieldOdd p N + (2 : ZMod p)⁻¹ * fieldHarmonic p N := by
    unfold fieldHarmonic fieldOdd
    rw [sum_range_even_odd, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    have he : ((2 * r + 1 + 1 : ℕ) : ZMod p) =
        (2 : ZMod p) * ((r + 1 : ℕ) : ZMod p) := by push_cast; ring
    rw [he, mul_inv_rev]
    ring
  rw [hn, WPActualHalfHarmonic.actual_full_harmonic_zero p (by omega),
    WPActualHalfHarmonic.actual_harmonic_half p (by omega)] at hs
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  change fieldOdd p N = _
  have hi : (2 : ZMod p)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  linear_combination -hs +
    (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) * hi

/-- Downward reflection uses only denominators strictly below p. -/
theorem fieldOdd_reflected (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (q : ℕ) (hq : q < (p - 1) / 2) :
    fieldOdd p ((p - 1) / 2 - q) =
      (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) +
        fieldHarmonic p q / 2 := by
  let N := (p - 1) / 2
  have hn : 2 * N + 1 = p := by
    have hh := prime_half_identity p (by omega : 7 ≤ p)
    dsimp [N]; omega
  change fieldOdd p (N - q) = _
  change q < N at hq
  induction q with
  | zero => simpa only [Nat.sub_zero, fieldHarmonic_zero, zero_div, add_zero]
      using fieldOdd_half p hp
  | succ q ih =>
      have hi := ih (by omega)
      have he : N - q = (N - (q + 1)) + 1 := by omega
      have hs := fieldOdd_succ p (N - (q + 1))
      rw [← he] at hs
      have hnat : (2 * (N - (q + 1)) + 1) + 2 * (q + 1) = p := by omega
      have hcast := congrArg (fun n : ℕ => (n : ZMod p)) hnat
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
        ZMod.natCast_self] at hcast
      have hd : ((2 * (N - (q + 1)) + 1 : ℕ) : ZMod p) =
          -((2 : ZMod p) * ((q + 1 : ℕ) : ZMod p)) := by
        push_cast
        linear_combination hcast
      rw [hd, inv_neg, mul_inv_rev] at hs
      rw [fieldHarmonic_succ]
      simp only [div_eq_mul_inv]
      linear_combination hi - hs

theorem oddSumIntegral_field (p : ℕ) [Fact p.Prime]
    (j : ℕ) (hj : j < (p - 1) / 2) :
    residueHom p (oddSumIntegral p j) = fieldOdd p (j + 1) := by
  rw [oddSumIntegral, map_sum, fieldOdd]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  exact smallIntegralInverse_field p (2 * r + 1) (by omega) (by omega)

noncomputable def oddReflectionNumerator (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : integralRationals p :=
  oddSumIntegral p ((p - 1) / 2 - r) -
    (WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) -
    (3 * integralSixth p (by omega)) * integralHarmonic p (r - 1)

theorem oddReflectionNumerator_field (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hr : 1 ≤ r) (hrN : r ≤ (p - 1) / 2) :
    residueHom p (oddReflectionNumerator p r hp) = 0 := by
  have hj : (p - 1) / 2 - r < (p - 1) / 2 := by omega
  have he : (p - 1) / 2 - r + 1 = (p - 1) / 2 - (r - 1) := by omega
  simp only [oddReflectionNumerator, _root_.map_sub, _root_.map_mul, _root_.map_ofNat, map_intCast,
    oddSumIntegral_field p _ hj, integralSixth_field,
    integralHarmonic_field p (r - 1) (by omega)]
  rw [he, fieldOdd_reflected p hp (r - 1) (by omega)]
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 := small_cast_ne_zero p 6 (by omega) (by omega)
  field_simp [h2, h6]
  ring

/-- Fixed rational quotient of the actual reflected numerator. -/
noncomputable def oddReflectionCarry (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hr : 1 ≤ r) (hrN : r ≤ (p - 1) / 2) : integralRationals p :=
  ⟨(oddReflectionNumerator p r hp).val / (p : ℚ), by
    apply WPActualChiSource.divide_prime_integral p _
    · exact (oddReflectionNumerator p r hp).property
    · change residueHom p (oddReflectionNumerator p r hp) = 0
      exact oddReflectionNumerator_field p r hp hr hrN⟩

theorem oddReflectionCarry_source (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hr : 1 ≤ r) (hrN : r ≤ (p - 1) / 2) :
    oddReflectionNumerator p r hp =
      (p : integralRationals p) * oddReflectionCarry p r hp hr hrN := by
  apply Subtype.ext
  change (oddReflectionNumerator p r hp).val =
    (p : ℚ) * ((oddReflectionNumerator p r hp).val / (p : ℚ))
  field_simp [show (p : ℚ) ≠ 0 by positivity]

noncomputable def cauchyHalf (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    integralRationals p := 3 * integralSixth p (by omega)

theorem cauchyHalf_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (cauchyHalf p hp).val = (1 / 2 : ℚ) := by
  change (3 : ℚ) * (1 / 6) = 1 / 2
  norm_num

theorem cauchyHalf_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (cauchyHalf p hp) = (1 / 2 : ZMod p) := by
  rw [cauchyHalf, _root_.map_mul, _root_.map_ofNat, integralSixth_field]
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 := small_cast_ne_zero p 6 (by omega) (by omega)
  field_simp [h2, h6]
  ring

noncomputable def universalCoefficient (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : integralRationals p :=
  (cauchyHalf p hp) ^ 2 * (smallIntegralInverse p r) ^ 2 +
    integralSixth p (by omega) * smallIntegralInverse p r *
      ((WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) -
        integralHarmonic p (p / 6)) +
    integralSixth p (by omega) * cauchyHalf p hp * smallIntegralInverse p r *
      integralHarmonic p (r - 1)

noncomputable def universalCoefficientRemainder (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hr : 1 ≤ r) (hrN : r ≤ (p - 1) / 2) : integralRationals p :=
  weightedCauchyRemainder p hp ((p - 1) / 2 - r) +
    (cauchyHalf p hp) ^ 2 * (smallIntegralInverse p r) ^ 2 *
      smallIntegralInverse p (2 * ((p - 1) / 2 - r) + 1) +
    integralSixth p (by omega) * smallIntegralInverse p r *
      smallIntegralInverse p (2 * ((p - 1) / 2 - r) + 1) *
        cauchyLinear p ((p - 1) / 2 - r) -
    integralSixth p (by omega) * smallIntegralInverse p r *
      oddReflectionCarry p r hp hr hrN

theorem cauchyLinear_reflected_source (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hr : 1 ≤ r) (hrN : r ≤ (p - 1) / 2) :
    cauchyLinear p ((p - 1) / 2 - r) =
      (WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) -
        integralHarmonic p (p / 6) +
      cauchyHalf p hp * integralHarmonic p (r - 1) +
      (p : integralRationals p) * oddReflectionCarry p r hp hr hrN := by
  have he := oddReflectionCarry_source p r hp hr hrN
  unfold oddReflectionNumerator cauchyLinear cauchyHalf at *
  linear_combination he

private theorem reflected_inverse_source (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hr : 1 ≤ r) (hrN : r ≤ (p - 1) / 2) :
    smallIntegralInverse p (2 * ((p - 1) / 2 - r) + 1) =
      -cauchyHalf p hp * smallIntegralInverse p r +
      (p : integralRationals p) * cauchyHalf p hp * smallIntegralInverse p r *
        smallIntegralInverse p (2 * ((p - 1) / 2 - r) + 1) := by
  let a := 2 * ((p - 1) / 2 - r) + 1
  have hn : a + 2 * r = p := by
    have hh := prime_half_identity p (by omega : 7 ≤ p)
    dsimp [a]; omega
  have ha : 0 < a := by dsimp [a]; omega
  have hap : a < p := by omega
  have hrp : r < p := by omega
  apply Subtype.ext
  change (smallIntegralInverse p a).val =
    -(cauchyHalf p hp).val * (smallIntegralInverse p r).val +
      (p : ℚ) * (cauchyHalf p hp).val * (smallIntegralInverse p r).val *
        (smallIntegralInverse p a).val
  rw [smallIntegralInverse_value p a ha hap,
    smallIntegralInverse_value p r (by omega) hrp, cauchyHalf_value]
  have hq : (a : ℚ) = (p : ℚ) - 2 * (r : ℚ) := by
    have h := congrArg (fun n : ℕ => (n : ℚ)) hn
    push_cast at h
    linear_combination h
  rw [hq]
  have har : (p : ℚ) - 2 * (r : ℚ) ≠ 0 := by
    rw [← hq]; positivity
  have hrq : (r : ℚ) ≠ 0 := by positivity
  field_simp [har, hrq]
  ring

private theorem reflected_inverse_precision_two (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hr : 1 ≤ r) (hrN : r ≤ (p - 1) / 2) :
    smallIntegralInverse p (2 * ((p - 1) / 2 - r) + 1) =
      -cauchyHalf p hp * smallIntegralInverse p r -
      (p : integralRationals p) * (cauchyHalf p hp) ^ 2 *
        (smallIntegralInverse p r) ^ 2 +
      (p : integralRationals p) ^ 2 * (cauchyHalf p hp) ^ 2 *
        (smallIntegralInverse p r) ^ 2 *
          smallIntegralInverse p (2 * ((p - 1) / 2 - r) + 1) := by
  have he := reflected_inverse_source p r hp hr hrN
  linear_combination he +
    ((p : integralRationals p) * cauchyHalf p hp * smallIntegralInverse p r) * he

/-- Exact p² identity for every retained coefficient, including its carry. -/
theorem actual_universal_coefficient_precision_two (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hr : 1 ≤ r) (hrN : r ≤ (p - 1) / 2) :
    weightedCauchyIntegral p hp ((p - 1) / 2 - r) =
      -cauchyHalf p hp * smallIntegralInverse p r -
      (p : integralRationals p) * universalCoefficient p r hp +
      (p : integralRationals p) ^ 2 *
        universalCoefficientRemainder p r hp hr hrN := by
  have ht := actual_weighted_cauchy_Taylor p hp ((p - 1) / 2 - r)
  have h1 := reflected_inverse_source p r hp hr hrN
  have h2 := reflected_inverse_precision_two p r hp hr hrN
  have hd := cauchyLinear_reflected_source p r hp hr hrN
  have hthird : 2 * integralSixth p (by omega) * cauchyHalf p hp =
      integralSixth p (by omega) := by
    apply Subtype.ext
    change (2 : ℚ) * (1 / 6) * (3 * (1 / 6)) = 1 / 6
    norm_num
  unfold universalCoefficient universalCoefficientRemainder
  linear_combination ht + h2 +
    ((p : integralRationals p) * (2 * integralSixth p (by omega)) *
      cauchyLinear p ((p - 1) / 2 - r)) * h1 -
    ((p : integralRationals p) * integralSixth p (by omega) *
      smallIntegralInverse p r) * hd +
    (((p : integralRationals p) ^ 2 * smallIntegralInverse p r *
        smallIntegralInverse p (2 * ((p - 1) / 2 - r) + 1) -
      (p : integralRationals p) * smallIntegralInverse p r) *
        cauchyLinear p ((p - 1) / 2 - r)) * hthird

noncomputable def weightedWindowIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (integralRationals p)[X] :=
  ∑ s ∈ Finset.range ((p - 1) / 2),
    C (weightedCauchyIntegral p hp ((p - 1) / 2 - 1 - s)) * X ^ (2 * (s + 1))
noncomputable def evenSeriesIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (integralRationals p)[X] :=
  ∑ s ∈ Finset.range ((p - 1) / 2),
    C (cauchyHalf p hp * smallIntegralInverse p (s + 1)) * X ^ (2 * (s + 1))
noncomputable def zeroEndEvenIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (integralRationals p)[X] :=
  evenSeriesIntegral p hp -
    C (cauchyHalf p hp * integralHarmonic p ((p - 1) / 2))
noncomputable def universalPolynomialIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (integralRationals p)[X] :=
  ∑ s ∈ Finset.range ((p - 1) / 2),
    C (universalCoefficient p (s + 1) hp) * X ^ (2 * (s + 1))
noncomputable def universalRemainderIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (integralRationals p)[X] :=
  ∑ s ∈ Finset.range ((p - 1) / 2),
    if hs : s < (p - 1) / 2 then
      C (universalCoefficientRemainder p (s + 1) hp (by omega) (by omega)) *
        X ^ (2 * (s + 1)) else 0

theorem weightedWindowIntegral_value (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    (weightedWindowIntegral p hp).map (integralRationals p).subtype =
      C (metricStar p hp).val * unitWindow ((p : ℚ) / 3) ((p - 1) / 2) := by
  let N := (p - 1) / 2
  simp only [weightedWindowIntegral, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Subring.subtype_apply]
  have he : (∑ s ∈ Finset.range N,
      C ((weightedCauchyIntegral p hp (N - 1 - s)).val) * X ^ (2 * (s + 1))) =
      ∑ j ∈ Finset.range N,
        C ((weightedCauchyIntegral p hp j).val) * X ^ (2 * (N - j)) := by
    have hh := Finset.sum_range_reflect
      (fun j => C ((weightedCauchyIntegral p hp j).val) *
        (X : ℚ[X]) ^ (2 * (N - j))) N
    rw [← hh]
    apply Finset.sum_congr rfl
    intro s hs
    have hs' := Finset.mem_range.mp hs
    congr 1
    congr 1
    omega
  change (∑ s ∈ Finset.range N,
      C ((weightedCauchyIntegral p hp (N - 1 - s)).val) * X ^ (2 * (s + 1))) =
    C ((metricStar p hp).val) * unitWindow ((p : ℚ) / 3) N
  rw [he]
  unfold unitWindow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [actual_weighted_cauchy_value p hp j (Finset.mem_range.mp hj), _root_.map_mul]
  ring

/-- The universal second coefficient with its full actual p² error. -/
theorem actual_universal_polynomial_precision_two (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    zeroEndEvenIntegral p hp + weightedWindowIntegral p hp =
      -C (cauchyHalf p hp * integralHarmonic p ((p - 1) / 2)) -
      C (p : integralRationals p) * universalPolynomialIntegral p hp +
      C ((p : integralRationals p) ^ 2) * universalRemainderIntegral p hp := by
  have he : weightedWindowIntegral p hp = -evenSeriesIntegral p hp -
      C (p : integralRationals p) * universalPolynomialIntegral p hp +
      C ((p : integralRationals p) ^ 2) * universalRemainderIntegral p hp := by
    unfold weightedWindowIntegral evenSeriesIntegral universalPolynomialIntegral
      universalRemainderIntegral
    rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have hs' := Finset.mem_range.mp hs
    rw [dif_pos hs', show (p - 1) / 2 - 1 - s = (p - 1) / 2 - (s + 1) by omega,
      actual_universal_coefficient_precision_two p (s + 1) hp (by omega) (by omega)]
    simp only [_root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_neg, _root_.map_pow]
    ring
  rw [he]
  unfold zeroEndEvenIntegral
  ring

private theorem QO_zero_local {K : Type*} [Field K] (p : ℕ) :
    QO p (0 : K[X]) = 0 := by
  have hc : contract 2 (0 : K[X]) = 0 := by
    ext n
    simp only [coeff_contract (by norm_num : (2 : ℕ) ≠ 0), coeff_zero]
  unfold QO NativeQuadraticInverse.quadraticInverse
  rw [hc, zero_comp]
  simp [ResidualProjection.Ij, WPFiniteNC122Residue.canceledDensity]

private theorem QO_sum_local {K : Type*} [Field K]
    {ι : Type*} (p : ℕ) (s : Finset ι) (f : ι → K[X]) :
    QO p (∑ i ∈ s, f i) = ∑ i ∈ s, QO p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [QO_zero_local]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, QO_add, ih, Finset.sum_insert hi]

private theorem QO_monomial_local {K : Type*} [Field K]
    (p n : ℕ) (a : K) : QO p (monomial n a) = a * QO p (X ^ n : K[X]) := by
  rw [← C_mul_X_pow_eq_monomial, QO_C_mul]

private theorem QO_X_odd {K : Type*} [Field K] (p r : ℕ) :
    QO p (X ^ (2 * r + 1) : K[X]) = 0 := by
  have hc : contract 2 (X ^ (2 * r + 1) : K[X]) = 0 := by
    ext n
    simp only [coeff_contract (by norm_num : (2 : ℕ) ≠ 0), coeff_X_pow, coeff_zero]
    split_ifs with hn
    · omega
    · rfl
  unfold QO NativeQuadraticInverse.quadraticInverse
  rw [hc, zero_comp]
  simp [ResidualProjection.Ij, WPFiniteNC122Residue.canceledDensity]

noncomputable def canonicalUnitG (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : ℚ :=
  (metricStar p hp).val *
    ∑ r ∈ Finset.range ((p - 1) / 2 - p / 6),
      moment ((p : ℚ) / 3) (rankJacobiNode p 1 ^ 2 * X ^ (2 * r)) *
        QO p (X ^ (2 * ((p - 1) / 2 - r)) : ℚ[X])

/-- G uses precisely r < N-d; all retained c_j indices satisfy j < N. -/
theorem fullUnitG_eq_canonicalUnitG (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : fullUnitG p hp = canonicalUnitG p hp := by
  let N := (p - 1) / 2
  let d := p / 6
  have hn : 2 * N + 1 = p := by
    exact prime_half_identity p (by omega)
  have hd : d ≤ N := by dsimp [d, N]; omega
  have hk : p - 1 - 2 * d = 2 * (N - d) := by omega
  unfold fullUnitG canonicalUnitG kernelLow
  rw [QO_sum_local]
  simp only [QO_monomial_local]
  change (metricStar p hp).val * (∑ k ∈ Finset.range (p - 1 - 2 * d), _) =
    (metricStar p hp).val * (∑ r ∈ Finset.range (N - d), _)
  rw [hk, sum_range_even_odd]
  have ho : (∑ r ∈ Finset.range (N - d),
      moment ((p : ℚ) / 3) (rankJacobiNode p 1 ^ 2 * X ^ (2 * r + 1)) *
        QO p (X ^ (p - 1 - (2 * r + 1)) : ℚ[X])) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have he : p - 1 - (2 * r + 1) = 2 * (N - r - 1) + 1 := by omega
    rw [he, QO_X_odd, mul_zero]
  rw [ho, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  rw [show p - 1 - 2 * r = 2 * (N - r) by omega]

noncomputable def weightedMomentIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (P : (integralRationals p)[X]) : integralRationals p :=
  P.sum fun n a => if n % 2 = 0 then
    a * weightedCauchyIntegral p hp (n / 2) else 0

theorem weightedMomentIntegral_value (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (P : (integralRationals p)[X])
    (hP : P.natDegree ≤ p - 3) :
    (weightedMomentIntegral p hp P).val =
      (metricStar p hp).val * moment ((p : ℚ) / 3)
        (P.map (integralRationals p).subtype) := by
  have he : P.map (integralRationals p).subtype =
      ∑ n ∈ P.support, C ((P.coeff n).val) * (X : ℚ[X]) ^ n := by
    conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
    simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X, Subring.subtype_apply]
  have hm : moment ((p : ℚ) / 3) (P.map (integralRationals p).subtype) =
      ∑ n ∈ P.support, (P.coeff n).val * momentWeight ((p : ℚ) / 3) n := by
    rw [he, map_sum]
    simp only [moment_C_mul, moment_X_pow]
  change (integralRationals p).subtype (weightedMomentIntegral p hp P) = _
  rw [weightedMomentIntegral, Polynomial.sum_def, map_sum, hm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnd : n ≤ p - 3 := (le_natDegree_of_mem_supp n hn).trans hP
  have hhalf := prime_half_identity p (by omega : 7 ≤ p)
  by_cases heven : n % 2 = 0
  · have hj : n / 2 < (p - 1) / 2 := by omega
    simp only [momentWeight, if_pos heven, _root_.map_mul]
    simp only [Subring.subtype_apply]
    rw [actual_weighted_cauchy_value p hp (n / 2) hj]
    ring
  · simp only [momentWeight, if_neg heven, _root_.map_zero, mul_zero]

noncomputable def canonicalUnitGIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : integralRationals p :=
  ∑ r ∈ Finset.range ((p - 1) / 2 - p / 6),
    QOi p hp (monomial (2 * ((p - 1) / 2 - r))
      (weightedMomentIntegral p hp (balancedFirstIntegral p hp ^ 2 * X ^ (2 * r))))

/-- Every retained moment is proved to lie in the strict unit window. -/
theorem canonicalUnitGIntegral_value (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (canonicalUnitGIntegral p hp).val = fullUnitG p hp := by
  rw [fullUnitG_eq_canonicalUnitG]
  change (integralRationals p).subtype (canonicalUnitGIntegral p hp) = _
  rw [canonicalUnitGIntegral, map_sum, canonicalUnitG, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  have hn := prime_half_identity p (by omega : 7 ≤ p)
  have hY := balancedFirstIntegral_degree p hp
  have hs : (balancedFirstIntegral p hp ^ 2).natDegree ≤ 2 * (p / 6) := by
    simpa only [pow_two, two_mul] using natDegree_mul_le_of_le hY hY
  have hP : (balancedFirstIntegral p hp ^ 2 * X ^ (2 * r)).natDegree ≤ p - 3 := by
    exact (natDegree_mul_le_of_le hs
      (show (X ^ (2 * r) : (integralRationals p)[X]).natDegree ≤ 2 * r by simp)).trans
        (by omega)
  simp only [Subring.subtype_apply]
  rw [QOi_value, Polynomial.map_monomial, QO_monomial_local]
  simp only [Subring.subtype_apply]
  rw [weightedMomentIntegral_value p hp _ hP]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    balancedFirstIntegral_value p hp]
  ring

end WPFieldAssembly.ActualCauchyMoment
