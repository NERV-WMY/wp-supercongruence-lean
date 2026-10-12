import WPFiniteDistribution
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Ring.GeomSum

open scoped BigOperators
open Polynomial

namespace WPFiniteInversion

theorem ell_one_eq_zero (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) : ell p 1 = 0 := by
  have hi := ell_inversion p 1 (one_ne_zero : (1 : ZMod p) ≠ 0)
  have htwo : (2 : ZMod p) ≠ 0 :=
    denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have he : (2 : ZMod p) * ell p 1 = 0 := by
    simp only [inv_one, one_pow, neg_mul, one_mul] at hi
    linear_combination hi
  exact (mul_eq_zero.mp he).resolve_left htwo

theorem R_one_eq_zero (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : R p 1 = 0 := by
  have hprime : p.Prime := Fact.out
  have hodd : Odd p := hprime.odd_of_ne_two (by omega)
  have hi := R_quadratic_distribution p hodd (1 : ZMod p)
  have hthree : (3 : ZMod p) ≠ 0 :=
    denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have he : (3 : ZMod p) * R p 1 = 0 := by
    simp only [one_pow, sub_self, mul_zero, zero_mul, add_zero] at hi
    linear_combination -hi
  exact (mul_eq_zero.mp he).resolve_left hthree

/-- A finite polynomial with exactly the logarithm's full index interval. -/
noncomputable def ellPolynomial (p : ℕ) [Fact p.Prime] : Polynomial (ZMod p) :=
  ∑ j ∈ Finset.Ico 1 p, C ((j : ZMod p)⁻¹) * X ^ j

/-- A finite polynomial with exactly the dilogarithm's full index interval. -/
noncomputable def RPolynomial (p : ℕ) [Fact p.Prime] : Polynomial (ZMod p) :=
  ∑ j ∈ Finset.Ico 1 p, C (((j : ZMod p) ^ 2)⁻¹) * X ^ j

private theorem eval_ellPolynomial (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    (ellPolynomial p).eval x = ell p x := by
  simp only [ellPolynomial, ell, eval_finsetSum, eval_mul, eval_C, eval_pow,
    eval_X, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem eval_RPolynomial (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    (RPolynomial p).eval x = R p x := by
  simp only [RPolynomial, R, eval_finsetSum, eval_mul, eval_C, eval_pow,
    eval_X, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem ell_zero (p : ℕ) [Fact p.Prime] : ell p 0 = 0 := by
  unfold ell
  apply Finset.sum_eq_zero
  intro j hj
  have hjpos : 0 < j := by have := (Finset.mem_Ico.mp hj).1; omega
  simp [zero_pow hjpos.ne']

private theorem R_zero (p : ℕ) [Fact p.Prime] : R p 0 = 0 := by
  unfold R
  apply Finset.sum_eq_zero
  intro j hj
  have hjpos : 0 < j := by have := (Finset.mem_Ico.mp hj).1; omega
  simp [zero_pow hjpos.ne']

private theorem finite_polynomial_degree (p : ℕ) [Fact p.Prime]
    (a : ℕ → ZMod p) :
    (∑ j ∈ Finset.Ico 1 p, C (a j) * X ^ j).natDegree ≤ p - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hj' := (Finset.mem_Ico.mp hj).2
  calc
    (C (a j) * X ^ j).natDegree ≤ (X ^ j : Polynomial (ZMod p)).natDegree :=
      natDegree_C_mul_le _ _
    _ ≤ j := by simp
    _ ≤ p - 1 := by omega

private theorem one_sub_X_degree (p : ℕ) [Fact p.Prime] :
    (1 - X : Polynomial (ZMod p)).natDegree ≤ 1 := by
  exact (natDegree_sub_le _ _).trans (by simp)

/-- In this degree range the only possible zero-derivative slots are 0 and p. -/
private theorem zero_of_derivative_and_ends (p : ℕ) [Fact p.Prime]
    (hp : 0 < p) (Q : Polynomial (ZMod p))
    (hqdeg : Q.natDegree < 2 * p) (hqder : Q.derivative = 0)
    (hq0 : Q.eval 0 = 0) (hq1 : Q.eval 1 = 0) : Q = 0 := by
  have hshape : Q = C (Q.coeff 0) + C (Q.coeff p) * X ^ p := by
    ext n
    by_cases hn0 : n = 0
    · subst n
      simp [coeff_C, hp.ne]
    by_cases hnp : n = p
    · subst n
      simp [coeff_C, hp.ne']
    have hcoeff : Q.coeff n = 0 := by
      by_cases hnlarge : 2 * p ≤ n
      · exact coeff_eq_zero_of_natDegree_lt (hqdeg.trans_le hnlarge)
      have hnsmall : n < 2 * p := by omega
      have hnotdvd : ¬p ∣ n := by
        rintro ⟨k, hk⟩
        have hklt : k < 2 := by
          apply (Nat.mul_lt_mul_left hp).mp
          rw [← hk]
          omega
        have hk01 : k = 0 ∨ k = 1 := by omega
        rcases hk01 with rfl | rfl <;> simp_all
      have hcast : (n : ZMod p) ≠ 0 := by
        intro hz
        exact hnotdvd ((ZMod.natCast_eq_zero_iff n p).mp hz)
      have hnpos : 1 ≤ n := by omega
      have he : Q.coeff n * (n : ZMod p) = 0 := by
        have hc := congrArg (fun T : Polynomial (ZMod p) => T.coeff (n - 1)) hqder
        simpa only [coeff_derivative, ← Nat.cast_add_one,
          Nat.sub_add_cancel hnpos, coeff_zero] using hc
      exact (mul_eq_zero.mp he).resolve_right hcast
    simp [coeff_C, hn0, hnp, hcoeff]
  have ha : Q.coeff 0 = 0 := by rwa [coeff_zero_eq_eval_zero]
  have hb : Q.coeff p = 0 := by
    have he := congrArg (fun T : Polynomial (ZMod p) => T.eval 1) hshape
    simpa [hq1, ha] using he.symm
  rw [hshape, ha, hb]
  simp

private theorem derivative_ellPolynomial (p : ℕ) [Fact p.Prime] :
    (ellPolynomial p).derivative = ∑ j ∈ Finset.range (p - 1),
      (X : Polynomial (ZMod p)) ^ j := by
  unfold ellPolynomial
  rw [derivative_sum]
  have hterms : (∑ j ∈ Finset.Ico 1 p,
      (C ((j : ZMod p)⁻¹) * X ^ j).derivative) =
      ∑ j ∈ Finset.Ico 1 p, (X : Polynomial (ZMod p)) ^ (j - 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [derivative_C_mul_X_pow, inv_mul_cancel₀ (denominator_ne_zero p j hj),
      C_1, one_mul]
  rw [hterms, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  omega

private theorem X_mul_derivative_RPolynomial (p : ℕ) [Fact p.Prime] :
    X * (RPolynomial p).derivative = ellPolynomial p := by
  unfold RPolynomial ellPolynomial
  rw [derivative_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjpos : 1 ≤ j := (Finset.mem_Ico.mp hj).1
  have hden := denominator_ne_zero p j hj
  have hcoef : (((j : ZMod p) ^ 2)⁻¹) * j = (j : ZMod p)⁻¹ := by
    field_simp
  rw [derivative_C_mul_X_pow, hcoef]
  calc
    X * (C ((j : ZMod p)⁻¹) * X ^ (j - 1)) =
        C ((j : ZMod p)⁻¹) * (X ^ (j - 1) * X) := by ring
    _ = C ((j : ZMod p)⁻¹) * X ^ j := by
      rw [← pow_succ, Nat.sub_add_cancel hjpos]

private theorem derivative_ell_closed (p : ℕ) [Fact p.Prime] (hp : 0 < p) :
    (ellPolynomial p).derivative =
      (1 - X : Polynomial (ZMod p)) ^ (p - 1) - X ^ (p - 1) := by
  have hnonzero : (1 - X : Polynomial (ZMod p)) ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa using (X_ne_C (1 : ZMod p)).symm
  have hgeom : (∑ j ∈ Finset.range p, (X : Polynomial (ZMod p)) ^ j) =
      (1 - X) ^ (p - 1) := by
    apply mul_right_cancel₀ hnonzero
    rw [geom_sum_mul_neg, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    simpa using (sub_pow_char (1 : Polynomial (ZMod p)) X (p := p)).symm
  rw [derivative_ellPolynomial]
  have hsum : (∑ j ∈ Finset.range (p - 1), (X : Polynomial (ZMod p)) ^ j) +
      X ^ (p - 1) = (1 - X) ^ (p - 1) := by
    rw [← Finset.sum_range_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    exact hgeom
  linear_combination hsum

private theorem ellPolynomial_reflection (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (ellPolynomial p).comp (1 - X) = ellPolynomial p := by
  let L := ellPolynomial p
  have hder : (L - L.comp (1 - X)).derivative = 0 := by
    rw [derivative_sub, derivative_comp_one_sub_X]
    have hl := derivative_ell_closed p (by omega)
    dsimp [L]
    rw [hl, sub_comp, pow_comp, pow_comp]
    simp only [sub_comp, one_comp, X_comp]
    rw [show (1 - (1 - X) : Polynomial (ZMod p)) = X by ring]
    ring
  have hLdeg : L.natDegree ≤ p - 1 := finite_polynomial_degree p _
  have hcdeg : (L.comp (1 - X)).natDegree ≤ p - 1 := by
    calc
      _ ≤ L.natDegree * (1 - X : Polynomial (ZMod p)).natDegree := natDegree_comp_le
      _ ≤ (p - 1) * 1 := Nat.mul_le_mul hLdeg (one_sub_X_degree p)
      _ = p - 1 := by simp
  have hdeg : (L - L.comp (1 - X)).natDegree < 2 * p := by
    apply lt_of_le_of_lt (natDegree_sub_le _ _)
    have hm : max L.natDegree (L.comp (1 - X)).natDegree ≤ p - 1 :=
      max_le hLdeg hcdeg
    omega
  have h0 : (L - L.comp (1 - X)).eval 0 = 0 := by
    simp [L, eval_ellPolynomial, ell_zero, ell_one_eq_zero p hp]
  have h1 : (L - L.comp (1 - X)).eval 1 = 0 := by
    simp [L, eval_ellPolynomial, ell_zero, ell_one_eq_zero p hp]
  have hz := zero_of_derivative_and_ends p (by omega) _ hdeg hder h0 h1
  exact (sub_eq_zero.mp hz).symm

/-- The proved finite logarithm polynomial reflection, for arbitrary field evaluation. -/
theorem ellPolynomial_reflection_eq (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (ellPolynomial p).comp (1 - X) = ellPolynomial p := ellPolynomial_reflection p hp

/-- The complete finite weight-two reflection defect, including the p-th-power slots. -/
noncomputable def reflectionDefect (p : ℕ) [Fact p.Prime] : Polynomial (ZMod p) :=
  X ^ p * RPolynomial p + (1 - X) ^ p * (RPolynomial p).comp (1 - X) +
    C ((2 : ZMod p)⁻¹) * (ellPolynomial p) ^ 2

private theorem reflectionDefect_degree (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (reflectionDefect p).natDegree < 2 * p := by
  have hR : (RPolynomial p).natDegree ≤ p - 1 := finite_polynomial_degree p _
  have hL : (ellPolynomial p).natDegree ≤ p - 1 := finite_polynomial_degree p _
  have hY := one_sub_X_degree p
  have hYpow : ((1 - X : Polynomial (ZMod p)) ^ p).natDegree ≤ p := by
    calc
      _ ≤ p * (1 - X : Polynomial (ZMod p)).natDegree := natDegree_pow_le
      _ ≤ p * 1 := Nat.mul_le_mul_left p hY
      _ = p := by simp
  have hRcomp : ((RPolynomial p).comp (1 - X)).natDegree ≤ p - 1 := by
    calc
      _ ≤ (RPolynomial p).natDegree * (1 - X : Polynomial (ZMod p)).natDegree :=
        natDegree_comp_le
      _ ≤ (p - 1) * 1 := Nat.mul_le_mul hR hY
      _ = p - 1 := by simp
  have hleft : (X ^ p * RPolynomial p).natDegree ≤ 2 * p - 1 := by
    calc
      _ ≤ (X ^ p : Polynomial (ZMod p)).natDegree + (RPolynomial p).natDegree :=
        natDegree_mul_le
      _ ≤ p + (p - 1) := Nat.add_le_add (by simp) hR
      _ ≤ 2 * p - 1 := by omega
  have hright : ((1 - X) ^ p * (RPolynomial p).comp (1 - X)).natDegree ≤
      2 * p - 1 := by
    calc
      _ ≤ ((1 - X : Polynomial (ZMod p)) ^ p).natDegree +
          ((RPolynomial p).comp (1 - X)).natDegree := natDegree_mul_le
      _ ≤ p + (p - 1) := Nat.add_le_add hYpow hRcomp
      _ ≤ 2 * p - 1 := by omega
  have hhalf : (C ((2 : ZMod p)⁻¹) * (ellPolynomial p) ^ 2).natDegree ≤
      2 * p - 1 := by
    calc
      _ ≤ ((ellPolynomial p) ^ 2).natDegree := natDegree_C_mul_le _ _
      _ ≤ 2 * (ellPolynomial p).natDegree := natDegree_pow_le
      _ ≤ 2 * (p - 1) := Nat.mul_le_mul_left 2 hL
      _ ≤ 2 * p - 1 := by omega
  have hsum : (X ^ p * RPolynomial p +
      (1 - X) ^ p * (RPolynomial p).comp (1 - X)).natDegree ≤ 2 * p - 1 :=
    (natDegree_add_le _ _).trans (max_le hleft hright)
  have hall : (reflectionDefect p).natDegree ≤ 2 * p - 1 :=
    (natDegree_add_le _ _).trans (max_le hsum hhalf)
  omega

private theorem reflectionDefect_derivative (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (reflectionDefect p).derivative = 0 := by
  have hxpder : (X ^ p : Polynomial (ZMod p)).derivative = 0 := by
    simp [derivative_X_pow]
  have hypder : ((1 - X : Polynomial (ZMod p)) ^ p).derivative = 0 := by
    simp [derivative_pow]
  have htwo : (2 : ZMod p) ≠ 0 :=
    denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hhalf : C ((2 : ZMod p)⁻¹) * C (2 : ZMod p) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ htwo, C_1]
  have hxp : (X : Polynomial (ZMod p)) ^ p = X ^ (p - 1) * X := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hyp : (1 - X : Polynomial (ZMod p)) ^ p = (1 - X) ^ (p - 1) * (1 - X) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hRref : (1 - X) * (RPolynomial p).derivative.comp (1 - X) =
      ellPolynomial p := by
    have he := congrArg (fun T : Polynomial (ZMod p) => T.comp (1 - X))
      (X_mul_derivative_RPolynomial p)
    simpa only [mul_comp, X_comp, ellPolynomial_reflection p (by omega)] using he
  unfold reflectionDefect
  rw [derivative_add, derivative_add, derivative_mul, hxpder, zero_mul, zero_add,
    derivative_mul, hypder, zero_mul, zero_add, derivative_comp_one_sub_X,
    derivative_mul, derivative_C, zero_mul, zero_add, derivative_sq]
  calc
    _ = X ^ (p - 1) * (X * (RPolynomial p).derivative) -
        (1 - X) ^ (p - 1) *
          ((1 - X) * (RPolynomial p).derivative.comp (1 - X)) +
        (C ((2 : ZMod p)⁻¹) * C (2 : ZMod p)) *
          ellPolynomial p * (ellPolynomial p).derivative := by
      rw [hxp, hyp]
      ring
    _ = 0 := by
      rw [X_mul_derivative_RPolynomial, hRref, hhalf,
        derivative_ell_closed p (by omega)]
      ring

private theorem reflectionDefect_zero (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    reflectionDefect p = 0 := by
  apply zero_of_derivative_and_ends p (by omega) _
    (reflectionDefect_degree p hp) (reflectionDefect_derivative p hp)
  · simp [reflectionDefect, eval_RPolynomial, eval_ellPolynomial, R_zero, ell_zero,
      R_one_eq_zero p hp]
  · simp [reflectionDefect, eval_RPolynomial, eval_ellPolynomial, R_zero,
      R_one_eq_zero p hp, ell_one_eq_zero p (by omega)]

/-- The proved full finite polynomial identity, available for extension-field evaluation. -/
theorem reflectionDefect_eq_zero (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    reflectionDefect p = 0 := reflectionDefect_zero p hp

theorem R_weight_two_reflection (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (x : ZMod p) :
    x ^ p * R p x + (1 - x) ^ p * R p (1 - x) = -(ell p x) ^ 2 / 2 := by
  have he := congrArg (fun T : Polynomial (ZMod p) => T.eval x) (reflectionDefect_zero p hp)
  simp only [reflectionDefect, eval_add, eval_mul, eval_pow, eval_X, eval_C,
    eval_comp, eval_sub, eval_one, eval_RPolynomial, eval_ellPolynomial, eval_zero] at he
  rw [div_eq_mul_inv]
  linear_combination he

section PrimeThreeBoundary

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem reflection_p3_zero_counterexample :
    (0 : ZMod 3) ^ 3 * R 3 0 + (1 - 0) ^ 3 * R 3 (1 - 0) ≠
      -(ell 3 0) ^ 2 / 2 := by
  norm_num [R, ell, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]
  have hfour : (4 : ZMod 3) = 1 :=
    (ZMod.natCast_eq_natCast_iff 4 1 3).mpr (by decide)
  rw [hfour, inv_one]
  change (2 : ZMod 3) ≠ 0
  exact (ZMod.natCast_eq_zero_iff 2 3).not.mpr (by decide)

end PrimeThreeBoundary

end WPFiniteInversion
