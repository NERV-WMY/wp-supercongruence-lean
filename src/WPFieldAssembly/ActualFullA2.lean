import WPFiniteJSource

open scoped BigOperators Polynomial
open Polynomial WPFiniteKSource WPFiniteAffineLog WPFiniteJSource

namespace WPFieldAssembly.ActualFullA2

set_option maxHeartbeats 1400000

variable {K : Type*} [Field K]

/-- The entire harmonic weight-two polynomial, including every full-cutoff coefficient. -/
noncomputable def fullHarmonicPrimitive (p : ℕ) : K[X] :=
  ∑ j ∈ Finset.Ico 1 p, C ((H (j-1) : K)/(j : K))*X^j

noncomputable def fullDilogPrimitive (p : ℕ) : K[X] :=
  -(RP p).comp (1-X)

private theorem H_succ (n : ℕ) : (H (n+1) : K)=H n+((n+1 : ℕ) : K)⁻¹ := by
  unfold H
  rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n+1)]

/-- The terminal harmonic is kept in the full telescoping identity. -/
private theorem full_harmonic_cleared (n : ℕ) :
    (1-X : K[X])*(∑ k ∈ Finset.range n, C (H k)*X^k)=
      (∑ j ∈ Finset.Ico 1 (n+1), C ((j : K)⁻¹)*X^j)-C (H n)*X^n := by
  induction n with
  | zero => simp [H]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih,
      Finset.sum_Ico_succ_top (a := 1) (b := n+1) (by omega), H_succ]
    simp only [map_add, pow_succ]
    ring

theorem fullHarmonicPrimitive_derivative (p : ℕ) [Fact p.Prime] [CharP K p] :
    (fullHarmonicPrimitive p : K[X]).derivative=
      ∑ k ∈ Finset.range (p-1), C (H k)*X^k := by
  unfold fullHarmonicPrimitive
  rw [derivative_sum, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hk1 : 1+k<p := by omega
  have hu : ((1+k : ℕ) : K) ≠ 0 := WPFiniteField.denominator_ne_zero p (1+k)
    (Finset.mem_Ico.mpr (by omega))
  rw [derivative_C_mul_X_pow, div_mul_cancel₀ _ hu]
  simp only [Nat.add_sub_cancel_left]

private theorem H_full_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (H (p-1) : K)=0 := by
  have he := congrArg (fun P : K[X] => P.eval 0) (LP_reflection (K := K) p hp)
  have hz : (LP p : K[X]).eval 0=0 := by
    unfold LP
    rw [eval_finsetSum]
    apply Finset.sum_eq_zero
    intro j hj
    have hjpos := (Finset.mem_Ico.mp hj).1
    simp only [eval_mul, eval_C, eval_pow, eval_X,
      zero_pow (by omega : j ≠ 0), mul_zero]
  simp only [eval_comp, eval_sub, eval_one, eval_X, sub_zero, hz] at he
  have hv : (LP p : K[X]).eval 1=H (p-1) := by
    simp only [LP, H, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
      one_pow, mul_one, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
  rw [hv] at he
  exact he

theorem fullHarmonicPrimitive_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (1-X : K[X])*(fullHarmonicPrimitive p).derivative=LP p := by
  rw [fullHarmonicPrimitive_derivative, full_harmonic_cleared,
    Nat.sub_add_cancel (Fact.out : p.Prime).one_le,
    H_full_zero p hp, map_zero, zero_mul, sub_zero]
  rfl

theorem fullDilogPrimitive_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (1-X : K[X])*(fullDilogPrimitive p).derivative=LP p := by
  have h := RP_comp_derivative (K := K) p (1-X)
  simp only [derivative_sub, derivative_one, derivative_X, zero_sub,
    LP_reflection p hp, mul_neg] at h
  unfold fullDilogPrimitive
  rw [derivative_neg]
  linear_combination -h

theorem fullHarmonicPrimitive_natDegree_le (p : ℕ) :
    (fullHarmonicPrimitive p : K[X]).natDegree ≤ p-1 := by
  unfold fullHarmonicPrimitive
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  calc
    _ ≤ (X^j : K[X]).natDegree := natDegree_C_mul_le _ _
    _ ≤ j := by simp
    _ ≤ p-1 := by omega

theorem fullDilogPrimitive_natDegree_le (p : ℕ) :
    (fullDilogPrimitive p : K[X]).natDegree ≤ p-1 := by
  have hu : (1-X : K[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  rw [fullDilogPrimitive, natDegree_neg]
  calc
    _ ≤ (RP p : K[X]).natDegree*(1-X : K[X]).natDegree := natDegree_comp_le
    _ ≤ (p-1)*1 := Nat.mul_le_mul (RP_natDegree_le p) hu
    _ = p-1 := by simp

private theorem zero_of_derivative_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (Q : K[X]) (hdeg : Q.natDegree<p) (hder : Q.derivative=0) (hz : Q.eval 0=0) :
    Q=0 := by
  ext n
  by_cases hn : n=0
  · subst n
    simpa only [coeff_zero_eq_eval_zero, eval_zero] using hz
  by_cases hnp : p ≤ n
  · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_le hnp)
  have he : Q.coeff n*(n : K)=0 := by
    have hc := congrArg (fun P : K[X] => P.coeff (n-1)) hder
    simpa only [coeff_derivative, ←Nat.cast_add_one,
      Nat.sub_add_cancel (by omega : 1 ≤ n), coeff_zero] using hc
  exact (mul_eq_zero.mp he).resolve_right (WPFiniteField.denominator_ne_zero p n
    (Finset.mem_Ico.mpr (by omega)))

/-- Full A2 identification; the degree<p window excludes an unfixed X^p term. -/
theorem actual_full_dilog_polynomial (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (fullHarmonicPrimitive p : K[X])=fullDilogPrimitive p := by
  have hdeg : ((fullHarmonicPrimitive p : K[X])-fullDilogPrimitive p).natDegree<p := by
    have h := (natDegree_sub_le _ _).trans (max_le
      (fullHarmonicPrimitive_natDegree_le (K := K) p)
      (fullDilogPrimitive_natDegree_le (K := K) p))
    have hp0 := (Fact.out : p.Prime).pos
    omega
  have hf : (1-X : K[X]) ≠ 0 := by
    intro hz
    have hc := congrArg (fun P : K[X] => P.coeff 1) hz
    norm_num [Polynomial.coeff_one] at hc
  have hder : ((fullHarmonicPrimitive p : K[X])-fullDilogPrimitive p).derivative=0 := by
    have h : (1-X : K[X])*
        ((fullHarmonicPrimitive p : K[X])-fullDilogPrimitive p).derivative=0 := by
      rw [derivative_sub, mul_sub, fullHarmonicPrimitive_cleared_derivative p hp,
        fullDilogPrimitive_cleared_derivative p hp, sub_self]
    exact (mul_eq_zero.mp h).resolve_left hf
  have hz : ((fullHarmonicPrimitive p : K[X])-fullDilogPrimitive p).eval 0=0 := by
    have hH : (fullHarmonicPrimitive p : K[X]).eval 0=0 := by
      unfold fullHarmonicPrimitive
      rw [eval_finsetSum]
      apply Finset.sum_eq_zero
      intro j hj
      have hjpos := (Finset.mem_Ico.mp hj).1
      simp only [eval_mul, eval_C, eval_pow, eval_X,
        zero_pow (by omega : j ≠ 0), mul_zero]
    have hR : WPFiniteField.R p (1 : K)=0 := by
      have h := congrArg (ZMod.castHom (dvd_refl p) K)
        (WPFiniteInversion.R_one_eq_zero p (by omega))
      simpa only [←WPFiniteField.R_castHom, map_one, map_zero] using h
    simp only [eval_sub, hH, fullDilogPrimitive, eval_neg, eval_comp,
      eval_sub, eval_one, eval_X, sub_zero, RP_eval, hR, neg_zero, sub_zero]
  exact sub_eq_zero.mp (zero_of_derivative_degree p _ hdeg hder hz)

theorem actual_full_dilog_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) :
    (fullHarmonicPrimitive p : K[X]).eval z=-WPFiniteField.R p (1-z) := by
  rw [actual_full_dilog_polynomial p hp]
  simp only [fullDilogPrimitive, eval_neg, eval_comp, eval_sub, eval_one, eval_X, RP_eval]

end WPFieldAssembly.ActualFullA2
