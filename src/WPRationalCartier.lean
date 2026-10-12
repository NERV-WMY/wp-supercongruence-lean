import WPFiniteCartier
import Mathlib.FieldTheory.RatFunc.Basic

open scoped Polynomial LaurentPolynomial
open LaurentPolynomial

namespace WPRationalCartier

variable (p : ℕ) [Fact p.Prime]

/-- Faithful evaluation of a finite Laurent polynomial at the rational-function variable. -/
noncomputable def evaluate : (ZMod p)[T;T⁻¹] →+* RatFunc (ZMod p) :=
  eval₂ RatFunc.C (Units.mk0 RatFunc.X (RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero))

theorem evaluate_toLaurent (P : (ZMod p)[X]) :
    evaluate p (Polynomial.toLaurent P) = algebraMap (ZMod p)[X] (RatFunc (ZMod p)) P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, map_add, hP, hQ]
  | monomial n a =>
    simp [evaluate, ← Polynomial.C_mul_X_pow_eq_monomial, Units.mk0]

theorem evaluate_monomial (a : ZMod p) (n : ℤ) :
    evaluate p (C a * T n) = RatFunc.C a * RatFunc.X ^ n := by
  simp [evaluate, eval₂_C_mul_T, Units.val_zpow_eq_zpow_val, Units.mk0]

@[simp] theorem evaluate_C (a : ZMod p) : evaluate p (C a) = RatFunc.C a := by
  simpa using evaluate_monomial p a 0

@[simp] theorem evaluate_T (n : ℤ) : evaluate p (T n) = RatFunc.X ^ n := by
  simpa using evaluate_monomial p 1 n

theorem evaluate_injective : Function.Injective (evaluate p) := by
  have hzero (P : (ZMod p)[T;T⁻¹]) (hP : evaluate p P = 0) : P = 0 := by
    obtain ⟨k, F, hF⟩ := LaurentPolynomial.exists_T_pow P
    have hFe := congrArg (evaluate p) hF
    rw [evaluate_toLaurent, map_mul, hP, zero_mul] at hFe
    have hF0 : F = 0 := (RatFunc.algebraMap_injective (ZMod p))
      (by simpa only [map_zero] using hFe)
    rw [hF0, map_zero] at hF
    have hmul := congrArg (fun Q : (ZMod p)[T;T⁻¹] => Q * T (-(k : ℤ))) hF
    simp only [zero_mul, mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one] at hmul
    exact hmul.symm
  intro P Q h
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, h, sub_self]

/-- Finite rational differential selection, using its actual reduced numerator and denominator. -/
noncomputable def rationalCartier (f : RatFunc (ZMod p)) : RatFunc (ZMod p) :=
  evaluate p (WPFiniteCartier.cartier p (Fact.out : p.Prime).pos
    (Polynomial.toLaurent f.num * (Polynomial.toLaurent f.denom) ^ (p - 1))) /
      algebraMap (ZMod p)[X] (RatFunc (ZMod p)) f.denom

/-- Exact denominator-independence, proved from the full finite p-power product identity. -/
theorem rationalCartier_fraction (P Q : (ZMod p)[T;T⁻¹])
    (hQ : evaluate p Q ≠ 0) :
    rationalCartier p (evaluate p P / evaluate p Q) =
      evaluate p (WPFiniteCartier.cartier p (Fact.out : p.Prime).pos
        (P * Q ^ (p - 1))) / evaluate p Q := by
  let f := evaluate p P / evaluate p Q
  let A : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent f.num
  let B : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent f.denom
  have hB : evaluate p B ≠ 0 := by
    rw [show B = Polynomial.toLaurent f.denom by rfl, evaluate_toLaurent]
    exact RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)
  have hrep : evaluate p A / evaluate p B = evaluate p P / evaluate p Q := by
    rw [show A = Polynomial.toLaurent f.num by rfl,
      show B = Polynomial.toLaurent f.denom by rfl, evaluate_toLaurent,
      evaluate_toLaurent, RatFunc.num_div_denom]
  have hcross : A * Q = P * B := by
    apply evaluate_injective p
    simp only [map_mul]
    exact (div_eq_div_iff hB hQ).mp hrep
  have hp : p = p - 1 + 1 := by have := (Fact.out : p.Prime).pos; omega
  have hQpow : Q ^ p = Q ^ (p - 1) * Q := by
    calc
      _ = Q ^ (p - 1 + 1) := congrArg (fun n : ℕ => Q ^ n) hp
      _ = _ := pow_succ Q (p - 1)
  have hBpow : B ^ p = B ^ (p - 1) * B := by
    calc
      _ = B ^ (p - 1 + 1) := congrArg (fun n : ℕ => B ^ n) hp
      _ = _ := pow_succ B (p - 1)
  have hwhole : Q ^ p * (A * B ^ (p - 1)) =
      B ^ p * (P * Q ^ (p - 1)) := by
    rw [hQpow, hBpow]
    calc
      _ = (A * Q) * (B ^ (p - 1) * Q ^ (p - 1)) := by ring
      _ = _ := by rw [hcross]; ring
  have hC := congrArg (WPFiniteCartier.cartier p (Fact.out : p.Prime).pos) hwhole
  rw [WPFiniteCartier.cartier_frobenius_product,
    WPFiniteCartier.cartier_frobenius_product] at hC
  have hCe := congrArg (evaluate p) hC
  simp only [map_mul] at hCe
  change evaluate p (WPFiniteCartier.cartier p (Fact.out : p.Prime).pos
    (A * B ^ (p - 1))) /
      algebraMap (ZMod p)[X] (RatFunc (ZMod p)) f.denom = _
  rw [← evaluate_toLaurent]
  change evaluate p (WPFiniteCartier.cartier p (Fact.out : p.Prime).pos
    (A * B ^ (p - 1))) / evaluate p B = _
  apply (div_eq_div_iff hB hQ).mpr
  linear_combination hCe

/-- The rational selection agrees with the full finite Laurent selection. -/
theorem rationalCartier_evaluate (P : (ZMod p)[T;T⁻¹]) :
    rationalCartier p (evaluate p P) =
      evaluate p (WPFiniteCartier.cartier p (Fact.out : p.Prime).pos P) := by
  have h := rationalCartier_fraction p P 1 (by simp)
  simpa using h

theorem rationalCartier_zero : rationalCartier p 0 = 0 := by
  simpa only [map_zero, WPFiniteCartier.cartier_zero] using rationalCartier_evaluate p 0

private theorem common_denominator_add (P R Q : (ZMod p)[T;T⁻¹])
    (hQ : evaluate p Q ≠ 0) :
    rationalCartier p (evaluate p (P + R) / evaluate p Q) =
      rationalCartier p (evaluate p P / evaluate p Q) +
      rationalCartier p (evaluate p R / evaluate p Q) := by
  rw [rationalCartier_fraction p (P + R) Q hQ,
    rationalCartier_fraction p P Q hQ, rationalCartier_fraction p R Q hQ,
    add_mul, WPFiniteCartier.cartier_add, map_add, add_div]

/-- Additivity across the actual reduced denominators, without a shared-denominator premise. -/
theorem rationalCartier_add (f g : RatFunc (ZMod p)) :
    rationalCartier p (f + g) = rationalCartier p f + rationalCartier p g := by
  let A : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent f.num
  let B : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent f.denom
  let P : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent g.num
  let Q : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent g.denom
  have hB : evaluate p B ≠ 0 := by
    rw [show B = Polynomial.toLaurent f.denom by rfl, evaluate_toLaurent]
    exact RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)
  have hQ : evaluate p Q ≠ 0 := by
    rw [show Q = Polynomial.toLaurent g.denom by rfl, evaluate_toLaurent]
    exact RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero g)
  have hf : f = evaluate p A / evaluate p B := by
    rw [show A = Polynomial.toLaurent f.num by rfl,
      show B = Polynomial.toLaurent f.denom by rfl, evaluate_toLaurent,
      evaluate_toLaurent, RatFunc.num_div_denom]
  have hg : g = evaluate p P / evaluate p Q := by
    rw [show P = Polynomial.toLaurent g.num by rfl,
      show Q = Polynomial.toLaurent g.denom by rfl, evaluate_toLaurent,
      evaluate_toLaurent, RatFunc.num_div_denom]
  have hf' : f = evaluate p (A * Q) / evaluate p (B * Q) := by
    rw [hf, map_mul, map_mul]
    field_simp
  have hg' : g = evaluate p (P * B) / evaluate p (B * Q) := by
    rw [hg, map_mul, map_mul]
    field_simp
  rw [hf', hg', ← add_div, ← map_add]
  exact common_denominator_add p (A * Q) (P * B) (B * Q)
    (by rw [map_mul]; exact mul_ne_zero hB hQ)

/-- The complete p-power product law for a Laurent multiplier and a rational differential. -/
theorem rationalCartier_laurent_frobenius (H : (ZMod p)[T;T⁻¹])
    (f : RatFunc (ZMod p)) :
    rationalCartier p (evaluate p H ^ p * f) =
      evaluate p H * rationalCartier p f := by
  let A : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent f.num
  let B : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent f.denom
  have hB : evaluate p B ≠ 0 := by
    rw [show B = Polynomial.toLaurent f.denom by rfl, evaluate_toLaurent]
    exact RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)
  have hf : f = evaluate p A / evaluate p B := by
    rw [show A = Polynomial.toLaurent f.num by rfl,
      show B = Polynomial.toLaurent f.denom by rfl, evaluate_toLaurent,
      evaluate_toLaurent, RatFunc.num_div_denom]
  rw [hf, ← mul_div_assoc, ← map_pow, ← map_mul,
    rationalCartier_fraction p (H ^ p * A) B hB,
    rationalCartier_fraction p A B hB, mul_assoc,
    WPFiniteCartier.cartier_frobenius_product, map_mul, mul_div_assoc]

theorem rationalCartier_const_mul (a : ZMod p) (f : RatFunc (ZMod p)) :
    rationalCartier p (RatFunc.C a * f) = RatFunc.C a * rationalCartier p f := by
  have h := rationalCartier_laurent_frobenius p (C a) f
  rw [evaluate_C, ← map_pow, ZMod.pow_card] at h
  exact h

theorem rationalCartier_neg (f : RatFunc (ZMod p)) :
    rationalCartier p (-f) = -rationalCartier p f := by
  simpa only [map_neg, map_one, neg_mul, one_mul] using rationalCartier_const_mul p (-1) f

theorem rationalCartier_sub (f g : RatFunc (ZMod p)) :
    rationalCartier p (f - g) = rationalCartier p f - rationalCartier p g := by
  rw [sub_eq_add_neg, rationalCartier_add, rationalCartier_neg, ← sub_eq_add_neg]

private theorem toLaurent_coeff_nat (P : (ZMod p)[X]) (n : ℕ) :
    P.toLaurent.coeff (n : ℤ) = P.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  have h := Finsupp.mapDomain_apply (Nat.castEmbedding (R := ℤ)).injective
    P.toFinsupp.coeff n
  simpa only [Nat.castEmbedding_apply, Polynomial.toFinsupp_apply] using h

private theorem toLaurent_coeff_outside (P : (ZMod p)[X]) (j : ℤ)
    (hj : j < 0 ∨ (P.natDegree : ℤ) < j) : P.toLaurent.coeff j = 0 := by
  by_contra h
  have hm : j ∈ P.toLaurent.coeff.support := Finsupp.mem_support_iff.mpr h
  rw [LaurentPolynomial.support_coeff_toLaurent] at hm
  obtain ⟨n, hn, hnj⟩ := Finset.mem_map.mp hm
  have hnle : n ≤ P.natDegree := Polynomial.le_natDegree_of_mem_supp n hn
  change (n : ℤ) = j at hnj
  rcases hj with hj | hj <;> omega

/-- A polynomial of degree at most p-1 retains exactly its top possible coefficient. -/
theorem cartier_polynomial_low_degree (P : (ZMod p)[X]) (hP : P.natDegree < p) :
    WPFiniteCartier.cartier p (Fact.out : p.Prime).pos P.toLaurent =
      C (P.coeff (p - 1)) := by
  ext k
  rw [WPFiniteCartier.cartier_coeff]
  by_cases hk : k = 0
  · subst k
    have hj : (p : ℤ) * (0 + 1) - 1 = (p - 1 : ℕ) := by
      have := (Fact.out : p.Prime).pos
      omega
    rw [hj, toLaurent_coeff_nat]
    simp
  · rw [LaurentPolynomial.C_apply, if_neg hk]
    apply toLaurent_coeff_outside
    have := (Fact.out : p.Prime).pos
    have hPz : (P.natDegree : ℤ) < (p : ℤ) := by exact_mod_cast hP
    by_cases hkneg : k < 0
    · left; nlinarith
    · have hkpos : 1 ≤ k := by omega
      right; nlinarith

/-- Every literal simple logarithmic pole is fixed by the rational differential selection. -/
theorem rationalCartier_simple_pole (a : ZMod p) :
    rationalCartier p (1 / (RatFunc.X - RatFunc.C a)) =
      1 / (RatFunc.X - RatFunc.C a) := by
  let Q : (ZMod p)[X] := Polynomial.X - Polynomial.C a
  have hQ : evaluate p Q.toLaurent ≠ 0 := by
    rw [evaluate_toLaurent]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero a)
  have hdeg : (Q ^ (p - 1)).natDegree = p - 1 := by
    dsimp only [Q]
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have hmonic : (Q ^ (p - 1)).Monic := (Polynomial.monic_X_sub_C a).pow _
  have hcoeff : (Q ^ (p - 1)).coeff (p - 1) = 1 := by
    simpa only [hdeg] using show (Q ^ (p - 1)).coeff (Q ^ (p - 1)).natDegree = 1 by
      rw [Polynomial.coeff_natDegree, hmonic.leadingCoeff]
  have hC := cartier_polynomial_low_degree p (Q ^ (p - 1))
    (by rw [hdeg]; exact Nat.sub_lt (Fact.out : p.Prime).pos (by omega))
  rw [hcoeff] at hC
  have h := rationalCartier_fraction p 1 Q.toLaurent hQ
  simp only [map_one, one_mul, ← map_pow, hC] at h
  simpa [Q, evaluate_toLaurent] using h

end WPRationalCartier
