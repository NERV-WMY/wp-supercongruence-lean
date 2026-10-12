import WPFieldAssembly.ConicDivision
import Mathlib.Algebra.Polynomial.Expand

open scoped Polynomial
open Polynomial

namespace WPFieldAssembly.ConicKernel

set_option maxHeartbeats 1000000

theorem coeff_comp_neg {K : Type*} [CommRing K] (Q : K[X]) (n : ℕ) :
    (Q.comp (-X)).coeff n = Q.coeff n * (-1 : K) ^ n := by
  refine Polynomial.induction_on Q
    (fun a => ?_) (fun f g hf hg => ?_) (fun d a _ => ?_)
  · simp only [C_comp, coeff_C]
    by_cases hn : n = 0 <;> simp [hn]
  · rw [add_comp, coeff_add, coeff_add, hf, hg]
    ring
  · have hpow : (-X : K[X]) ^ (d + 1) = C ((-1 : K) ^ (d + 1)) * X ^ (d + 1) := by
      calc
        _ = (C (-1 : K) * X) ^ (d + 1) := by simp
        _ = _ := by rw [mul_pow, ← C_pow]
    rw [mul_comp, C_comp, pow_comp, X_comp, hpow, ← mul_assoc, ← C_mul,
      coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    by_cases hn : d + 1 = n
    · subst n
      simp
    · simp only [if_neg (Ne.symm hn), zero_mul]

/-- The bounded odd Frobenius kernel retains its 5p coefficient as a hypothesis. -/
theorem bounded_conic_kernel_normalized (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (b : (ZMod p)[X]) (hD : b.derivative = 0) (hdeg : b.natDegree ≤ 5 * p)
    (hodd : b.comp (-X) = -b) (h1 : b.eval 1 = 0) (hh : b.eval (1 / 2) = 0)
    (h5p : b.coeff (5 * p) = -20) :
    b = C (5 : ZMod p) * X ^ p * ((1 - X ^ 2) * (4 * X ^ 2 - 1)) ^ p := by
  let U : (ZMod p)[X] := contract p b
  let A : (ZMod p)[X] := (1 - X ^ 2) * (4 * X ^ 2 - 1)
  have hpP : p.Prime := Fact.out
  have hp0 : 0 < p := hpP.pos
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have hexpand : expand (ZMod p) p U = b := Polynomial.expand_contract p hD hpP.ne_zero
  have hUdeg : U.natDegree ≤ 5 := by
    have hm : U.natDegree * p ≤ 5 * p := by
      rw [← natDegree_expand p U, hexpand]
      exact hdeg
    nlinarith
  have hEvenCoeff (n : ℕ) (hsign : (-1 : ZMod p) ^ (n * p) = 1) : U.coeff n = 0 := by
    have he := congrArg (fun P : (ZMod p)[X] => P.coeff (n * p)) hodd
    rw [coeff_comp_neg, coeff_neg, hsign, mul_one] at he
    have hz : (2 : ZMod p) * b.coeff (n * p) = 0 := by linear_combination he
    change (contract p b).coeff n = 0
    rw [coeff_contract hpP.ne_zero]
    exact (mul_eq_zero.mp hz).resolve_left h2
  have hU0 : U.coeff 0 = 0 := hEvenCoeff 0 (by simp)
  have hU2 : U.coeff 2 = 0 := hEvenCoeff 2 (by rw [pow_mul]; norm_num)
  have hU4 : U.coeff 4 = 0 := hEvenCoeff 4 (by rw [pow_mul]; norm_num)
  let a1 : ZMod p := U.coeff 1
  let a3 : ZMod p := U.coeff 3
  let a5 : ZMod p := U.coeff 5
  have hshape : U = C a1 * X + C a3 * X ^ 3 + C a5 * X ^ 5 := by
    ext n
    by_cases hn : n ≤ 5
    · interval_cases n <;> simp [a1, a3, a5, hU0, hU2, hU4]
    · have hUn : U.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (hUdeg.trans_lt (by omega))
      have hn1 : n ≠ 1 := by omega
      have hn3 : n ≠ 3 := by omega
      have hn5 : n ≠ 5 := by omega
      simp [hUn, Ne.symm hn1, hn3, hn5, coeff_C_mul, coeff_X_pow, coeff_X]
  have hEval (z : ZMod p) : U.eval z = b.eval z := by
    have he := congrArg (fun P : (ZMod p)[X] => P.eval z) hexpand
    simpa only [expand_eq_comp_X_pow, eval_comp, eval_pow, eval_X, ZMod.pow_card] using he
  have he1 : a1 + a3 + a5 = 0 := by
    have he := (hEval 1).trans h1
    rw [hshape] at he
    simpa only [eval_add, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one] using he
  have heh : 16 * a1 + 4 * a3 + a5 = 0 := by
    have he := (hEval (1 / 2)).trans hh
    rw [hshape] at he
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at he
    field_simp [h2] at he
    linear_combination he
  have ha3 : a3 = -5 * a1 := by
    apply mul_left_cancel₀ h3
    linear_combination heh - he1
  have ha5 : a5 = 4 * a1 := by linear_combination he1 - ha3
  have ha5top : a5 = -20 := by
    change (contract p b).coeff 5 = -20
    rw [coeff_contract hpP.ne_zero, h5p]
  have ha1 : a1 = -5 := by
    apply mul_left_cancel₀ h4
    linear_combination -ha5 + ha5top
  have hU : U = C (5 : ZMod p) * X * A := by
    rw [hshape, ha3, ha5, ha1]
    simp only [A, map_mul, map_ofNat, map_neg]
    ring
  have hFrob : frobenius (ZMod p) p = RingHom.id (ZMod p) := by
    ext z
    change z ^ p = z
    exact ZMod.pow_card z
  have hAexpand : expand (ZMod p) p A = A ^ p := by
    simpa [hFrob] using Polynomial.map_frobenius_expand p A
  calc
    b = expand (ZMod p) p U := hexpand.symm
    _ = C (5 : ZMod p) * X ^ p * A ^ p := by
      rw [hU]
      simp only [map_mul, expand_C, expand_X, hAexpand]
    _ = _ := rfl

theorem coeff_comp_bound_top {K : Type*} [CommRing K] [IsDomain K]
    (P Q : K[X]) (d e : ℕ) (hP : P.natDegree ≤ d) (hQ : Q.natDegree = e) (he : 0 < e) :
    (P.comp Q).coeff (d * e) = P.coeff d * Q.coeff e ^ d := by
  by_cases hd : P.natDegree = d
  · simpa [hd, hQ, Polynomial.leadingCoeff] using
      (Polynomial.coeff_comp_degree_mul_degree (p := P) (q := Q) (by omega : Q.natDegree ≠ 0))
  · have hdlt : P.natDegree < d := lt_of_le_of_ne hP hd
    have hc : (P.comp Q).natDegree < d * e := by
      rw [natDegree_comp, hQ]
      exact Nat.mul_lt_mul_of_pos_right hdlt he
    rw [coeff_eq_zero_of_natDegree_lt hc, coeff_eq_zero_of_natDegree_lt hdlt, zero_mul]

theorem comp_injective_nonconstant {K : Type*} [CommRing K] [IsDomain K]
    (B : K[X]) (hB : B.natDegree ≠ 0) : Function.Injective (fun P : K[X] => P.comp B) := by
  intro P Q hPQ
  change P.comp B = Q.comp B at hPQ
  apply sub_eq_zero.mp
  have hz : (P - Q).comp B = 0 := by rw [sub_comp, hPQ, sub_self]
  rcases Polynomial.comp_eq_zero_iff.mp hz with h | h
  · exact h
  · exact False.elim (hB (by rw [h.2]; simp))

end WPFieldAssembly.ConicKernel
