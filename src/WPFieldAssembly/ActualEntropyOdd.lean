import WPFieldAssembly.ActualEntropyPolynomial
import WPFiniteKSource

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPActualRankTwoHatLift

namespace WPFieldAssembly.ActualEntropyOdd

set_option maxHeartbeats 1200000

/-- Every original integer divided binomial coefficient, before reduction. -/
noncomputable def fullEntropyIntegral (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  ∑ j ∈ Finset.Ico 1 p,
    C ((((Nat.choose p j : ℤ)/(p : ℤ) : ℤ) : integralRationals p)) * X^j

noncomputable def oddEntropyIntegral (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  C (smallIntegralInverse p 2) *
    (fullEntropyIntegral p-(fullEntropyIntegral p).comp (-X))

/-- The whole integral odd source changes sign under the original involution. -/
theorem oddEntropyIntegral_comp_neg (p : ℕ) [Fact p.Prime] :
    (oddEntropyIntegral p).comp (-X) = -(oddEntropyIntegral p) := by
  have hx : (- (X : (integralRationals p)[X])).comp (-X) = X := by
    simp only [neg_comp, X_comp, neg_neg]
  simp only [oddEntropyIntegral, mul_comp, C_comp, sub_comp, comp_assoc, hx, comp_X]
  ring

/-- Exact integral polynomial binomial source, including both original extreme terms. -/
theorem fullEntropyIntegral_source (p : ℕ) [Fact p.Prime] :
    C (p : integralRationals p)*fullEntropyIntegral p =
      (1+X)^p-1-X^p := by
  have hbin := add_pow (X : (integralRationals p)[X]) 1 p
  rw [Finset.sum_range_succ,
    ←Finset.sum_range_add_sum_Ico _ (Fact.out : p.Prime).one_le] at hbin
  simp only [Finset.sum_range_one, pow_zero, one_pow, Nat.choose_zero_right,
    Nat.choose_self, Nat.cast_one, mul_one] at hbin
  have hsum : C (p : integralRationals p)*fullEntropyIntegral p =
      ∑ j ∈ Finset.Ico 1 p, (X : (integralRationals p)[X])^j*(Nat.choose p j) := by
    unfold fullEntropyIntegral
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hd : (p : ℤ) ∣ (Nat.choose p j : ℤ) := by
      exact_mod_cast (Fact.out : p.Prime).dvd_choose_self
        (by have hh := Finset.mem_Ico.mp hj; omega) (Finset.mem_Ico.mp hj).2
    have hi := Int.mul_ediv_cancel' hd
    have hiR := congrArg (fun n : ℤ => (n : integralRationals p)) hi
    push_cast at hiR
    rw [←mul_assoc, ←C_mul, hiR, map_natCast]
    ring
  rw [hsum]
  rw [add_comm X 1] at hbin
  linear_combination -hbin

private theorem integral_two_inverse (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (2 : integralRationals p)*smallIntegralInverse p 2=1 := by
  apply Subtype.ext
  change (integralRationals p).subtype
    ((2 : integralRationals p)*smallIntegralInverse p 2)=1
  rw [map_mul, map_ofNat]
  change 2*(smallIntegralInverse p 2).val=1
  rw [smallIntegralInverse_value p 2 (by omega) (by omega)]
  norm_num

/-- The odd entropy has a canonical integral model, including the removed top Frobenius term. -/
theorem oddEntropyIntegral_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    C (2*(p : integralRationals p))*oddEntropyIntegral p =
      (1+X)^p-(1-X)^p-2*X^p := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hminus := congrArg (fun P : (integralRationals p)[X] => P.comp (-X))
    (fullEntropyIntegral_source p)
  simp only [mul_comp, C_comp, pow_comp, add_comp, one_comp, X_comp,
    sub_comp, ←sub_eq_add_neg] at hminus
  rw [hodd.neg_pow (X : (integralRationals p)[X])] at hminus
  have hc : C (2*(p : integralRationals p))*C (smallIntegralInverse p 2) =
      C (p : integralRationals p) := by
    rw [←C_mul]
    congr 1
    linear_combination (p : integralRationals p)*integral_two_inverse p hp
  rw [oddEntropyIntegral, ←mul_assoc, hc, mul_sub,
    fullEntropyIntegral_source p, hminus]
  ring

noncomputable def oddEntropyQ (p : ℕ) : ℚ[X] :=
  C (1/(2*(p : ℚ)))*((1+X)^p-(1-X)^p-2*X^p)

theorem oddEntropyIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (oddEntropyIntegral p).map (integralRationals p).subtype=oddEntropyQ p := by
  have hraw := congrArg (Polynomial.map (integralRationals p).subtype)
    (oddEntropyIntegral_source p hp)
  have hc : (integralRationals p).subtype (2*(p : integralRationals p)) =
      2*(p : ℚ) := by rw [map_mul, map_ofNat, map_natCast]
  have h : C (2*(p : ℚ)) * (oddEntropyIntegral p).map (integralRationals p).subtype =
      (1+X)^p-(1-X)^p-2*X^p := by
    simpa only [Polynomial.map_mul, Polynomial.map_C, hc,
      Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_ofNat] using hraw
  have hp0 : (2*(p : ℚ)) ≠ 0 := by
    exact_mod_cast (by omega : 2*p ≠ 0)
  apply mul_left_cancel₀ (C_ne_zero.mpr hp0)
  rw [h, oddEntropyQ, ←mul_assoc, ←C_mul, mul_one_div_cancel hp0, C_1, one_mul]

/-- Reduction uses the original integer quotient theorem, rather than a Q-to-field map. -/
theorem fullEntropyIntegral_field_value (p : ℕ) [Fact p.Prime] (_hp : 19 ≤ p)
    (z : integralRationals p) :
    residueHom p ((fullEntropyIntegral p).eval z)=
      -WPFiniteField.ell p (-residueHom p z) := by
  simp only [fullEntropyIntegral, eval_finsetSum, eval_mul, eval_C, eval_pow,
    eval_X, map_sum, map_mul, map_pow, WPFiniteField.ell,
    ←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hc : residueHom p ((((Nat.choose p j : ℤ)/(p : ℤ) : ℤ) : integralRationals p)) =
      (-1 : ZMod p)^(j-1)/(j : ZMod p) := by
    simpa only [map_intCast] using WPFiniteInversion.divided_choose_cast p j hj
  have hs : (-1 : ZMod p)^j = -(-1)^(j-1) := by
    calc
      _ = (-1 : ZMod p)^(j-1)*(-1) := by
        rw [←pow_succ, Nat.sub_add_cancel (by have hh := Finset.mem_Ico.mp hj; omega)]
      _ = _ := by ring
  have hz : (-residueHom p z)^j =
      (-1 : ZMod p)^j*(residueHom p z)^j := by rw [neg_pow]
  rw [hc, hz, hs]
  ring

/-- The full polynomial reduction retains the alternating divided-binomial sign. -/
theorem fullEntropyIntegral_field (p : ℕ) [Fact p.Prime] :
    (fullEntropyIntegral p).map (residueHom p) =
      -(WPFiniteAffineLog.LP p : (ZMod p)[X]).comp (-X) := by
  simp only [fullEntropyIntegral, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    WPFiniteAffineLog.LP, sum_comp, mul_comp, C_comp, pow_comp, X_comp,
    ←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hs : (-1 : ZMod p)^j = -(-1)^(j-1) := by
    calc
      _ = (-1 : ZMod p)^(j-1)*(-1) := by
        rw [←pow_succ, Nat.sub_add_cancel (by have hh := Finset.mem_Ico.mp hj; omega)]
      _ = _ := by ring
  have hc : (((Nat.choose p j : ℤ)/(p : ℤ) : ℤ) : ZMod p) =
      -((j : ZMod p)⁻¹ * (-1)^j) := by
    rw [WPFiniteInversion.divided_choose_cast p j hj, hs]
    ring
  have hcoef : residueHom p ((((Nat.choose p j : ℤ)/(p : ℤ) : ℤ) : integralRationals p)) =
      -((j : ZMod p)⁻¹ * (-1)^j) := by simpa only [map_intCast] using hc
  have hxj : (- (X : (ZMod p)[X]))^j =
      (-1 : (ZMod p)[X])^j*X^j := by rw [neg_pow]
  rw [hcoef, hxj]
  simp only [map_neg, map_mul, map_pow, map_one]
  ring

/-- The actual integral odd polynomial reduces to the whole literal OP polynomial. -/
theorem oddEntropyIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (oddEntropyIntegral p).map (residueHom p) =
      (WPFiniteKSource.OP p : (ZMod p)[X]) := by
  have hx : (- (X : (ZMod p)[X])).comp (-X) = X := by
    simp only [neg_comp, X_comp, neg_neg]
  rw [oddEntropyIntegral, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_sub, Polynomial.map_comp, Polynomial.map_neg,
    Polynomial.map_X, smallIntegralInverse_field p 2 (by omega) (by omega),
    fullEntropyIntegral_field p]
  simp only [neg_comp, comp_assoc, hx, comp_X, WPFiniteKSource.OP]
  ring

/-- Base change reaches arbitrary characteristic-p points, including nonsplit primes. -/
theorem oddEntropyIntegral_base_change_eval {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (u : K) :
    (((oddEntropyIntegral p).map (residueHom p)).map
      (ZMod.castHom (dvd_refl p) K)).eval u = WPFiniteField.O p u := by
  rw [oddEntropyIntegral_field p hp]
  have hm : (WPFiniteKSource.OP p : (ZMod p)[X]).map
      (ZMod.castHom (dvd_refl p) K) = (WPFiniteKSource.OP p : K[X]) := by
    simp only [WPFiniteKSource.OP, WPFiniteAffineLog.LP, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_sub, Polynomial.map_comp,
      Polynomial.map_neg, Polynomial.map_X, Polynomial.map_sum,
      Polynomial.map_pow, map_inv₀, map_ofNat, map_natCast]
  rw [hm, WPFiniteKSource.OP_eval]

theorem oddEntropyIntegral_field_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (z : integralRationals p) :
    residueHom p ((oddEntropyIntegral p).eval z)=WPFiniteField.O p (residueHom p z) := by
  rw [oddEntropyIntegral, eval_mul, eval_C, eval_sub, eval_comp,
    eval_neg, eval_X, map_mul, map_sub,
    fullEntropyIntegral_field_value p hp, fullEntropyIntegral_field_value p hp,
    map_neg, neg_neg, smallIntegralInverse_field p 2 (by omega) (by omega)]
  unfold WPFiniteField.O
  ring

end WPFieldAssembly.ActualEntropyOdd
