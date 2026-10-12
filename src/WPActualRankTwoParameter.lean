import WPActualNativeSecondTaylor

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPActualNativeParameter
  WPActualNativeFirstJet WPActualNativeSecondTaylor WPActualNativeHasse WPNativeParameterTaylor

namespace WPActualRankTwoParameter

/-- The two original upper Gauss parameters, with their fixed denominators cleared. -/
noncomputable def rankNumerator (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  ∏ j ∈ Finset.range n,
    (C (6 * (j : R) + 1) + 6 * X) * (C (6 * (j : R) + 5) + 6 * X)

/-- The original lower parameter 1+epsilon and n!, retaining the factor36. -/
noncomputable def rankDenominator (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  ∏ j ∈ Finset.range n, C (36 * ((j : R) + 1)) * (C ((j : R) + 1) + X)

theorem rankNumerator_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) : (rankNumerator R n).map f = rankNumerator S n := by
  simp only [rankNumerator, Polynomial.map_prod, Polynomial.map_mul,
    Polynomial.map_add, Polynomial.map_ofNat, Polynomial.map_X,
    Polynomial.map_natCast, Polynomial.map_one,
    map_add, map_mul, map_ofNat, map_natCast, map_one]

theorem rankDenominator_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) : (rankDenominator R n).map f = rankDenominator S n := by
  simp only [rankDenominator, Polynomial.map_prod, Polynomial.map_mul,
    Polynomial.map_add, Polynomial.map_ofNat, Polynomial.map_X,
    Polynomial.map_natCast, Polynomial.map_one,
    map_add, map_mul, map_ofNat, map_natCast, map_one]

theorem rankNumerator_eval_succ (R : Type*) [CommRing R] (n : ℕ) (t : R) :
    (rankNumerator R (n + 1)).eval t = (rankNumerator R n).eval t *
      ((6 * (n : R) + 1 + 6 * t) * (6 * (n : R) + 5 + 6 * t)) := by
  simp [rankNumerator, Finset.prod_range_succ]

theorem rankDenominator_eval_succ (R : Type*) [CommRing R] (n : ℕ) (t : R) :
    (rankDenominator R (n + 1)).eval t = (rankDenominator R n).eval t *
      (36 * ((n : R) + 1) * ((n : R) + 1 + t)) := by
  simp [rankDenominator, Finset.prod_range_succ]

theorem rankDenominator_eval_zero (R : Type*) [CommRing R] (n : ℕ) :
    (rankDenominator R n).eval 0 = (36 : R) ^ n * (n.factorial : R) ^ 2 := by
  induction n with
  | zero => simp [rankDenominator]
  | succ n ih =>
    rw [rankDenominator_eval_succ, ih, pow_succ, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

noncomputable def rankCoefficient (n : ℕ) (t : ℚ) : ℚ :=
  (rankNumerator ℚ n).eval t / (rankDenominator ℚ n).eval t

/-- The actual low and high nodes use k=1 and k=5 in this common integral model. -/
noncomputable def rankNode (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (k : ℕ) :
    integralRationals p := (k : integralRationals p) * integralNode p hp

theorem rankNode_value (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (k : ℕ) :
    (rankNode p hp k).val = -(k : ℚ) * (p : ℚ) / 6 := by
  simp only [rankNode, Subring.coe_mul, Subring.coe_natCast, integralNode_value]
  ring

theorem rankNode_residue (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (k : ℕ) :
    residueHom p (rankNode p hp k) = 0 := by
  rw [rankNode, map_mul, integralNode_residue, mul_zero]

theorem rankDenominator_origin_residue_ne_zero (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) : (rankDenominator (ZMod p) n).eval 0 ≠ 0 := by
  rw [rankDenominator_eval_zero]
  have hsmall (a : ℕ) (ha : 0 < a) (hlt : a < p) : (a : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have := Nat.le_of_dvd ha hd
    omega
  have h36 : (36 : ZMod p) ≠ 0 := by
    rw [show (36 : ZMod p) = 2 ^ 2 * 3 ^ 2 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ (hsmall 2 (by omega) (by omega)))
      (pow_ne_zero _ (hsmall 3 (by omega) (by omega)))
  have hfac : (n.factorial : ZMod p) ≠ 0 := by
    intro hz
    have := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp
      ((ZMod.natCast_eq_zero_iff _ _).mp hz)
    omega
  exact mul_ne_zero (pow_ne_zero _ h36) (pow_ne_zero _ hfac)

theorem rankDenominator_node_residue (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (k : ℕ) :
    residueHom p ((rankDenominator (integralRationals p) n).eval (rankNode p hp k)) =
      (rankDenominator (ZMod p) n).eval 0 := by
  rw [← Polynomial.eval_map_apply, rankDenominator_map, rankNode_residue]

theorem rankDenominator_node_unit (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (k : ℕ) :
    ((rankDenominator (integralRationals p) n).eval (rankNode p hp k)).val ≠ 0 ∧
      (((rankDenominator (integralRationals p) n).eval (rankNode p hp k)).val)⁻¹ ∈
        integralRationals p := by
  apply integral_inverse_of_residue_ne_zero
  rw [rankDenominator_node_residue]
  exact rankDenominator_origin_residue_ne_zero p n hp hn

noncomputable def rankIntegralCoefficient (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (k : ℕ) : integralRationals p :=
  (rankNumerator (integralRationals p) n).eval (rankNode p hp k) *
    ⟨((rankDenominator (integralRationals p) n).eval (rankNode p hp k)).val⁻¹,
      (rankDenominator_node_unit p n hp hn k).2⟩

theorem rankIntegralCoefficient_value (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (k : ℕ) :
    (rankIntegralCoefficient p n hp hn k).val =
      rankCoefficient n (-(k : ℚ) * (p : ℚ) / 6) := by
  unfold rankIntegralCoefficient rankCoefficient
  change ((rankNumerator (integralRationals p) n).eval (rankNode p hp k)).val *
    (((rankDenominator (integralRationals p) n).eval (rankNode p hp k)).val⁻¹) = _
  rw [evaluate_subtype, evaluate_subtype, rankNumerator_map,
    rankDenominator_map, rankNode_value]
  simp only [div_eq_mul_inv]

theorem actual_rankCoefficient_integral (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (k : ℕ) :
    0 ≤ padicValRat p (rankCoefficient n (-(k : ℚ) * (p : ℚ) / 6)) := by
  rw [← rankIntegralCoefficient_value p n hp hn k]
  exact (rankIntegralCoefficient p n hp hn k).property

noncomputable def rankFieldCoefficient (p n : ℕ) [Fact p.Prime] : ZMod p :=
  (rankNumerator (ZMod p) n).eval 0 / (rankDenominator (ZMod p) n).eval 0

/-- Every actual node has the same field coefficient; its inverse is transported as a unit. -/
theorem rankIntegralCoefficient_residue (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (k : ℕ) :
    residueHom p (rankIntegralCoefficient p n hp hn k) = rankFieldCoefficient p n := by
  let D := (rankDenominator (integralRationals p) n).eval (rankNode p hp k)
  let u : integralRationals p := ⟨D.val⁻¹, (rankDenominator_node_unit p n hp hn k).2⟩
  have hu : D * u = 1 := by
    apply Subtype.ext
    change D.val * D.val⁻¹ = 1
    exact mul_inv_cancel₀ (rankDenominator_node_unit p n hp hn k).1
  have hD := rankDenominator_origin_residue_ne_zero p n hp hn
  have hm := congrArg (residueHom p) hu
  rw [map_mul, map_one] at hm
  change residueHom p ((rankDenominator (integralRationals p) n).eval
    (rankNode p hp k)) * residueHom p u = 1 at hm
  rw [rankDenominator_node_residue] at hm
  have hi : residueHom p u = ((rankDenominator (ZMod p) n).eval 0)⁻¹ := by
    apply mul_left_cancel₀ hD
    rw [hm, mul_inv_cancel₀ hD]
  change residueHom p
    ((rankNumerator (integralRationals p) n).eval (rankNode p hp k) * u) = _
  rw [map_mul, hi, ← Polynomial.eval_map_apply, rankNumerator_map, rankNode_residue]
  rfl

theorem actual_rankCoefficient_reduction (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (k : ℕ) :
    (rankCoefficient n (-(k : ℚ) * (p : ℚ) / 6) : ZMod p) = rankFieldCoefficient p n := by
  have h := rankIntegralCoefficient_residue p n hp hn k
  change ((rankIntegralCoefficient p n hp hn k).val : ZMod p) = _ at h
  rwa [rankIntegralCoefficient_value] at h

theorem actual_low_rankNumerator_zero (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : p / 6 < n) :
    (rankNumerator ℚ n).eval (-(p : ℚ) / 6) = 0 := by
  rw [rankNumerator, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hn)
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  rcases prime_six_classes p hp with hp1 | hp5
  · have hq : (p : ℚ) = 6 * ((p / 6 : ℕ) : ℚ) + 1 := by exact_mod_cast hp1
    rw [hq]
    ring
  · have hq : (p : ℚ) = 6 * ((p / 6 : ℕ) : ℚ) + 5 := by exact_mod_cast hp5
    rw [hq]
    ring

theorem actual_high_rankNumerator_zero (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : p - 1 - p / 6 < n) :
    (rankNumerator ℚ n).eval (-(5 : ℚ) * (p : ℚ) / 6) = 0 := by
  rw [rankNumerator, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hn)
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  rcases prime_six_classes p hp with hp1 | hp5
  · have he : p - 1 - p / 6 = 5 * (p / 6) := by omega
    have hq : (p : ℚ) = 6 * ((p / 6 : ℕ) : ℚ) + 1 := by exact_mod_cast hp1
    rw [he, Nat.cast_mul, Nat.cast_ofNat, hq]
    ring
  · have he : p - 1 - p / 6 = 5 * (p / 6) + 4 := by omega
    have hq : (p : ℚ) = 6 * ((p / 6 : ℕ) : ℚ) + 5 := by exact_mod_cast hp5
    rw [he, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hq]
    ring

/-- The two actual rational terminating nodes use the identical full upper indexing. -/
noncomputable def rankNodePolynomial (p k : ℕ) : ℚ[X] :=
  coefficientPolynomial (p - 1 - p / 6)
    (fun n => rankCoefficient n (-(k : ℚ) * (p : ℚ) / 6))

theorem rankNodePolynomial_origin (p k : ℕ) : (rankNodePolynomial p k).eval 0 = 1 := by
  rw [rankNodePolynomial, coefficientPolynomial_origin]
  simp [rankCoefficient, rankNumerator, rankDenominator]

theorem actual_low_rankNode_degree (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (rankNodePolynomial p 1).natDegree ≤ p / 6 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [rankNodePolynomial, coefficientPolynomial_coeff]
  split_ifs
  · simp only [Nat.cast_one, neg_one_mul, rankCoefficient]
    rw [actual_low_rankNumerator_zero p n hp hn, zero_div]
  · rfl

theorem actual_high_rankNode_degree (p : ℕ) :
    (rankNodePolynomial p 5).natDegree ≤ p - 1 - p / 6 :=
  coefficientPolynomial_degree _ _

theorem actual_rankNodePolynomial_reduction (p k n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) : ((rankNodePolynomial p k).coeff n : ZMod p) =
      if n < p - 1 - p / 6 + 1 then rankFieldCoefficient p n else 0 := by
  rw [rankNodePolynomial, coefficientPolynomial_coeff]
  split_ifs with hn
  · exact actual_rankCoefficient_reduction p n hp (by omega) k
  · simp

theorem actual_two_rankNode_reductions (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    ((rankNodePolynomial p 1).coeff n : ZMod p) =
      ((rankNodePolynomial p 5).coeff n : ZMod p) := by
  rw [actual_rankNodePolynomial_reduction p 1 n hp,
    actual_rankNodePolynomial_reduction p 5 n hp]

theorem actual_rankFieldCoefficient_high_zero (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : p / 6 < n) (hpn : n < p) : rankFieldCoefficient p n = 0 := by
  rw [← actual_rankCoefficient_reduction p n hp hpn 1]
  simp only [Nat.cast_one, neg_one_mul, rankCoefficient]
  rw [actual_low_rankNumerator_zero p n hp hn, zero_div, Rat.cast_zero]

/-- The actual NC51 nodes in their printed Jacobi variable T, z=(1-T)/2. -/
noncomputable def rankJacobiNode (p k : ℕ) : ℚ[X] :=
  (rankNodePolynomial p k).comp (C (1 / 2) * (1 - X))

theorem rankJacobiNode_endpoint_one (p k : ℕ) : (rankJacobiNode p k).eval 1 = 1 := by
  rw [rankJacobiNode, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, sub_self, mul_zero]
  exact rankNodePolynomial_origin p k

theorem jacobiCoordinate_degree : (C (1 / 2 : ℚ) * (1 - X)).natDegree ≤ 1 := by
  have hC : (C (1 / 2 : ℚ)).natDegree ≤ 0 := by simp
  have hL : (1 - X : ℚ[X]).natDegree ≤ 1 := by
    simpa using Polynomial.natDegree_sub_le_of_le
      (show (1 : ℚ[X]).natDegree ≤ 0 by simp) (Polynomial.natDegree_X_le (R := ℚ))
  simpa using Polynomial.natDegree_mul_le_of_le hC hL

theorem actual_low_rankJacobi_degree (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (rankJacobiNode p 1).natDegree ≤ p / 6 := by
  unfold rankJacobiNode
  calc
    _ ≤ (rankNodePolynomial p 1).natDegree * (C (1 / 2 : ℚ) * (1 - X)).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ (p / 6) * 1 := Nat.mul_le_mul (actual_low_rankNode_degree p hp) jacobiCoordinate_degree
    _ = _ := Nat.mul_one _

theorem actual_high_rankJacobi_degree (p : ℕ) :
    (rankJacobiNode p 5).natDegree ≤ p - 1 - p / 6 := by
  unfold rankJacobiNode
  calc
    _ ≤ (rankNodePolynomial p 5).natDegree * (C (1 / 2 : ℚ) * (1 - X)).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ (p - 1 - p / 6) * 1 := Nat.mul_le_mul (actual_high_rankNode_degree p) jacobiCoordinate_degree
    _ = _ := Nat.mul_one _

end WPActualRankTwoParameter
