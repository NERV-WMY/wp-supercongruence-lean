import WPActualRankTwoParameter

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPActualNativeFirstJet WPActualNativeSecondTaylor
  WPActualRankTwoParameter WPActualNativeSecondJet

namespace WPActualRankTwoDividedDifference

/-- Exact two-node quotient division inside any commutative integral coefficient model. -/
theorem integral_two_quotient_difference {R : Type*} [CommRing R]
    (A D : R[X]) (a b ua ub : R) (ha : D.eval a * ua = 1) (hb : D.eval b * ub = 1) :
    ∃ r : R, A.eval a * ua - A.eval b * ub = (a - b) * r := by
  have hd : X - C b ∣ A * C (D.eval b) - C (A.eval b) * D := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  obtain ⟨E, hE⟩ := hd
  have he := congrArg (Polynomial.eval a) hE
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at he
  refine ⟨E.eval a * ua * ub, ?_⟩
  calc
    _ = (A.eval a * D.eval b - A.eval b * D.eval a) * ua * ub := by
      linear_combination -(A.eval a * ua) * hb + (A.eval b * ub) * ha
    _ = _ := by rw [he]; ring

/-- The zero-centered second quotient expansion keeps its exact integral cubic term. -/
theorem integral_centred_second_expansion {R : Type*} [CommRing R]
    (A D : R[X]) (t u0 ut : R) (h0 : D.eval 0 * u0 = 1) (ht : D.eval t * ut = 1) :
    ∃ r : R, A.eval t * ut - A.eval 0 * u0 -
      t * firstJetOver A D 0 u0 - t ^ 2 * secondJetOver A D 0 u0 = t ^ 3 * r := by
  obtain ⟨E, hE⟩ := quotient_taylor_divisible A D 0 u0 h0
  rw [Polynomial.taylor_zero, Polynomial.taylor_zero] at hE
  have he := congrArg (Polynomial.eval t) hE
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at he
  refine ⟨-E.eval t * ut, ?_⟩
  linear_combination -ut * he +
    (A.eval 0 * u0 + t * firstJetOver A D 0 u0 + t ^ 2 * secondJetOver A D 0 u0) * ht

theorem rankDenominator_origin_unit (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    ((rankDenominator (integralRationals p) n).eval 0).val ≠ 0 ∧
      (((rankDenominator (integralRationals p) n).eval 0).val)⁻¹ ∈ integralRationals p := by
  simpa only [rankNode, Nat.cast_zero, zero_mul] using rankDenominator_node_unit p n hp hn 0

noncomputable def rankOriginInverse (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) : integralRationals p :=
  ⟨((rankDenominator (integralRationals p) n).eval 0).val⁻¹,
    (rankDenominator_origin_unit p n hp hn).2⟩

noncomputable def rankFirstOriginIntegral (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) : integralRationals p :=
  firstJetOver (rankNumerator (integralRationals p) n)
    (rankDenominator (integralRationals p) n) 0 (rankOriginInverse p n hp hn)

noncomputable def rankSecondOriginIntegral (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) : integralRationals p :=
  secondJetOver (rankNumerator (integralRationals p) n)
    (rankDenominator (integralRationals p) n) 0 (rankOriginInverse p n hp hn)

noncomputable def rankDividedCoefficient (p n : ℕ) : ℚ :=
  (rankCoefficient n (-(p : ℚ) / 6) - rankCoefficient n (-(5 : ℚ) * (p : ℚ) / 6)) /
    (2 * (p : ℚ) / 3)

/-- The literal NC52 divided coefficient, normalized by the actual node difference. -/
theorem actual_rankDividedCoefficient_remainder (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    ∃ r : integralRationals p, rankDividedCoefficient p n = r.val := by
  let A := rankNumerator (integralRationals p) n
  let D := rankDenominator (integralRationals p) n
  let a := rankNode p hp 1
  let b := rankNode p hp 5
  let ua : integralRationals p := ⟨(D.eval a).val⁻¹, (rankDenominator_node_unit p n hp hn 1).2⟩
  let ub : integralRationals p := ⟨(D.eval b).val⁻¹, (rankDenominator_node_unit p n hp hn 5).2⟩
  have ha : D.eval a * ua = 1 := by
    apply Subtype.ext
    change (D.eval a).val * (D.eval a).val⁻¹ = 1
    exact mul_inv_cancel₀ (rankDenominator_node_unit p n hp hn 1).1
  have hb : D.eval b * ub = 1 := by
    apply Subtype.ext
    change (D.eval b).val * (D.eval b).val⁻¹ = 1
    exact mul_inv_cancel₀ (rankDenominator_node_unit p n hp hn 5).1
  obtain ⟨r, hr⟩ := integral_two_quotient_difference A D a b ua ub ha hb
  have h := congrArg Subtype.val hr
  change (rankIntegralCoefficient p n hp hn 1).val -
    (rankIntegralCoefficient p n hp hn 5).val = (a.val - b.val) * r.val at h
  rw [rankIntegralCoefficient_value, rankIntegralCoefficient_value] at h
  change rankCoefficient n (-(1 : ℚ) * (p : ℚ) / 6) -
    rankCoefficient n (-(5 : ℚ) * (p : ℚ) / 6) =
      ((rankNode p hp 1).val - (rankNode p hp 5).val) * r.val at h
  rw [rankNode_value, rankNode_value] at h
  norm_num only [neg_one_mul] at h
  refine ⟨r, ?_⟩
  unfold rankDividedCoefficient
  rw [h]
  have hpq : (p : ℚ) ≠ 0 := by positivity
  field_simp
  ring

theorem actual_rankDividedCoefficient_integral (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) : 0 ≤ padicValRat p (rankDividedCoefficient p n) := by
  obtain ⟨r, hr⟩ := actual_rankDividedCoefficient_remainder p n hp hn
  rw [hr]
  exact r.property

/-- The actual divided difference has its fixed next coefficient and an integral p^2 remainder. -/
theorem actual_rankDividedCoefficient_second (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    ∃ r : integralRationals p,
      rankDividedCoefficient p n - (rankFirstOriginIntegral p n hp hn).val +
        (p : ℚ) * (rankSecondOriginIntegral p n hp hn).val = (p : ℚ) ^ 2 * r.val / 144 := by
  let A := rankNumerator (integralRationals p) n
  let D := rankDenominator (integralRationals p) n
  let a := rankNode p hp 1
  let b := rankNode p hp 5
  let u0 := rankOriginInverse p n hp hn
  let ua : integralRationals p := ⟨(D.eval a).val⁻¹, (rankDenominator_node_unit p n hp hn 1).2⟩
  let ub : integralRationals p := ⟨(D.eval b).val⁻¹, (rankDenominator_node_unit p n hp hn 5).2⟩
  have h0 : D.eval 0 * u0 = 1 := by
    apply Subtype.ext
    change (D.eval 0).val * (D.eval 0).val⁻¹ = 1
    exact mul_inv_cancel₀ (rankDenominator_origin_unit p n hp hn).1
  have ha : D.eval a * ua = 1 := by
    apply Subtype.ext
    change (D.eval a).val * (D.eval a).val⁻¹ = 1
    exact mul_inv_cancel₀ (rankDenominator_node_unit p n hp hn 1).1
  have hb : D.eval b * ub = 1 := by
    apply Subtype.ext
    change (D.eval b).val * (D.eval b).val⁻¹ = 1
    exact mul_inv_cancel₀ (rankDenominator_node_unit p n hp hn 5).1
  obtain ⟨ra, hRa⟩ := integral_centred_second_expansion A D a u0 ua h0 ha
  obtain ⟨rb, hRb⟩ := integral_centred_second_expansion A D b u0 ub h0 hb
  have hA := congrArg Subtype.val hRa
  have hB := congrArg Subtype.val hRb
  change (rankIntegralCoefficient p n hp hn 1).val - (A.eval 0).val * u0.val -
    a.val * (rankFirstOriginIntegral p n hp hn).val -
    a.val ^ 2 * (rankSecondOriginIntegral p n hp hn).val = a.val ^ 3 * ra.val at hA
  change (rankIntegralCoefficient p n hp hn 5).val - (A.eval 0).val * u0.val -
    b.val * (rankFirstOriginIntegral p n hp hn).val -
    b.val ^ 2 * (rankSecondOriginIntegral p n hp hn).val = b.val ^ 3 * rb.val at hB
  change (rankIntegralCoefficient p n hp hn 1).val - (A.eval 0).val * u0.val -
    (rankNode p hp 1).val * (rankFirstOriginIntegral p n hp hn).val -
    (rankNode p hp 1).val ^ 2 * (rankSecondOriginIntegral p n hp hn).val =
      (rankNode p hp 1).val ^ 3 * ra.val at hA
  change (rankIntegralCoefficient p n hp hn 5).val - (A.eval 0).val * u0.val -
    (rankNode p hp 5).val * (rankFirstOriginIntegral p n hp hn).val -
    (rankNode p hp 5).val ^ 2 * (rankSecondOriginIntegral p n hp hn).val =
      (rankNode p hp 5).val ^ 3 * rb.val at hB
  norm_num only [rankIntegralCoefficient_value, rankNode_value, neg_one_mul] at hA hB
  have hd : rankCoefficient n (-(p : ℚ) / 6) -
      rankCoefficient n (-(5 : ℚ) * (p : ℚ) / 6) =
    (2 * (p : ℚ) / 3) * (rankFirstOriginIntegral p n hp hn).val -
      (2 * (p : ℚ) ^ 2 / 3) * (rankSecondOriginIntegral p n hp hn).val +
      (p : ℚ) ^ 3 / 216 * (-ra.val + 125 * rb.val) := by
    linear_combination hA - hB
  refine ⟨-ra + 125 * rb, ?_⟩
  change rankDividedCoefficient p n - (rankFirstOriginIntegral p n hp hn).val +
    (p : ℚ) * (rankSecondOriginIntegral p n hp hn).val =
      (p : ℚ) ^ 2 * (-ra.val + 125 * rb.val) / 144
  unfold rankDividedCoefficient
  rw [hd]
  have hpq : (p : ℚ) ≠ 0 := by positivity
  field_simp
  ring

theorem rankFirstOriginIntegral_value (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    (rankFirstOriginIntegral p n hp hn).val =
      WPNativeParameterTaylor.quotientJet (rankNumerator ℚ n) (rankDenominator ℚ n) 0 := by
  have hD := (rankDenominator_origin_unit p n hp hn).1
  rw [evaluate_subtype, rankDenominator_map, Subring.coe_zero] at hD
  unfold rankFirstOriginIntegral firstJetOver rankOriginInverse
  change ((rankNumerator (integralRationals p) n).derivative.eval 0).val *
      (((rankDenominator (integralRationals p) n).eval 0).val⁻¹) -
    ((rankNumerator (integralRationals p) n).eval 0).val *
      ((rankDenominator (integralRationals p) n).derivative.eval 0).val *
      (((rankDenominator (integralRationals p) n).eval 0).val⁻¹) ^ 2 = _
  rw [derivative_evaluate_subtype, derivative_evaluate_subtype]
  simp only [evaluate_subtype, rankNumerator_map, rankDenominator_map, Subring.coe_zero]
  simpa only [firstJetOver] using firstJetOver_rational (rankNumerator ℚ n) (rankDenominator ℚ n) 0 hD

theorem rankSecondOriginIntegral_value (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    (rankSecondOriginIntegral p n hp hn).val =
      quotientSecondJet (rankNumerator ℚ n) (rankDenominator ℚ n) 0 := by
  unfold rankSecondOriginIntegral
  change (integralRationals p).subtype
    (secondJetOver (rankNumerator (integralRationals p) n)
      (rankDenominator (integralRationals p) n) 0 (rankOriginInverse p n hp hn)) = _
  rw [secondJetOver_map, rankNumerator_map, rankDenominator_map]
  unfold quotientSecondJet
  change secondJetOver (rankNumerator ℚ n) (rankDenominator ℚ n) 0
    (((rankDenominator (integralRationals p) n).eval 0).val⁻¹) = _
  rw [evaluate_subtype, rankDenominator_map, Subring.coe_zero]

theorem actual_rankDividedCoefficient_reduction (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    (rankDividedCoefficient p n : ZMod p) =
      residueHom p (rankFirstOriginIntegral p n hp hn) := by
  obtain ⟨r, hr⟩ := actual_rankDividedCoefficient_second p n hp hn
  let c : integralRationals p := ⟨rankDividedCoefficient p n,
    actual_rankDividedCoefficient_integral p n hp hn⟩
  let g := rankFirstOriginIntegral p n hp hn
  let k := rankSecondOriginIntegral p n hp hn
  let a : integralRationals p := ⟨1 / 2,
    WPFiniteConductorPolynomial.small_inverse_integral p 2 (by norm_num) (by omega)⟩
  let b : integralRationals p := ⟨1 / 6,
    WPFiniteConductorPolynomial.small_inverse_integral p 6 (by norm_num) (by omega)⟩
  have hR : c - g + (p : integralRationals p) * k =
      (p : integralRationals p) ^ 2 * (r * a ^ 2 * b ^ 2) := by
    apply Subtype.ext
    change rankDividedCoefficient p n - g.val + (p : ℚ) * k.val =
      (p : ℚ) ^ 2 * (r.val * (1 / 2 : ℚ) ^ 2 * (1 / 6 : ℚ) ^ 2)
    rw [hr]
    ring
  have hf := congrArg (residueHom p) hR
  simp only [map_add, map_sub, map_mul, map_pow, map_natCast, ZMod.natCast_self,
    zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero] at hf
  exact sub_eq_zero.mp hf

theorem actual_rankDividedCoefficient_derivative (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) : (rankDividedCoefficient p n : ZMod p) =
      (WPNativeParameterTaylor.quotientJet (rankNumerator ℚ n) (rankDenominator ℚ n) 0 : ZMod p) := by
  have h := actual_rankDividedCoefficient_reduction p n hp hn
  change (rankDividedCoefficient p n : ZMod p) =
    ((rankFirstOriginIntegral p n hp hn).val : ZMod p) at h
  rwa [rankFirstOriginIntegral_value] at h

noncomputable def rankDividedPolynomial (p : ℕ) : ℚ[X] :=
  coefficientPolynomial (p - 1 - p / 6) (rankDividedCoefficient p)

theorem rankDividedPolynomial_origin (p : ℕ) : (rankDividedPolynomial p).eval 0 = 0 := by
  rw [rankDividedPolynomial, coefficientPolynomial_origin]
  simp [rankDividedCoefficient, rankCoefficient, rankNumerator, rankDenominator]

theorem rankDividedPolynomial_degree (p : ℕ) :
    (rankDividedPolynomial p).natDegree ≤ p - 1 - p / 6 :=
  coefficientPolynomial_degree _ _

theorem actual_two_node_difference (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    rankNodePolynomial p 1 - rankNodePolynomial p 5 =
      C (2 * (p : ℚ) / 3) * rankDividedPolynomial p := by
  have hpq : (p : ℚ) ≠ 0 := by positivity
  ext n
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  simp only [rankNodePolynomial, rankDividedPolynomial, coefficientPolynomial_coeff]
  split_ifs with hn
  · norm_num only [neg_one_mul]
    unfold rankDividedCoefficient
    field_simp
  · simp

noncomputable def rankDividedJacobi (p : ℕ) : ℚ[X] :=
  (rankDividedPolynomial p).comp (C (1 / 2) * (1 - X))

theorem rankDividedJacobi_endpoint_one (p : ℕ) : (rankDividedJacobi p).eval 1 = 0 := by
  rw [rankDividedJacobi, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, sub_self, mul_zero]
  exact rankDividedPolynomial_origin p

theorem rankDividedJacobi_degree (p : ℕ) :
    (rankDividedJacobi p).natDegree ≤ p - 1 - p / 6 := by
  unfold rankDividedJacobi
  calc
    _ ≤ (rankDividedPolynomial p).natDegree * (C (1 / 2 : ℚ) * (1 - X)).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ (p - 1 - p / 6) * 1 := Nat.mul_le_mul (rankDividedPolynomial_degree p) jacobiCoordinate_degree
    _ = _ := Nat.mul_one _

theorem actual_two_jacobi_node_difference (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    rankJacobiNode p 1 - rankJacobiNode p 5 =
      C (2 * (p : ℚ) / 3) * rankDividedJacobi p := by
  have h := congrArg (fun P : ℚ[X] => P.comp (C (1 / 2) * (1 - X)))
    (actual_two_node_difference p hp)
  simpa only [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp,
    rankJacobiNode, rankDividedJacobi] using h

end WPActualRankTwoDividedDifference
