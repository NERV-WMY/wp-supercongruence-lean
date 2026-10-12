import WPActualRankTwoFixedDegree

open scoped Polynomial
open Polynomial WPPIntegralReduction WPNativeParameterTaylor WPActualNativeParameter
  WPActualRankTwoParameter WPActualRankTwoGaussODE WPActualRankTwoLegendreField
  WPActualRankTwoFirstLift WPActualRankTwoFixedDegree

namespace WPActualRankTwoLowTaylor

set_option maxHeartbeats 800000

/-- The derivative of the actual fixed-degree finite quotient at mu=0. -/
noncomputable def fixedJetCoefficient (d n : ℕ) : ℚ :=
  quotientJet (fixedNumerator ℚ d n) (fixedDenominator ℚ n) 0

noncomputable def fixedJetPolynomial (d : ℕ) : ℚ[X] :=
  rankCoefficientPolynomial d (fixedJetCoefficient d)

noncomputable def fixedJetJacobi (d : ℕ) : ℚ[X] :=
  (fixedJetPolynomial d).comp (C (1 / 2) * (1 - X))

/-- The literal actual low-node error, divided in Q by p^2. -/
noncomputable def fixedErrorCoefficient (p n : ℕ) : ℚ :=
  (rankCoefficient n (-(p : ℚ) / 6) -
    ((shiftedLegendre (p / 6)).map (Int.castRingHom ℚ)).coeff n +
      (p : ℚ) / 6 * fixedJetCoefficient (p / 6) n) / (p : ℚ) ^ 2

theorem fixedJetCoefficient_integral (p d n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) : 0 ≤ padicValRat p (fixedJetCoefficient d n) := by
  rw [fixedJetCoefficient, ← fixedFirstOriginIntegral_value p d n hp hn]
  exact (fixedFirstOriginIntegral p d n hp hn).property

theorem actual_fixedErrorCoefficient_remainder (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    ∃ r : integralRationals p, fixedErrorCoefficient p n = r.val / 36 := by
  obtain ⟨r, hr⟩ := actual_fixedCoefficient_first_remainder p (p / 6) n hp hn
  rw [fixedCoefficient_origin_legendre, ← actual_low_fixedCoefficient p n hp] at hr
  refine ⟨r, ?_⟩
  unfold fixedErrorCoefficient fixedJetCoefficient
  rw [hr]
  have hpq : (p : ℚ) ≠ 0 := by positivity
  field_simp

theorem actual_fixedErrorCoefficient_integral (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) : 0 ≤ padicValRat p (fixedErrorCoefficient p n) := by
  obtain ⟨r, hr⟩ := actual_fixedErrorCoefficient_remainder p n hp hn
  have hs : (1 / 6 : ℚ) ∈ integralRationals p :=
    WPFiniteConductorPolynomial.small_inverse_integral p 6 (by norm_num) (by omega)
  have hi := (integralRationals p).mul_mem r.property ((integralRationals p).pow_mem hs 2)
  have he : fixedErrorCoefficient p n = r.val * (1 / 6 : ℚ) ^ 2 := by rw [hr]; ring
  rw [he]
  exact hi

noncomputable def fixedErrorPolynomial (p : ℕ) : ℚ[X] :=
  rankCoefficientPolynomial (p / 6) (fixedErrorCoefficient p)

noncomputable def fixedErrorJacobi (p : ℕ) : ℚ[X] :=
  (fixedErrorPolynomial p).comp (C (1 / 2) * (1 - X))

/-- The whole original actual low node has the exact integral Taylor remainder. -/
theorem actual_low_fixedTaylor_polynomial (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    rankNodePolynomial p 1 - (shiftedLegendre (p / 6)).map (Int.castRingHom ℚ) +
      C ((p : ℚ) / 6) * fixedJetPolynomial (p / 6) =
        C ((p : ℚ) ^ 2) * fixedErrorPolynomial p := by
  have hpq : (p : ℚ) ≠ 0 := by positivity
  ext n
  rw [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, fixedJetPolynomial, fixedErrorPolynomial,
    rankCoefficientPolynomial_coeff, rankCoefficientPolynomial_coeff]
  by_cases hn : n < p / 6 + 1
  · rw [if_pos hn, if_pos hn, rankNodePolynomial,
      WPActualNativeSecondTaylor.coefficientPolynomial_coeff, if_pos (by omega)]
    norm_num only [Nat.cast_one, neg_one_mul]
    unfold fixedErrorCoefficient
    field_simp
  · rw [if_neg hn, if_neg hn, Polynomial.coeff_eq_zero_of_natDegree_lt
      ((actual_low_rankNode_degree p hp).trans_lt (by omega))]
    have hd : ((shiftedLegendre (p / 6)).map (Int.castRingHom ℚ)).natDegree ≤ p / 6 :=
      Polynomial.natDegree_map_le.trans (by rw [natDegree_shiftedLegendre])
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))]
    ring

theorem actual_low_fixedTaylor_jacobi (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    rankJacobiNode p 1 - rationalLegendre (p / 6) +
      C ((p : ℚ) / 6) * fixedJetJacobi (p / 6) =
        C ((p : ℚ) ^ 2) * fixedErrorJacobi p := by
  have h := congrArg (fun P : ℚ[X] => P.comp (C (1 / 2) * (1 - X)))
    (actual_low_fixedTaylor_polynomial p hp)
  simpa only [Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
    Polynomial.C_comp, rankJacobiNode, rationalLegendre, fixedJetJacobi, fixedErrorJacobi] using h

noncomputable def fixedIntegralJetPolynomial (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[X] :=
  rankCoefficientPolynomial (p / 6)
    (fun n => if hn : n < p then fixedFirstOriginIntegral p (p / 6) n hp hn else 0)

theorem fixedIntegralJetPolynomial_value (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (fixedIntegralJetPolynomial p hp).map (integralRationals p).subtype = fixedJetPolynomial (p / 6) := by
  ext n
  rw [Polynomial.coeff_map, fixedIntegralJetPolynomial, fixedJetPolynomial,
    rankCoefficientPolynomial_coeff, rankCoefficientPolynomial_coeff]
  by_cases hn : n < p / 6 + 1
  · rw [if_pos hn, if_pos hn, dif_pos (by omega)]
    exact fixedFirstOriginIntegral_value p (p / 6) n hp (by omega)
  · simp [hn]

noncomputable def fixedIntegralErrorPolynomial (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[X] :=
  rankCoefficientPolynomial (p / 6)
    (fun n => if hn : n < p then
      ⟨fixedErrorCoefficient p n, actual_fixedErrorCoefficient_integral p n hp hn⟩ else 0)

theorem fixedIntegralErrorPolynomial_value (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (fixedIntegralErrorPolynomial p hp).map (integralRationals p).subtype = fixedErrorPolynomial p := by
  ext n
  rw [Polynomial.coeff_map, fixedIntegralErrorPolynomial, fixedErrorPolynomial,
    rankCoefficientPolynomial_coeff, rankCoefficientPolynomial_coeff]
  by_cases hn : n < p / 6 + 1
  · rw [if_pos hn, if_pos hn, dif_pos (by omega)]
    rfl
  · simp [hn]

noncomputable def fixedIntegralJetJacobi (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[X] :=
  (fixedIntegralJetPolynomial p hp).comp (C (integralHalf p hp) * (1 - X))

noncomputable def fixedIntegralErrorJacobi (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[X] :=
  (fixedIntegralErrorPolynomial p hp).comp (C (integralHalf p hp) * (1 - X))

theorem fixedIntegralJetJacobi_value (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (fixedIntegralJetJacobi p hp).map (integralRationals p).subtype = fixedJetJacobi (p / 6) := by
  rw [fixedIntegralJetJacobi, Polynomial.map_comp, fixedIntegralJetPolynomial_value]
  simp [fixedJetJacobi, Polynomial.map_mul, Polynomial.map_sub, integralHalf]

theorem fixedIntegralErrorJacobi_value (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (fixedIntegralErrorJacobi p hp).map (integralRationals p).subtype = fixedErrorJacobi p := by
  rw [fixedIntegralErrorJacobi, Polynomial.map_comp, fixedIntegralErrorPolynomial_value]
  simp [fixedErrorJacobi, Polynomial.map_mul, Polynomial.map_sub, integralHalf]

theorem fixedJetCoefficient_zero (d : ℕ) : fixedJetCoefficient d 0 = 0 := by
  simp [fixedJetCoefficient, quotientJet, fixedNumerator, fixedDenominator]

theorem fixedJetJacobi_endpoint_one (d : ℕ) : (fixedJetJacobi d).eval 1 = 0 := by
  rw [fixedJetJacobi, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, sub_self, mul_zero]
  rw [← Polynomial.coeff_zero_eq_eval_zero, fixedJetPolynomial,
    rankCoefficientPolynomial_coeff, if_pos (by omega), fixedJetCoefficient_zero]

theorem fixedJetJacobi_degree (d : ℕ) : (fixedJetJacobi d).natDegree ≤ d := by
  unfold fixedJetJacobi
  calc
    _ ≤ (fixedJetPolynomial d).natDegree * (C (1 / 2 : ℚ) * (1 - X)).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ d * 1 := Nat.mul_le_mul (rankCoefficientPolynomial_degree _ _) jacobiCoordinate_degree
    _ = _ := Nat.mul_one _

theorem polynomial_subtype_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (fun P : (integralRationals p)[X] => P.map (integralRationals p).subtype) := by
  intro P Q h
  ext n
  have hc := congrArg (fun R : ℚ[X] => R.coeff n) h
  simpa only [Polynomial.coeff_map, Subring.subtype_apply] using hc

theorem legendreJacobi_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (d : ℕ) (P : K[X]) :
    (legendreJacobi d P).map f = legendreJacobi d (P.map f) := by
  simp [legendreJacobi, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.derivative_map]

noncomputable def carrySource {K : Type*} [CommRing K] (d : ℕ) (P Q : K[X]) : K[X] :=
  36 * legendreJacobi d P + 12 * (X * Q.derivative - C (d : K) * Q)

theorem carrySource_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (d : ℕ) (P Q : K[X]) :
    (carrySource d P Q).map f = carrySource d (P.map f) (Q.map f) := by
  simp [carrySource, legendreJacobi_map, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.derivative_map]

noncomputable def integralSixth (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) : integralRationals p :=
  ⟨1 / 6, WPFiniteConductorPolynomial.small_inverse_integral p 6 (by norm_num) (by omega)⟩

theorem integralSixth_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    residueHom p (integralSixth p hp) = (1 / 6 : ZMod p) := by
  change ((1 / 6 : ℚ) : ZMod p) = (1 / 6 : ZMod p)
  norm_num [Rat.cast_def]

noncomputable def lowCarryIntegral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[X] :=
  rankCoefficientPolynomial (p / 6)
    (fun n => ⟨lowCarryCoefficient p n, actual_lowCarryCoefficient_integral p n hp⟩)

theorem lowCarryIntegral_value (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (lowCarryIntegral p hp).map (integralRationals p).subtype = lowCarryPolynomial p := by
  ext n
  rw [Polynomial.coeff_map, lowCarryIntegral, lowCarryPolynomial,
    rankCoefficientPolynomial_coeff, WPActualNativeSecondTaylor.coefficientPolynomial_coeff]
  split_ifs <;> rfl

/-- The actual first quotient retains the full integral second-order error. -/
theorem actual_lowCarry_fixedTaylor (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    lowCarryPolynomial p + C (1 / 6 : ℚ) * fixedJetJacobi (p / 6) =
      C (p : ℚ) * fixedErrorJacobi p := by
  have ht := actual_low_fixedTaylor_jacobi p hp
  have hc := actual_lowCarryPolynomial_source p hp
  have h6 : C ((p : ℚ) / 6) = C (p : ℚ) * C (1 / 6 : ℚ) := by rw [← map_mul]; congr 1; ring
  have h2 : C ((p : ℚ) ^ 2) = C (p : ℚ) * C (p : ℚ) := by rw [← map_mul]; congr 1; ring
  rw [h6, h2] at ht
  have hz : C (p : ℚ) *
      (lowCarryPolynomial p + C (1 / 6 : ℚ) * fixedJetJacobi (p / 6) -
        C (p : ℚ) * fixedErrorJacobi p) = 0 := by
    linear_combination ht - hc
  have he := (mul_eq_zero.mp hz).resolve_left (by simp; positivity)
  exact sub_eq_zero.mp he

theorem actual_lowCarry_integralTaylor (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    lowCarryIntegral p hp + C (integralSixth p hp) * fixedIntegralJetJacobi p hp =
      C (p : integralRationals p) * fixedIntegralErrorJacobi p hp := by
  apply polynomial_subtype_injective p
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    lowCarryIntegral_value, fixedIntegralJetJacobi_value, fixedIntegralErrorJacobi_value,
    Polynomial.map_natCast, map_natCast]
  change lowCarryPolynomial p + C (1 / 6 : ℚ) * fixedJetJacobi (p / 6) =
    C (p : ℚ) * fixedErrorJacobi p
  exact actual_lowCarry_fixedTaylor p hp

noncomputable def actualVariationField (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) : (ZMod p)[X] :=
  (fixedIntegralJetJacobi p hp).map (residueHom p)

noncomputable def actualCarryField (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) : (ZMod p)[X] :=
  (lowCarryIntegral p hp).map (residueHom p)

theorem fixedIntegralJetJacobi_degree (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (fixedIntegralJetJacobi p hp).natDegree ≤ p / 6 := by
  unfold fixedIntegralJetJacobi
  have hcoordinate : (C (integralHalf p hp) * (1 - X)).natDegree ≤ 1 := by compute_degree
  exact Polynomial.natDegree_comp_le.trans
    ((Nat.mul_le_mul (rankCoefficientPolynomial_degree _ _) hcoordinate).trans (by simp))

theorem actualVariationField_degree (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (actualVariationField p hp).natDegree ≤ p / 6 :=
  Polynomial.natDegree_map_le.trans (fixedIntegralJetJacobi_degree p hp)

theorem fixedIntegralJetJacobi_endpoint_one (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (fixedIntegralJetJacobi p hp).eval 1 = 0 := by
  apply Subtype.ext
  have h := congrArg (fun P : ℚ[X] => P.eval 1) (fixedIntegralJetJacobi_value p hp)
  rw [fixedJetJacobi_endpoint_one] at h
  change ((fixedIntegralJetJacobi p hp).map (integralRationals p).subtype).eval
    ((integralRationals p).subtype 1) = 0 at h
  rw [Polynomial.eval_map_apply] at h
  exact h

theorem actualVariationField_endpoint_one (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (actualVariationField p hp).eval 1 = 0 := by
  unfold actualVariationField
  rw [← (residueHom p).map_one]
  rw [Polynomial.eval_map_apply, fixedIntegralJetJacobi_endpoint_one, map_zero]

theorem actual_lowCarry_variation_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    actualCarryField p hp + C (1 / 6 : ZMod p) * actualVariationField p hp = 0 := by
  have h := congrArg (fun P : (integralRationals p)[X] => P.map (residueHom p))
    (actual_lowCarry_integralTaylor p hp)
  have hpn : residueHom p (p : integralRationals p) = 0 := by simp
  simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    integralSixth_field, hpn, Polynomial.C_0,
    zero_mul, actualCarryField, actualVariationField] using h

theorem actual_lowCarryIntegral_ODE (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    36 * legendreJacobi (p / 6) (lowCarryIntegral p hp) +
      12 * (X * (rankIntegralJacobi p hp 1).derivative -
        C ((p / 6 : ℕ) : integralRationals p) * rankIntegralJacobi p hp 1) = 0 := by
  apply polynomial_subtype_injective p
  change (carrySource (p / 6) (lowCarryIntegral p hp) (rankIntegralJacobi p hp 1)).map
    (integralRationals p).subtype = (0 : (integralRationals p)[X]).map (integralRationals p).subtype
  rw [carrySource_map, lowCarryIntegral_value, rankIntegralJacobi_value, Polynomial.map_zero]
  exact actual_lowCarryPolynomial_ODE p hp

theorem actual_lowCarry_field_ODE (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    36 * legendreJacobi (p / 6) (actualCarryField p hp) +
      12 * (X * (actualLegendreJacobi p).derivative -
        C ((p / 6 : ℕ) : ZMod p) * actualLegendreJacobi p) = 0 := by
  have h := congrArg (fun P : (integralRationals p)[X] => P.map (residueHom p))
    (actual_lowCarryIntegral_ODE p hp)
  change (carrySource (p / 6) (lowCarryIntegral p hp) (rankIntegralJacobi p hp 1)).map
    (residueHom p) = (0 : (integralRationals p)[X]).map (residueHom p) at h
  rw [carrySource_map, rankIntegralJacobi_field, Polynomial.map_zero] at h
  exact h

theorem actualVariationField_ODE (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    legendreJacobi (p / 6) (actualVariationField p hp) =
      2 * (X * (actualLegendreJacobi p).derivative -
        C ((p / 6 : ℕ) : ZMod p) * actualLegendreJacobi p) := by
  have h6 : (6 : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 6 p).mp hz
    have := Nat.le_of_dvd (by norm_num : 0 < 6) hd
    omega
  have hcarry : actualCarryField p hp = -C (1 / 6 : ZMod p) * actualVariationField p hp := by
    linear_combination actual_lowCarry_variation_field p hp
  have h := actual_lowCarry_field_ODE p hp
  rw [hcarry, neg_mul, ← mul_neg, legendreJacobi_C_mul] at h
  have hLneg : legendreJacobi (p / 6) (-actualVariationField p hp) =
      -legendreJacobi (p / 6) (actualVariationField p hp) := by
    simp only [legendreJacobi, Polynomial.derivative_neg]
    ring
  rw [hLneg] at h
  have hsix : (36 : (ZMod p)[X]) * C (1 / 6 : ZMod p) = 6 := by
    rw [show (36 : (ZMod p)[X]) = C (36 : ZMod p) by rfl,
      show (6 : (ZMod p)[X]) = C (6 : ZMod p) by rfl, ← map_mul]
    congr 1
    field_simp [h6]
    ring
  have hz : (6 : (ZMod p)[X]) *
      (legendreJacobi (p / 6) (actualVariationField p hp) -
        2 * (X * (actualLegendreJacobi p).derivative -
          C ((p / 6 : ℕ) : ZMod p) * actualLegendreJacobi p)) = 0 := by
    linear_combination -h - hsix * legendreJacobi (p / 6) (actualVariationField p hp)
  have h6poly : (6 : (ZMod p)[X]) ≠ 0 := by
    rw [show (6 : (ZMod p)[X]) = C (6 : ZMod p) by rfl]
    exact Polynomial.C_ne_zero.mpr h6
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h6poly)

end WPActualRankTwoLowTaylor
