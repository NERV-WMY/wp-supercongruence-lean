import WPFieldAssembly.ActualHFTransmutation

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualHFTransmutation WPFieldAssembly.ActualSB101Trace
  WPFieldAssembly.ActualBalancedTrace WPFieldAssembly.ActualGreenCommonTrace
  WPPIntegralReduction WPActualRankTwoHatLift WPActualEtaIntegrality

namespace WPFieldAssembly.ActualSigmaIntegral

set_option maxHeartbeats 1600000

section FieldSource
variable {K L : Type*} [Field K] [Field L]

theorem D_coefficientMap (f : K →+* L) (G : K[T;T⁻¹]) :
    WPActualChiSource.coefficientMap f (D G) =
      D (WPActualChiSource.coefficientMap f G) := by
  ext j
  rw [WPActualChiSource.coefficientMap_coeff, D_coeff, D_coeff,
    WPActualChiSource.coefficientMap_coeff, map_mul, map_intCast]

theorem Abar_invert : invert (WPFiniteZSource.Abar : K[X]).toLaurent =
    T (-2) * (WPFiniteZSource.Abar : K[X]).toLaurent := by
  have hA : (WPFiniteZSource.Abar : K[X]).toLaurent = 17 * T 1 - 4 * T 2 - 4 := by
    simp only [WPFiniteZSource.Abar, map_mul, map_sub, map_ofNat,
      Polynomial.toLaurent_X, map_one]
    rw [show (T 2 : K[T;T⁻¹]) = T 1 * T 1 by rw [← T_add]; norm_num]
    ring
  have h2 : (T (-2) : K[T;T⁻¹]) * T 2 = 1 := by rw [← T_add]; norm_num
  have h1 : (T (-2) : K[T;T⁻¹]) * T 1 = T (-1) := by rw [← T_add]; norm_num
  rw [hA]
  simp only [map_sub, map_mul, map_ofNat, invert_T]
  linear_combination 4 * h2 - 17 * h1

theorem squaredCoordinate_invert :
    invert (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent =
      T (-1) * (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent := by
  have ht : (T (-1) : K[T;T⁻¹]) * T 1 = 1 := by rw [← T_add]; norm_num
  simp only [WPFiniteWSource.squaredCoordinate, map_mul, map_add,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X, map_one, invert_C, invert_T]
  linear_combination -LaurentPolynomial.C (5 : K)⁻¹ * ht

theorem R_reflection (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (T (-2) : K[T;T⁻¹]) * invert (WPFiniteZSource.R p) =
      T (-(((p - 1) / 2 : ℕ) : ℤ)) * WPFiniteZSource.R p := by
  have ht : (T (-2) : K[T;T⁻¹]) * T (p : ℤ) * T (-2) ^ (p - 1) *
      T (-1) ^ ((p - 1) / 2) = T (-(((p - 1) / 2 : ℕ) : ℤ)) * T (-(p : ℤ)) := by
    simp only [T_pow, ← T_add]
    congr 1
    omega
  simp only [WPFiniteZSource.R, map_mul, map_pow, invert_C, invert_T,
    neg_neg, Abar_invert, squaredCoordinate_invert, mul_pow]
  linear_combination LaurentPolynomial.C (1 / 2 : K) *
    (WPFiniteZSource.Abar : K[X]).toLaurent ^ (p - 1) *
    (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent ^ ((p - 1) / 2) * ht

theorem symmetric_P_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    D (WPFiniteZSource.P p u + invert (WPFiniteZSource.P p u)) =
      WPFiniteZSource.R p * (1 - T (-(((p - 1) / 2 : ℕ) : ℤ))) := by
  have ht : (T (-2) : K[T;T⁻¹]) * T 1 = T (-1) := by rw [← T_add]; norm_num
  rw [map_add, D_invert, WPFiniteZSource.P_derivative p hp u]
  simp only [map_sub, map_mul, invert_C, invert_T, neg_neg]
  linear_combination -R_reflection (K := K) p hp + LaurentPolynomial.C (1 / 2 : K) * ht

theorem comparisonField_derivative_closed (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsAlgClosed K] (hp : 19 ≤ p) :
    D (comparisonField (K := K) p) =
      WPFiniteZSource.R p * (1 - T (-(((p - 1) / 2 : ℕ) : ℤ))) := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (1 / 5 : K) (by norm_num : 0 < (2 : ℕ))
  rw [← actual_P_symmetric_comparison p hp u hu]
  exact symmetric_P_derivative p hp u

theorem R_map (p : ℕ) (f : K →+* L) :
    WPActualChiSource.coefficientMap f (WPFiniteZSource.R p) =
      (WPFiniteZSource.R p : L[T;T⁻¹]) := by
  simp only [WPFiniteZSource.R, map_mul, map_pow,
    WPActualChiSource.coefficientMap_C, WPActualChiSource.coefficientMap_T,
    WPActualChiSource.coefficientMap_toLaurent, map_div₀, map_one, map_ofNat,
    WPFiniteZSource.Abar, WPFiniteWSource.squaredCoordinate,
    Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_C,
    Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_one, map_inv₀]
end FieldSource

theorem comparisonField_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    D (comparisonField (K := ZMod p) p) =
      WPFiniteZSource.R p * (1 - T (-(((p - 1) / 2 : ℕ) : ℤ))) := by
  let K := AlgebraicClosure (ZMod p)
  let f : ZMod p →+* K := ActualThreePhase.φ p
  apply WPLaurentIntegralResidue.coefficientMap_injective f f.injective
  rw [D_coefficientMap, comparisonField_map]
  simp only [map_mul, map_sub, map_one, R_map, WPActualChiSource.coefficientMap_T]
  exact comparisonField_derivative_closed p hp

noncomputable def actualBSourceIntegral (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[T;T⁻¹] :=
  LaurentPolynomial.C (smallIntegralInverse p 2 * smallIntegralInverse p 5 ^ (2 * (p - 1))) *
    T (-(p : ℤ)) * (comparisonCoordinateI p).toLaurent ^ ((p - 1) / 2) *
    (1 - T (-(((p - 1) / 2 : ℕ) : ℤ))) * (actualAbarIntegral p).toLaurent ^ (p - 1)

theorem actualBSourceIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (integralRationals p).subtype (actualBSourceIntegral p) =
      actualBSourceQ p := by
  have hscalar : (integralRationals p).subtype
      (smallIntegralInverse p 2 * smallIntegralInverse p 5 ^ (2 * (p-1))) =
        (1/2 : ℚ)*(1/5 : ℚ)^(2*(p-1)) := by
    simp only [map_mul, map_pow, Subring.subtype_apply,
      smallIntegralInverse_value p 2 (by omega) (by omega),
      smallIntegralInverse_value p 5 (by omega) (by omega), Nat.cast_ofNat]
  have hcoord : (comparisonCoordinateI p).map (integralRationals p).subtype =
      ActualGreenPrimitive.greenCoordinateQ p := by
    simp only [comparisonCoordinateI, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_one, Subring.subtype_apply]
    rw [smallIntegralInverse_value p 5 (by omega) (by omega)]
    norm_num [ActualGreenPrimitive.greenCoordinateQ]
  have hA : (actualAbarIntegral p).map (integralRationals p).subtype =
      (WPFiniteZSource.Abar : ℚ[X]) := by
    simp only [actualAbarIntegral, WPFiniteZSource.Abar, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_one]
  calc
    _ = LaurentPolynomial.C ((integralRationals p).subtype
        (smallIntegralInverse p 2 * smallIntegralInverse p 5 ^ (2*(p-1)))) *
      T (-(p : ℤ)) *
      ((comparisonCoordinateI p).map (integralRationals p).subtype).toLaurent ^ ((p-1)/2) *
      (1-T (-(((p-1)/2 : ℕ) : ℤ))) *
      ((actualAbarIntegral p).map (integralRationals p).subtype).toLaurent ^ (p-1) := by
        simp only [actualBSourceIntegral, map_mul, map_pow, map_sub, map_one,
          WPActualChiSource.coefficientMap_C, WPActualChiSource.coefficientMap_T,
          WPActualChiSource.coefficientMap_toLaurent]
    _ = _ := by simp only [hscalar, hcoord, hA, actualBSourceQ]

theorem actualBSourceIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (residueHom p) (actualBSourceIntegral p) =
      WPFiniteZSource.R p * (1 - T (-(((p - 1) / 2 : ℕ) : ℤ))) := by
  have h5 : (5 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have he : (1 / 5 : ZMod p) ^ (2 * (p - 1)) = 1 := by
    rw [Nat.mul_comm 2 (p - 1), pow_mul,
      ZMod.pow_card_sub_one_eq_one (one_div_ne_zero h5), one_pow]
  have hscalar : residueHom p
      (smallIntegralInverse p 2 * smallIntegralInverse p 5 ^ (2*(p-1))) =
        (1/2 : ZMod p) := by
    simp only [map_mul, map_pow,
      smallIntegralInverse_field p 2 (by omega) (by omega),
      smallIntegralInverse_field p 5 (by omega) (by omega), Nat.cast_ofNat]
    simp only [one_div] at he ⊢
    rw [he, mul_one]
  have hA : (actualAbarIntegral p).map (residueHom p) =
      (WPFiniteZSource.Abar : (ZMod p)[X]) := by
    simp only [actualAbarIntegral, WPFiniteZSource.Abar, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_one]
  calc
    _ = LaurentPolynomial.C (residueHom p
        (smallIntegralInverse p 2 * smallIntegralInverse p 5 ^ (2*(p-1)))) *
      T (-(p : ℤ)) *
      ((comparisonCoordinateI p).map (residueHom p)).toLaurent ^ ((p-1)/2) *
      (1-T (-(((p-1)/2 : ℕ) : ℤ))) *
      ((actualAbarIntegral p).map (residueHom p)).toLaurent ^ (p-1) := by
        simp only [actualBSourceIntegral, map_mul, map_pow, map_sub, map_one,
          WPActualChiSource.coefficientMap_C, WPActualChiSource.coefficientMap_T,
          WPActualChiSource.coefficientMap_toLaurent]
    _ = _ := by
      rw [hscalar, comparisonCoordinateI_field p hp, hA]
      unfold WPFiniteZSource.R
      ring

theorem derivative_integral (p : ℕ) [Fact p.Prime] (L : ℚ[T;T⁻¹])
    (hL : L ∈ integralLaurent p) : D L ∈ integralLaurent p := by
  intro j
  rw [D_coeff]
  exact (integralRationals p).mul_mem (intCast_mem (integralRationals p) (j + 1)) (hL (j + 1))

theorem mapped_integral (p : ℕ) [Fact p.Prime] (L : (integralRationals p)[T;T⁻¹]) :
    WPActualChiSource.coefficientMap (integralRationals p).subtype L ∈ integralLaurent p := by
  intro j
  rw [WPActualChiSource.coefficientMap_coeff]
  exact (L.coeff j).property

theorem residue_mapped (p : ℕ) [Fact p.Prime] (L : (integralRationals p)[T;T⁻¹]) :
    WPLaurentIntegralResidue.residueLaurent p
      ⟨WPActualChiSource.coefficientMap (integralRationals p).subtype L, mapped_integral p L⟩ =
        WPActualChiSource.coefficientMap (residueHom p) L := by
  ext j
  rw [WPLaurentIntegralResidue.residueLaurent_coeff,
    WPActualChiSource.coefficientMap_coeff, WPActualChiSource.coefficientMap_coeff]
  rfl

theorem residue_derivative (p : ℕ) [Fact p.Prime] (L : (integralRationals p)[T;T⁻¹]) :
    WPLaurentIntegralResidue.residueLaurent p
      ⟨D (WPActualChiSource.coefficientMap (integralRationals p).subtype L),
        derivative_integral p _ (mapped_integral p L)⟩ =
      D (WPActualChiSource.coefficientMap (residueHom p) L) := by
  ext j
  rw [WPLaurentIntegralResidue.residueLaurent_coeff, D_coeff, D_coeff,
    WPActualChiSource.coefficientMap_coeff, WPActualChiSource.coefficientMap_coeff]
  have hm : ((j + 1 : ℤ) : ℚ) * (L.coeff (j + 1)).val ∈ integralRationals p :=
    (integralRationals p).mul_mem (intCast_mem (integralRationals p) (j + 1))
      (L.coeff (j + 1)).property
  change residueHom p
      ⟨((j + 1 : ℤ) : ℚ) * (L.coeff (j + 1)).val, hm⟩ =
    ((j + 1 : ℤ) : ZMod p) * residueHom p (L.coeff (j + 1))
  have hc : (⟨((j + 1 : ℤ) : ℚ) * (L.coeff (j + 1)).val, hm⟩ : integralRationals p) =
      ((j + 1 : ℤ) : integralRationals p) * L.coeff (j + 1) := by
    apply Subtype.ext
    change ((j + 1 : ℤ) : ℚ) * (L.coeff (j + 1)).val =
      (integralRationals p).subtype
        (((j + 1 : ℤ) : integralRationals p) * L.coeff (j + 1))
    simp only [map_mul, map_intCast, Subring.subtype_apply]
  rw [hc, map_mul, map_intCast]

/-- The actual comparison derivative has zero field residue, coefficient by coefficient. -/
theorem actual_sigma_numerator_residue_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPLaurentIntegralResidue.residueZero p
      (D (comparisonRational p hp) - actualBSourceQ p) := by
  have hS : comparisonRational p hp ∈ integralLaurent p := mapped_integral p (comparisonIntegral p)
  have hB : actualBSourceQ p ∈ integralLaurent p := by
    rw [← actualBSourceIntegral_value p hp]
    exact mapped_integral p _
  have hD := derivative_integral p _ hS
  have hi := (integralLaurent p).sub_mem hD hB
  refine ⟨hi, ?_⟩
  have hsub : (⟨D (comparisonRational p hp) - actualBSourceQ p, hi⟩ : integralLaurent p) =
      ⟨D (comparisonRational p hp), hD⟩ - ⟨actualBSourceQ p, hB⟩ := by apply Subtype.ext; rfl
  rw [hsub, map_sub]
  have hd : WPLaurentIntegralResidue.residueLaurent p ⟨D (comparisonRational p hp), hD⟩ =
      D (comparisonField (K := ZMod p) p) := by
    exact (residue_derivative p (comparisonIntegral p)).trans
      (congrArg D (comparisonIntegral_field p hp))
  have hb : WPLaurentIntegralResidue.residueLaurent p ⟨actualBSourceQ p, hB⟩ =
      WPFiniteZSource.R p * (1 - T (-(((p - 1) / 2 : ℕ) : ℤ))) := by
    have hBlift : (⟨actualBSourceQ p, hB⟩ : integralLaurent p) =
        ⟨WPActualChiSource.coefficientMap (integralRationals p).subtype
          (actualBSourceIntegral p), mapped_integral p (actualBSourceIntegral p)⟩ := by
      apply Subtype.ext
      exact (actualBSourceIntegral_value p hp).symm
    rw [hBlift, residue_mapped, actualBSourceIntegral_field p hp]
  rw [hd, hb, comparisonField_derivative p hp, sub_self]

/-- Honest p-division of the complete actual comparison source, without a chosen residue value. -/
theorem actualSigmaQ_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualSigmaQ p hp ∈ integralLaurent p := by
  obtain ⟨hi, hz⟩ := (WPLaurentIntegralResidue.residueZero_iff p _).mp
    (actual_sigma_numerator_residue_zero p hp)
  intro j
  have hd := WPActualChiSource.divide_prime_integral p
    ((D (comparisonRational p hp) - actualBSourceQ p).coeff j) (hi j) (hz j)
  have hc : (actualSigmaQ p hp).coeff j =
      (D (comparisonRational p hp) - actualBSourceQ p).coeff j / (p : ℚ) := by
    rw [actualSigmaQ, ← LaurentPolynomial.smul_eq_C_mul]
    change (1 / (p : ℚ)) *
      (D (comparisonRational p hp) - actualBSourceQ p).coeff j = _
    ring
  rw [hc]
  exact hd

noncomputable def actualSigmaIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[T;T⁻¹] :=
  WPLaurentIntegralResidue.integralLift p ⟨actualSigmaQ p hp, actualSigmaQ_integral p hp⟩

theorem actualSigmaIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (integralRationals p).subtype (actualSigmaIntegral p hp) =
      actualSigmaQ p hp := WPLaurentIntegralResidue.integralLift_rational p _

end WPFieldAssembly.ActualSigmaIntegral
