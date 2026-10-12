import WPLiteralAdapter.PrimitiveAttachment
import WPLiteralAdapter.EscapeAttachment
import WPLiteralAdapter.ConductorOrigin
import WPLiteralAdapter.SourceEscapePrecision
import WPLiteralAdapter.EndpointDescent

open scoped BigOperators LaurentSeries
open Polynomial HahnSeries WPForcedSourceStokes WPFiniteConductorPolynomial

namespace WPLiteralAdapter

noncomputable section

local notation "ι" => algebraMap ℚ[X] (RatFunc ℚ)

theorem actual_escape_polynomial_negative (P : ℚ[X]) (n : ℤ) (hn : n<0) :
    actualEscapeRationalCoefficient (ι P) n=0 := by
  rw [actualEscapeRationalCoefficient, actual_escape_polynomial_series,
    PowerSeries.coeff_coe, if_pos hn]

theorem actual_escape_tail_series (a₁ a₂ : ℚ) :
    actualEscapeRationalSeries (actualEscapeTail a₁ a₂) =
      HahnSeries.single (-1 : ℤ) (a₁/99) +
        HahnSeries.single (-2 : ℤ) (a₂/(99 : ℚ)^2) := by
  let Ψ : RatFunc ℚ →+* LaurentSeries ℚ :=
    (algebraMap (RatFunc ℚ) (LaurentSeries ℚ)).comp
      (rationalTranslationHom escapePoint)
  have hE : ι escape=99*symbol-50 := by
    norm_num [escape, symbol, map_ratCast, _root_.map_ofNat]
  have hs (q : ℚ) : Ψ (RatFunc.C q)=HahnSeries.C q := actual_escape_series_scalar q
  have he₁ : Ψ ((ι escape)⁻¹)=HahnSeries.single (-1 : ℤ) (1/(99 : ℚ)) := by
    rw [map_inv₀]
    change (actualEscapeRationalSeries (ι escape))⁻¹=_
    rw [actual_escape_polynomial_escape, HahnSeries.inv_single]
    norm_num
  have he₂ : (HahnSeries.single (-1 : ℤ) (1/(99 : ℚ)) : LaurentSeries ℚ)^2 =
      HahnSeries.single (-2 : ℤ) (1/(99 : ℚ)^2) := by
    rw [pow_two, HahnSeries.single_mul_single]
    norm_num
  have ht : actualEscapeTail a₁ a₂=RatFunc.C a₁*(ι escape)⁻¹+
      RatFunc.C a₂*((ι escape)⁻¹)^2 := by
    unfold actualEscapeTail
    simp only [← hE, div_eq_mul_inv, ← inv_pow]
  change Ψ (actualEscapeTail a₁ a₂)=_
  rw [ht]
  simp only [map_add, map_mul, map_pow, hs, he₁]
  rw [he₂]
  simp only [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add,
    div_eq_mul_inv, one_mul]

theorem actual_escape_tail_coefficient (a₁ a₂ : ℚ) (n : ℤ) :
    actualEscapeRationalCoefficient (actualEscapeTail a₁ a₂) n =
      (if n=(-1 : ℤ) then a₁/99 else 0)+
        (if n=(-2 : ℤ) then a₂/(99 : ℚ)^2 else 0) := by
  rw [actualEscapeRationalCoefficient, actual_escape_tail_series,
    HahnSeries.coeff_add, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs <;> rfl

theorem actual_beta_escape_negative_precision
    (p : ℕ) [Fact p.Prime] (hp : 19≤p) (n : ℤ) (hn : n<0) :
    precisionZero p 3 (actualEscapeRationalCoefficient (actualBetaFunctional p) n) := by
  let R := integralSubring p
  have h99 : (1/(99 : ℚ))∈R := escape_inverse_99_integral p hp
  by_cases h₁ : n=(-1 : ℤ)
  · subst n
    rw [actual_beta_escape_minus_one p (by omega)]
    convert precisionZero_mul_integral p 3 _ _
      (actual_conductor_escape_simple_precision p hp) h99 using 1
    ring
  by_cases h₂ : n=(-2 : ℤ)
  · subst n
    rw [actual_beta_escape_minus_two p (by omega)]
    have h99₂ : (1/(99 : ℚ)^2)∈R := by
      rw [show (1/(99 : ℚ)^2)=(1/(99 : ℚ))^2 by norm_num]
      exact R.pow_mem h99 2
    convert precisionZero_mul_integral p 3 _ _
      (actual_conductor_escape_double_precision p hp) h99₂ using 1
    ring
  exact Or.inl (actual_beta_escape_below p (by omega) n (by omega))

theorem actual_source_escape_negative_precision
    (p : ℕ) [Fact p.Prime] (hp : 19≤p) (n : ℤ) (hn : n<0) :
    precisionZero p 6 (actualEscapeRationalCoefficient (actualTotalSource p) n) := by
  have hA : precisionZero p 3 (WPReview.nativeEndpoint p) := by
    apply Or.inr
    rw [actual_native_endpoint_valuation p (by omega)]
    norm_num
  have hB := actual_beta_escape_negative_precision p hp n hn
  have hm := precisionZero_mul p 3 3 _ _ hA hB
  have he := actual_source_conductor_error_escape_precision p hp n
  rw [actual_escape_coefficient_sub, actual_escape_coefficient_scalar] at he
  convert precisionZero_add p 6 _ _ he hm using 1
  ring

theorem actual_negative_escape_scalar (p : ℕ) (hp : 0<p) (n : ℤ) (hn : n<0) :
    0=6750*((1-escapePoint)*((n+1 : ℤ) : ℚ)*
        actualEscapeRationalCoefficient (actualTotalPrimitive p) (n+1)-
      ((n : ℚ)+1/2)*actualEscapeRationalCoefficient (actualTotalPrimitive p) n)+
      3375*actualEscapeRationalCoefficient (actualTotalSource p) n+
      actualEscapeRationalCoefficient (nativeSquareForcing p) n := by
  have hL : 2*symbol*rationalDerivative (nativeWeightedG p)+nativeWeightedG p =
      ι (2*X*derivative (WPLiteralNativeNormalization.outerPolynomial p)+
        WPLiteralNativeNormalization.outerPolynomial p) := by
    rw [actual_weighted_G_outer_polynomial, rationalDerivative_polynomial]
    simp only [map_add, map_mul, _root_.map_ofNat, symbol]
  have h := congrArg (fun f => actualEscapeRationalCoefficient f n)
    (actual_full_forced_scalar p hp)
  rw [hL, actual_escape_polynomial_negative _ n hn] at h
  have h6750 : (6750 : RatFunc ℚ)=RatFunc.C (6750 : ℚ) := by norm_num
  have h3375 : (3375 : RatFunc ℚ)=RatFunc.C (3375 : ℚ) := by norm_num
  rw [h6750, h3375] at h
  simp only [actual_escape_coefficient_add, actual_escape_coefficient_scalar,
    actual_escape_beta_coefficient] at h
  exact h

theorem actual_total_primitive_negative_escape_coefficients (p : ℕ) (hp : 2≤p) :
    actualEscapeRationalCoefficient (actualTotalPrimitive p) (-3)=0 ∧
    actualEscapeRationalCoefficient (actualTotalPrimitive p) (-2)=
      escapeSquareTailTwo (actualPrimitiveNumerator p)/(99 : ℚ)^2 ∧
    actualEscapeRationalCoefficient (actualTotalPrimitive p) (-1)=
      escapeSquareTailOne (actualPrimitiveNumerator p)/99 := by
  have hc (n : ℤ) (hn : n<0) :
      actualEscapeRationalCoefficient (actualTotalPrimitive p) n =
        (if n=(-1 : ℤ) then escapeSquareTailOne (actualPrimitiveNumerator p)/99 else 0)+
        (if n=(-2 : ℤ) then escapeSquareTailTwo (actualPrimitiveNumerator p)/(99 : ℚ)^2 else 0) := by
    rw [actual_total_primitive_decomposition p hp, actual_escape_coefficient_add,
      actual_escape_polynomial_negative _ n hn, zero_add, actual_escape_tail_coefficient]
  refine ⟨?_, ?_, ?_⟩
  · simpa using hc (-3) (by norm_num)
  · simpa using hc (-2) (by norm_num)
  · simpa using hc (-1) (by norm_num)

/-- The actual scalar equation eliminates both genuine escape tails at precision six. -/
theorem actual_total_primitive_escape_tail_precision
    (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    precisionZero p 6 (escapeSquareTailOne (actualPrimitiveNumerator p)) ∧
      precisionZero p 6 (escapeSquareTailTwo (actualPrimitiveNumerator p)) := by
  let R := integralSubring p
  let a₁ := escapeSquareTailOne (actualPrimitiveNumerator p)
  let a₂ := escapeSquareTailTwo (actualPrimitiveNumerator p)
  rcases actual_total_primitive_negative_escape_coefficients p (by omega) with ⟨ht₃, ht₂, ht₁⟩
  have he₃ : (-6750*98*a₂)/(99 : ℚ)^3 =
      -(3375*actualEscapeRationalCoefficient (actualTotalSource p) (-3)+
        actualEscapeRationalCoefficient (nativeSquareForcing p) (-3)) := by
    have he := actual_negative_escape_scalar p (by omega) (-3) (by norm_num)
    rw [show (-3 : ℤ)+1=-2 by norm_num, ht₂, ht₃] at he
    norm_num [escapePoint] at he
    dsimp only [a₂]
    linear_combination -he
  have he₂ : (6750*(-49*a₁+(3/2)*a₂))/(99 : ℚ)^2 =
      -(3375*actualEscapeRationalCoefficient (actualTotalSource p) (-2)+
        actualEscapeRationalCoefficient (nativeSquareForcing p) (-2)) := by
    have he := actual_negative_escape_scalar p (by omega) (-2) (by norm_num)
    rw [show (-2 : ℤ)+1=-1 by norm_num, ht₁, ht₂] at he
    norm_num [escapePoint] at he
    dsimp only [a₁, a₂]
    linear_combination -he
  have hb₃ : precisionZero p 6 ((-6750*98*a₂)/(99 : ℚ)^3) := by
    rw [he₃]
    apply precisionZero_neg
    apply precisionZero_add p 6
    · convert precisionZero_mul_integral p 6 _ _
        (actual_source_escape_negative_precision p hp (-3) (by norm_num))
        (natCast_mem R 3375) using 1
      ring
    · exact actual_square_escape_minus_three_precision p hp
  have hb₂ : precisionZero p 6 ((6750*(-49*a₁+(3/2)*a₂))/(99 : ℚ)^2) := by
    rw [he₂]
    apply precisionZero_neg
    apply precisionZero_add p 6
    · convert precisionZero_mul_integral p 6 _ _
        (actual_source_escape_negative_precision p hp (-2) (by norm_num))
        (natCast_mem R 3375) using 1
      ring
    · exact actual_square_escape_minus_two_precision p hp
  have h₃ : precisionZero p 6 (-6750*98*a₂) := by
    have h := precisionZero_mul_integral p 6 _ _ hb₃ (R.pow_mem (natCast_mem R 99) 3)
    convert h using 1
    norm_num
  have h₂ : precisionZero p 6 (6750*(-49*a₁+(3/2)*a₂)) := by
    have h := precisionZero_mul_integral p 6 _ _ hb₂ (R.pow_mem (natCast_mem R 99) 2)
    convert h using 1
    norm_num
  exact precisionZero_escape_pole_elimination p hp a₁ a₂ h₃ h₂

theorem actual_weighted_G_high_zero (p k : ℕ) (hk : 3*p≤k) :
    actualRationalCoefficient (nativeWeightedG p) (k : ℤ)=0 := by
  rw [actual_weighted_G_outer_polynomial, actual_rational_polynomial_coefficient,
    WPLiteralNativeNormalization.outerPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro n hn
  have hn' := Finset.mem_range.mp hn
  have hne : 3*n≠k := by omega
  simp [Polynomial.coeff_monomial, hne]

theorem actual_total_beta_origin_high_precision
    (p : ℕ) [Fact p.Prime] (hp : 19≤p) (k : ℕ) (hk : 3*p≤k) :
    precisionZero p 6 (actualRationalCoefficient
      ((1-symbol)*rationalDerivative (actualTotalPrimitive p)-actualTotalPrimitive p/2) (k : ℤ)) := by
  let R := integralSubring p
  have he : 6750*actualRationalCoefficient
      ((1-symbol)*rationalDerivative (actualTotalPrimitive p)-actualTotalPrimitive p/2) (k : ℤ) =
      -(3375*actualRationalCoefficient (actualTotalSource p) (k : ℤ)+
        actualRationalCoefficient (nativeSquareForcing p) (k : ℤ)) := by
    have h := actual_full_source_coefficient p (by omega) (k : ℤ)
    rw [actual_weighted_G_high_zero p k hk, mul_zero,
      ← actual_beta_coefficient (actualTotalPrimitive p) (k : ℤ)] at h
    linear_combination -h
  have hs : precisionZero p 6 (6750*actualRationalCoefficient
      ((1-symbol)*rationalDerivative (actualTotalPrimitive p)-actualTotalPrimitive p/2) (k : ℤ)) := by
    rw [he]
    apply precisionZero_neg
    apply precisionZero_add p 6
    · convert precisionZero_mul_integral p 6 _ _
        (actual_source_high_origin_precision p hp k hk) (natCast_mem R 3375) using 1
      ring
    · exact actual_square_forcing_origin_precision p hp k
  have h2 : (1/2 : ℚ)∈R := small_inverse_integral p 2 (by norm_num) (by omega)
  have h3 : (1/3 : ℚ)∈R := small_inverse_integral p 3 (by norm_num) (by omega)
  have h5 : (1/5 : ℚ)∈R := small_inverse_integral p 5 (by norm_num) (by omega)
  have hi : (6750 : ℚ)⁻¹∈R := by
    rw [show (6750 : ℚ)⁻¹=(1/2)*(1/3)^3*(1/5)^3 by norm_num]
    exact R.mul_mem (R.mul_mem h2 (R.pow_mem h3 3)) (R.pow_mem h5 3)
  have h := precisionZero_mul_integral p 6 _ _ hs hi
  convert h using 1
  norm_num
  ring

theorem actual_polynomial_beta_origin_coefficient (P : ℚ[X]) (k : ℕ) :
    actualRationalCoefficient ((1-symbol)*rationalDerivative (ι P)-ι P/2) (k : ℤ) =
      ((k : ℚ)+1)*P.coeff (k+1)-((k : ℚ)+1/2)*P.coeff k := by
  rw [actual_beta_coefficient, show (k : ℤ)+1=((k+1 : ℕ) : ℤ) by omega,
    actual_rational_polynomial_coefficient, actual_rational_polynomial_coefficient]
  push_cast
  ring

theorem actual_polynomialPart_beta_origin_high_precision
    (p : ℕ) [Fact p.Prime] (hp : 19≤p) (k : ℕ) (hk : 3*p≤k) :
    precisionZero p 6 (actualRationalCoefficient
      ((1-symbol)*rationalDerivative (ι (rationalPolynomialPart (actualTotalPrimitive p)))-
        ι (rationalPolynomialPart (actualTotalPrimitive p))/2) (k : ℤ)) := by
  let P := rationalPolynomialPart (actualTotalPrimitive p)
  let A := actualEscapeTail (escapeSquareTailOne (actualPrimitiveNumerator p))
    (escapeSquareTailTwo (actualPrimitiveNumerator p))
  have hdec : actualTotalPrimitive p=ι P+A := actual_total_primitive_decomposition p (by omega)
  have hsplit : (1-symbol)*rationalDerivative (actualTotalPrimitive p)-actualTotalPrimitive p/2 =
      ((1-symbol)*rationalDerivative (ι P)-ι P/2)+((1-symbol)*rationalDerivative A-A/2) := by
    calc
      _=(1-symbol)*rationalDerivative (ι P+A)-(ι P+A)/2 :=
        congrArg (fun f : RatFunc ℚ => (1-symbol)*rationalDerivative f-f/2) hdec
      _=_ := by rw [rationalDerivative_add]; ring
  rcases actual_total_primitive_escape_tail_precision p hp with ⟨ha₁, ha₂⟩
  have ha := actual_escape_tail_beta_origin_precision p hp
    (escapeSquareTailOne (actualPrimitiveNumerator p))
    (escapeSquareTailTwo (actualPrimitiveNumerator p)) ha₁ ha₂ k
  have ht := actual_total_beta_origin_high_precision p hp k hk
  rw [hsplit, actual_rational_coefficient_add] at ht
  have hn := precisionZero_neg p 6 _ ha
  convert precisionZero_add p 6 _ _ ht hn using 1
  ring

theorem actual_polynomialPart_extended_endpoint_precision
    (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    precisionZero p 6 ((rationalPolynomialPart (actualTotalPrimitive p)).coeff (3*p)) := by
  apply six_step_polynomial_endpoint p hp _ (actual_total_primitive_polynomial_degree p (by omega))
  intro j _hj
  have h := actual_polynomialPart_beta_origin_high_precision p hp (3*p+j) (by omega)
  rw [actual_polynomial_beta_origin_coefficient] at h
  exact h

/-- The extended actual endpoint retains both tails. -/
theorem actual_total_primitive_endpoint_precision
    (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    precisionZero p 6 (actualRationalCoefficient (actualTotalPrimitive p) ((3*p : ℕ) : ℤ)) := by
  rcases actual_total_primitive_escape_tail_precision p hp with ⟨ha₁, ha₂⟩
  rw [actual_total_primitive_decomposition p (by omega), actual_rational_coefficient_add,
    actual_rational_polynomial_coefficient]
  exact precisionZero_add p 6 _ _ (actual_polynomialPart_extended_endpoint_precision p hp)
    (actual_escape_tail_origin_precision p hp (escapeSquareTailOne (actualPrimitiveNumerator p))
      (escapeSquareTailTwo (actualPrimitiveNumerator p)) ha₁ ha₂ (3*p))

end

end WPLiteralAdapter
