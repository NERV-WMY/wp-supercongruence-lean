import WPActualEscapeCoefficients
import WPActualSourceOriginPrecision

open WPFiniteConductorPolynomial

namespace WPLiteralAdapter

open WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 5000

attribute [local irreducible] integralRationalOrigin polynomialCoefficientSubring

@[simp] theorem actual_escape_coefficient_neg (f : RatFunc ℚ) (n : ℤ) :
    actualEscapeRationalCoefficient (-f) n = -actualEscapeRationalCoefficient f n := by
  change actualRationalCoefficient (rationalTranslationHom escapePoint (-f)) n = _
  rw [map_neg, actual_rational_coefficient_neg]
  rfl

@[simp] theorem actual_escape_coefficient_add (f g : RatFunc ℚ) (n : ℤ) :
    actualEscapeRationalCoefficient (f+g) n =
      actualEscapeRationalCoefficient f n+actualEscapeRationalCoefficient g n := by
  change actualRationalCoefficient (rationalTranslationHom escapePoint (f+g)) n = _
  rw [map_add, actual_rational_coefficient_add]
  rfl

@[simp] theorem actual_escape_coefficient_sub (f g : RatFunc ℚ) (n : ℤ) :
    actualEscapeRationalCoefficient (f-g) n =
      actualEscapeRationalCoefficient f n-actualEscapeRationalCoefficient g n := by
  change actualRationalCoefficient (rationalTranslationHom escapePoint (f-g)) n = _
  rw [map_sub, actual_rational_coefficient_sub]
  rfl

theorem actual_small_inverse_escape (p n : ℕ) [Fact p.Prime]
    (hn : 0<n) (hnp : n<p) :
    (1/(n : RatFunc ℚ)) ∈ integralRationalEscape (integralSubring p) := by
  simpa only [map_div₀, map_one, map_natCast] using
    integral_rational_escape_scalar (integralSubring p) (1/(n : ℚ))
      (small_inverse_integral p n hn hnp)

/-- Translation of the original coefficient variable preserves integral coefficients. -/
theorem actual_escape_symbol_integral (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    symbol ∈ integralRationalEscape (integralSubring p) := by
  let R := integralSubring p
  have h3 : (1/3 : ℚ)∈R := small_inverse_integral p 3 (by norm_num) (by omega)
  have h11 : (1/11 : ℚ)∈R := small_inverse_integral p 11 (by norm_num) (by omega)
  have hc : escapePoint∈R := by
    rw [show escapePoint=50*(1/3)^2*(1/11) by norm_num [escapePoint]]
    exact R.mul_mem (R.mul_mem (natCast_mem R 50) (R.pow_mem h3 2)) h11
  change rationalTranslationHom escapePoint symbol ∈ integralRationalOrigin R
  rw [rational_translation_symbol]
  exact (integralRationalOrigin R).add_mem (integral_rational_origin_symbol R)
    (integral_rational_origin_scalar R _ hc)

/-- The original factor x is a unit in the Laurent expansion at x=50/99. -/
theorem actual_escape_symbol_inverse_integral (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    symbol⁻¹ ∈ integralRationalEscape (integralSubring p) := by
  let R := integralSubring p
  have h2 : (1/2 : ℚ)∈R := small_inverse_integral p 2 (by norm_num) (by omega)
  have h5 : (1/5 : ℚ)∈R := small_inverse_integral p 5 (by norm_num) (by omega)
  have hc : (-escapePoint)⁻¹∈R := by
    rw [show (-escapePoint)⁻¹= -99*(1/2)*(1/5)^2 by norm_num [escapePoint]]
    exact R.mul_mem (R.mul_mem (R.neg_mem (natCast_mem R 99)) h2) (R.pow_mem h5 2)
  change rationalTranslationHom escapePoint symbol⁻¹ ∈ integralRationalOrigin R
  rw [map_inv₀, rational_translation_symbol]
  have he : symbol+RatFunc.C escapePoint = symbol-RatFunc.C (-escapePoint) := by
    rw [map_neg]
    ring
  rw [he]
  exact integral_rational_origin_finite_pole R _ (by norm_num [escapePoint]) hc

/-- The other affine denominator stays a unit at the original escape point. -/
theorem actual_escape_M_inverse_integral (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (9*symbol-25)⁻¹ ∈ integralRationalEscape (integralSubring p) := by
  let R := integralSubring p
  have h3 : (1/3 : ℚ)∈R := small_inverse_integral p 3 (by norm_num) (by omega)
  have h5 : (1/5 : ℚ)∈R := small_inverse_integral p 5 (by norm_num) (by omega)
  have h9 : (9 : ℚ)⁻¹∈R := by
    rw [show (9 : ℚ)⁻¹=(1/3)^2 by norm_num]
    exact R.pow_mem h3 2
  have hr : (9/(225/11) : ℚ)∈R := by
    rw [show (9/(225/11) : ℚ)=11*(1/5)^2 by norm_num]
    exact R.mul_mem (natCast_mem R 11) (R.pow_mem h5 2)
  change rationalTranslationHom escapePoint ((9*symbol-25)⁻¹) ∈ integralRationalOrigin R
  rw [map_inv₀, map_sub, map_mul, _root_.map_ofNat, _root_.map_ofNat,
    rational_translation_symbol]
  have he : 9*(symbol+RatFunc.C escapePoint)-25 =
      RatFunc.C 9*symbol-RatFunc.C (225/11 : ℚ) := by
    norm_num [escapePoint, map_div₀]
    ring
  rw [he]
  exact integral_rational_origin_affine_inverse R 9 (225/11) (by norm_num)
    (by norm_num) h9 hr

/-- The collision denominator becomes precisely 99 times the local parameter. -/
theorem actual_escape_e_inverse_integral (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (99*symbol-50)⁻¹ ∈ integralRationalEscape (integralSubring p) := by
  let R := integralSubring p
  have h3 : (1/3 : ℚ)∈R := small_inverse_integral p 3 (by norm_num) (by omega)
  have h11 : (1/11 : ℚ)∈R := small_inverse_integral p 11 (by norm_num) (by omega)
  have h99 : (1/99 : ℚ)∈R := by
    rw [show (1/99 : ℚ)=(1/3)^2*(1/11) by norm_num]
    exact R.mul_mem (R.pow_mem h3 2) h11
  change rationalTranslationHom escapePoint ((99*symbol-50)⁻¹) ∈ integralRationalOrigin R
  rw [map_inv₀, map_sub, map_mul, _root_.map_ofNat, _root_.map_ofNat,
    rational_translation_symbol]
  have he : (99*(symbol+RatFunc.C escapePoint)-50)⁻¹ =
      RatFunc.C (1/99 : ℚ)*symbol⁻¹ := by
    have he0 : 99*(symbol+RatFunc.C escapePoint)-50 = 99*symbol := by
      norm_num [escapePoint, map_div₀]
      ring
    rw [he0, mul_inv_rev]
    norm_num [map_div₀]
    all_goals ring
  rw [he]
  exact (integralRationalOrigin R).mul_mem (integral_rational_origin_scalar R _ h99)
    (integral_rational_origin_symbol_inverse R)

theorem eta_coefficient_denominator_inverse_escape_integral (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) (i j : Fin 3) :
    (etaCoefficientDenominator i j)⁻¹ ∈ integralRationalEscape (integralSubring p) := by
  let I := integralRationalEscape (integralSubring p)
  have hd : RatFunc.C ((etaFixedDenominator i j : ℚ)⁻¹) ∈ I :=
    integral_rational_escape_scalar _ _
      (by simpa only [one_div] using eta_fixed_scalar_inverse_integral p hp i j)
  have hf : (etaCoefficientDenominator i j)⁻¹ =
      RatFunc.C ((etaFixedDenominator i j : ℚ)⁻¹) *
        (symbol⁻¹)^(etaCoefficientXOrder i j) *
        ((9*symbol-25)⁻¹)^(etaCoefficientCollisionOrder i j)*((99*symbol-50)⁻¹)^3 := by
    rw [eta_coefficient_denominator_factorization]
    simp only [mul_inv_rev, ← inv_pow, ← map_inv₀]
    ring
  rw [hf]
  exact I.mul_mem (I.mul_mem (I.mul_mem hd
    (I.pow_mem (actual_escape_symbol_inverse_integral p hp) _))
    (I.pow_mem (actual_escape_M_inverse_integral p hp) _))
    (I.pow_mem (actual_escape_e_inverse_integral p hp) 3)

theorem eta_cleared_polynomial_escape_integral (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) (i j : Fin 3) :
    etaClearedPolynomial i j ∈ polynomialCoefficientSubring (integralRationalEscape (integralSubring p)) := by
  let I := integralRationalEscape (integralSubring p)
  let P := polynomialCoefficientSubring I
  exact P.mul_mem (P.mul_mem
    (C_mem_polynomialCoefficientSubring I _ (eta_coefficient_denominator_inverse_escape_integral p hp i j))
    (P.pow_mem (X_mem_polynomialCoefficientSubring I) _))
    (eta_numerator_polynomial_integral_of_symbol I (actual_escape_symbol_integral p hp) i j)

theorem actual_lambda_escape_integral (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    lambda ∈ integralRationalEscape (integralSubring p) := by
  let R := integralSubring p
  let I := integralRationalEscape R
  have h5 : (1/5 : ℚ) ∈ R := small_inverse_integral p 5 (by norm_num) (by omega)
  have ht : (729/15625 : ℚ)∈R := by
    rw [show (729/15625 : ℚ)=729*(1/5)^6 by norm_num]
    exact R.mul_mem (natCast_mem R 729) (R.pow_mem h5 6)
  have hs : (729/15625 : RatFunc ℚ)=RatFunc.C (729/15625 : ℚ) := by norm_num [map_div₀]
  unfold lambda
  rw [hs]
  exact I.mul_mem (integral_rational_escape_scalar R _ ht)
    (I.pow_mem (actual_escape_symbol_integral p hp) 3)

theorem actual_lambda_inverse_escape_integral (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    lambda⁻¹ ∈ integralRationalEscape (integralSubring p) := by
  let R := integralSubring p
  let I := integralRationalEscape R
  have h3 : (1/3 : ℚ)∈R := small_inverse_integral p 3 (by norm_num) (by omega)
  have ht : (15625/729 : ℚ)∈R := by
    rw [show (15625/729 : ℚ)=15625*(1/3)^6 by norm_num]
    exact R.mul_mem (natCast_mem R 15625) (R.pow_mem h3 6)
  have hs : (729/15625 : RatFunc ℚ)⁻¹=RatFunc.C (15625/729 : ℚ) := by norm_num [map_div₀]
  unfold lambda
  rw [mul_inv_rev, ← inv_pow, hs]
  exact I.mul_mem (I.pow_mem (actual_escape_symbol_inverse_integral p hp) 3)
    (integral_rational_escape_scalar R _ ht)

end

end WPLiteralAdapter
