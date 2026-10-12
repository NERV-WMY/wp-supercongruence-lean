import WPActualIntegratedSource

open scoped LaurentSeries
open HahnSeries Polynomial

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 1000000

/-- The literal formal Laurent expansion at x zero of the actual reduced rational function. -/
noncomputable def actualRationalSeries (f : RatFunc ℚ) : LaurentSeries ℚ :=
  algebraMap (RatFunc ℚ) (LaurentSeries ℚ) f

noncomputable def actualRationalCoefficient (f : RatFunc ℚ) (n : ℤ) : ℚ :=
  (actualRationalSeries f).coeff n

theorem actual_rational_coefficient_sum {ι : Type*} (s : Finset ι)
    (f : ι → RatFunc ℚ) (n : ℤ) :
    actualRationalCoefficient (∑ i ∈ s, f i) n =
      ∑ i ∈ s, actualRationalCoefficient (f i) n := by
  simp only [actualRationalCoefficient, actualRationalSeries, map_sum, HahnSeries.coeff_sum]

@[simp] theorem actual_rational_coefficient_neg (f : RatFunc ℚ) (n : ℤ) :
    actualRationalCoefficient (-f) n = -actualRationalCoefficient f n := by
  simp only [actualRationalCoefficient, actualRationalSeries, map_neg, HahnSeries.coeff_neg]

theorem actual_rational_derivative_series (f : RatFunc ℚ) :
    actualRationalSeries (rationalDerivative f) = laurentS (actualRationalSeries f) := by
  change algebraMap (RatFunc ℚ) (LaurentSeries ℚ)
      (rationalLift (Polynomial.derivative'.restrictScalars ℤ) f) =
    laurentSDerivation (algebraMap (RatFunc ℚ) (LaurentSeries ℚ) f)
  exact rationalLift_laurent_embedding (Polynomial.derivative'.restrictScalars ℤ)
    laurentSDerivation laurentS_polynomial f

@[simp] theorem actual_rational_coefficient_add (f g : RatFunc ℚ) (n : ℤ) :
    actualRationalCoefficient (f+g) n =
      actualRationalCoefficient f n+actualRationalCoefficient g n := by
  simp only [actualRationalCoefficient, actualRationalSeries, map_add, HahnSeries.coeff_add]

@[simp] theorem actual_rational_coefficient_sub (f g : RatFunc ℚ) (n : ℤ) :
    actualRationalCoefficient (f-g) n =
      actualRationalCoefficient f n-actualRationalCoefficient g n := by
  simp only [actualRationalCoefficient, actualRationalSeries, map_sub, HahnSeries.coeff_sub]

theorem actual_rational_coefficient_scalar (q : ℚ) (f : RatFunc ℚ) (n : ℤ) :
    actualRationalCoefficient (RatFunc.C q*f) n = q*actualRationalCoefficient f n := by
  simp only [actualRationalCoefficient, actualRationalSeries, map_mul,
    rational_laurent_coefficient, HahnSeries.C_apply, HahnSeries.coeff_single_mul, sub_zero]

theorem actual_rational_coefficient_symbol (f : RatFunc ℚ) (n : ℤ) :
    actualRationalCoefficient (symbol*f) n = actualRationalCoefficient f (n-1) := by
  simp only [actualRationalCoefficient, actualRationalSeries, map_mul,
    symbol, RatFunc.algebraMap_X, RatFunc.coe_X, HahnSeries.coeff_single_mul,
    one_mul]

theorem actual_rational_derivative_coefficient (f : RatFunc ℚ) (n : ℤ) :
    actualRationalCoefficient (rationalDerivative f) n =
      ((n+1 : ℤ) : ℚ)*actualRationalCoefficient f (n+1) := by
  rw [actualRationalCoefficient, actual_rational_derivative_series, laurentS_coeff]
  rfl

theorem actual_beta_coefficient (f : RatFunc ℚ) (n : ℤ) :
    actualRationalCoefficient ((1-symbol)*rationalDerivative f-f/2) n =
      ((n+1 : ℤ) : ℚ)*actualRationalCoefficient f (n+1)-
        ((n : ℚ)+1/2)*actualRationalCoefficient f n := by
  have hdiv : f/2 = RatFunc.C (1/2)*f := by
    norm_num [map_div₀]
    ring
  have hx : (1-symbol)*rationalDerivative f =
      rationalDerivative f-symbol*rationalDerivative f := by ring
  rw [hx, hdiv, actual_rational_coefficient_sub, actual_rational_coefficient_sub,
    actual_rational_coefficient_scalar, actual_rational_coefficient_symbol,
    actual_rational_derivative_coefficient, actual_rational_derivative_coefficient]
  rw [show n-1+1=n by omega]
  push_cast
  ring

/-- All integer Laurent coefficients of the full actual scalar source equation. -/
theorem actual_full_source_coefficient (p : ℕ) (hp : 0<p) (n : ℤ) :
    ((2*n+1 : ℤ) : ℚ)*actualRationalCoefficient (nativeWeightedG p) n =
      6750*(((n+1 : ℤ) : ℚ)*actualRationalCoefficient (actualTotalPrimitive p) (n+1)-
        ((n : ℚ)+1/2)*actualRationalCoefficient (actualTotalPrimitive p) n) +
      3375*actualRationalCoefficient (actualTotalSource p) n +
      actualRationalCoefficient (nativeSquareForcing p) n := by
  have h := congrArg (fun f => actualRationalCoefficient f n) (actual_full_forced_scalar p hp)
  have h6750 : (6750 : RatFunc ℚ) = RatFunc.C (6750 : ℚ) := by norm_num
  have h3375 : (3375 : RatFunc ℚ) = RatFunc.C (3375 : ℚ) := by norm_num
  have hleft : 2*symbol*rationalDerivative (nativeWeightedG p) =
      RatFunc.C 2*(symbol*rationalDerivative (nativeWeightedG p)) := by
    norm_num
    ring
  rw [hleft, h6750, h3375] at h
  simp only [actual_rational_coefficient_add,
    actual_rational_coefficient_scalar, actual_rational_coefficient_symbol,
    actual_rational_derivative_coefficient, actual_beta_coefficient] at h
  rw [show n-1+1=n by omega] at h
  push_cast at h ⊢
  linear_combination h

theorem actual_full_source_constant (p : ℕ) (hp : 0<p) :
    actualRationalCoefficient (nativeWeightedG p) 0 =
      6750*(actualRationalCoefficient (actualTotalPrimitive p) 1-
        actualRationalCoefficient (actualTotalPrimitive p) 0/2) +
      3375*actualRationalCoefficient (actualTotalSource p) 0 +
      actualRationalCoefficient (nativeSquareForcing p) 0 := by
  have h := actual_full_source_coefficient p hp 0
  norm_num at h
  linear_combination h

end

end WPForcedSourceStokes
