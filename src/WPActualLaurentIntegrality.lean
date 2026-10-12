import WPActualIntegratedSource
import WPGeometricResidue
import WPActualSquareForcing

open scoped LaurentSeries
open HahnSeries Polynomial

namespace WPForcedSourceStokes

noncomputable section

/-- Coefficient integrality over any commutative coefficient ring used by the literal adapter. -/
noncomputable def polynomialCoefficientSubring {A : Type*} [CommRing A]
    (R : Subring A) : Subring (Polynomial A) where
  carrier := {P | ∀ k, P.coeff k ∈ R}
  zero_mem' := by intro k; simpa only [Polynomial.coeff_zero] using R.zero_mem
  one_mem' := by
    intro k
    rw [Polynomial.coeff_one]
    split_ifs <;> first | exact R.one_mem | exact R.zero_mem
  add_mem' := by
    intro P Q hP hQ k
    rw [Polynomial.coeff_add]
    exact R.add_mem (hP k) (hQ k)
  neg_mem' := by
    intro P hP k
    rw [Polynomial.coeff_neg]
    exact R.neg_mem (hP k)
  mul_mem' := by
    intro P Q hP hQ k
    rw [Polynomial.coeff_mul]
    exact R.sum_mem (fun ij _ => R.mul_mem (hP ij.1) (hQ ij.2))

theorem mem_polynomialCoefficientSubring {A : Type*} [CommRing A]
    (R : Subring A) (P : Polynomial A) :
    P ∈ polynomialCoefficientSubring R ↔ ∀ k, P.coeff k ∈ R := Iff.rfl

theorem C_mem_polynomialCoefficientSubring {A : Type*} [CommRing A]
    (R : Subring A) (a : A) (ha : a ∈ R) : Polynomial.C a ∈ polynomialCoefficientSubring R := by
  intro k
  rw [Polynomial.coeff_C]
  split_ifs <;> first | exact ha | exact R.zero_mem

theorem X_mem_polynomialCoefficientSubring {A : Type*} [CommRing A]
    (R : Subring A) : Polynomial.X ∈ polynomialCoefficientSubring R := by
  intro k
  rw [Polynomial.coeff_X]
  split_ifs <;> first | exact R.one_mem | exact R.zero_mem

/-- Laurent coefficient integrality is closed under the actual finite convolution. -/
noncomputable def integralLaurentSubring (R : Subring ℚ) : Subring (LaurentSeries ℚ) where
  carrier := {f | ∀ n : ℤ, f.coeff n ∈ R}
  zero_mem' := by intro n; simpa only [HahnSeries.coeff_zero] using R.zero_mem
  one_mem' := by
    intro n
    rw [HahnSeries.coeff_one]
    split_ifs <;> first | exact R.one_mem | exact R.zero_mem
  add_mem' := by
    intro f g hf hg n
    rw [HahnSeries.coeff_add]
    exact R.add_mem (hf n) (hg n)
  neg_mem' := by
    intro f hf n
    rw [HahnSeries.coeff_neg]
    exact R.neg_mem (hf n)
  mul_mem' := by
    intro f g hf hg n
    rw [HahnSeries.coeff_mul]
    exact R.sum_mem (fun ij _ => R.mul_mem (hf ij.1) (hg ij.2))

/-- The original rational functions whose actual Laurent coefficients are integral. -/
noncomputable def integralRationalOrigin (R : Subring ℚ) : Subring (RatFunc ℚ) :=
  (integralLaurentSubring R).comap (algebraMap (RatFunc ℚ) (LaurentSeries ℚ))

theorem integral_rational_origin_iff (R : Subring ℚ) (f : RatFunc ℚ) :
    f ∈ integralRationalOrigin R ↔
      ∀ n : ℤ, (algebraMap (RatFunc ℚ) (LaurentSeries ℚ) f).coeff n ∈ R := Iff.rfl

theorem integral_rational_origin_scalar (R : Subring ℚ) (q : ℚ) (hq : q ∈ R) :
    RatFunc.C q ∈ integralRationalOrigin R := by
  intro n
  rw [rational_laurent_coefficient]
  simp only [HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs <;> first | exact hq | exact R.zero_mem

theorem integral_rational_origin_symbol (R : Subring ℚ) :
    symbol ∈ integralRationalOrigin R := by
  intro n
  simp only [symbol, RatFunc.algebraMap_X, RatFunc.coe_X, HahnSeries.coeff_single]
  split_ifs <;> first | exact R.one_mem | exact R.zero_mem

theorem integral_rational_origin_symbol_inverse (R : Subring ℚ) :
    symbol⁻¹ ∈ integralRationalOrigin R := by
  intro n
  have hs : algebraMap (RatFunc ℚ) (LaurentSeries ℚ) symbol⁻¹ =
      single (-1 : ℤ) (1 : ℚ) := by
    apply mul_left_cancel₀ (single_ne_zero one_ne_zero :
      (single (1 : ℤ) (1 : ℚ) : LaurentSeries ℚ) ≠ 0)
    have hx : symbol ≠ 0 := RatFunc.algebraMap_ne_zero X_ne_zero
    have hm := congrArg (algebraMap (RatFunc ℚ) (LaurentSeries ℚ)) (mul_inv_cancel₀ hx)
    simp only [map_mul, map_one, symbol, RatFunc.algebraMap_X, RatFunc.coe_X] at hm
    simp only [symbol, RatFunc.algebraMap_X]
    rw [hm, single_mul_single]
    norm_num [HahnSeries.single_zero_one]
  rw [hs, HahnSeries.coeff_single]
  split_ifs <;> first | exact R.one_mem | exact R.zero_mem

/-- The literal inverse finite pole has integral Laurent coefficients whenever its inverse does. -/
theorem integral_rational_origin_finite_pole (R : Subring ℚ) (c : ℚ)
    (hc : c≠0) (hi : c⁻¹ ∈ R) :
    (symbol-RatFunc.C c)⁻¹ ∈ integralRationalOrigin R := by
  intro n
  rw [map_inv₀, map_sub, rational_laurent_coefficient]
  simp only [symbol, RatFunc.algebraMap_X, RatFunc.coe_X]
  change (((single (1 : ℤ) (1 : ℚ)-HahnSeries.C c)⁻¹ : LaurentSeries ℚ).coeff n) ∈ R
  rw [geometric_pole_inverse c hc, PowerSeries.coeff_coe]
  split_ifs
  · exact R.zero_mem
  · change PowerSeries.coeff n.natAbs (geometricPoleSeries c) ∈ R
    rw [geometricPoleSeries, neg_mul, map_neg,
      PowerSeries.coeff_C_mul, geometric_power_series_coeff]
    exact R.neg_mem (R.mul_mem hi (R.pow_mem hi _))

/-- The actual two affine denominator factors use only the inverse of their constant term. -/
theorem integral_rational_origin_affine_inverse (R : Subring ℚ) (a b : ℚ)
    (ha : a≠0) (hb : b≠0) (hai : a⁻¹ ∈ R) (habi : a/b ∈ R) :
    (RatFunc.C a*symbol-RatFunc.C b)⁻¹ ∈ integralRationalOrigin R := by
  have hbi : (b/a)⁻¹ ∈ R := by simpa only [inv_div] using habi
  have hca : RatFunc.C a ≠ 0 := by
    simpa only [map_zero] using (RatFunc.C_injective (K := ℚ)).ne ha
  have he : (RatFunc.C a*symbol-RatFunc.C b)⁻¹ =
      RatFunc.C a⁻¹*(symbol-RatFunc.C (b/a))⁻¹ := by
    have hf : RatFunc.C a*symbol-RatFunc.C b =
        RatFunc.C a*(symbol-RatFunc.C (b/a)) := by
      rw [map_div₀]
      field_simp [hca]
    rw [hf, mul_inv_rev, map_inv₀]
    ring
  rw [he]
  exact (integralRationalOrigin R).mul_mem
    (integral_rational_origin_scalar R _ hai)
    (integral_rational_origin_finite_pole R _ (div_ne_zero hb ha) hbi)

end

end WPForcedSourceStokes
