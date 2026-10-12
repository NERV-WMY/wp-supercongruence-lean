import WPFieldAssembly.ActualBpairLowHSourcePullback
import WPFieldAssembly.ActualBpairLowHLocalPole

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1400000

theorem lowHFiniteSeries_one : lowHFiniteSeries (1 : K[T;T⁻¹]) = 1 := by
  rw [show (1 : K[T;T⁻¹]) = LaurentPolynomial.C (1 : K) * T 0 by simp,
    lowHFiniteSeries_monomial]
  rfl

/-- The existing full coefficient embedding is made multiplicative without truncation. -/
noncomputable def lowHFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K where
  toFun := lowHFiniteSeries
  map_zero' := map_zero _
  map_one' := lowHFiniteSeries_one
  map_add' := map_add _
  map_mul' := lowHFiniteSeries_mul

theorem lowHFiniteSeries_C (c : K) :
    lowHFiniteSeriesHom (LaurentPolynomial.C c) = algebraMap K (LaurentSeries K) c := by
  change lowHFiniteSeries (LaurentPolynomial.C c) = _
  rw [show LaurentPolynomial.C c = LaurentPolynomial.C c * T 0 by simp,
    lowHFiniteSeries_monomial]
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply]

theorem lowHFiniteSeries_T (n : ℤ) :
    lowHFiniteSeriesHom (T n : K[T;T⁻¹]) = HahnSeries.single n (1 : K) := by
  change lowHFiniteSeries (T n : K[T;T⁻¹]) = _
  simpa only [map_one, one_mul] using lowHFiniteSeries_monomial (1 : K) n

/-- The original Abar quotient has the same full coefficient functional in the canonical embedding. -/
theorem lowHFiniteSeries_Abar_quotient_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (F : K[T;T⁻¹]) :
    (lowHFiniteSeriesHom F /
      lowHFiniteSeriesHom ((WPFiniteZSource.Abar : K[X]).toLaurent)).coeff (-1) =
        WPFieldAssembly.ActualSimplePoleResidue.originPole F := by
  exact WPFieldAssembly.ActualBpairLowHLocalPole.local_Abar_quotient_residue p hp F

theorem lowH_powerSeries_polynomial_field_eval (t : PowerSeries K) (P : K[X]) :
    ((Polynomial.aeval t P : PowerSeries K) : LaurentSeries K) =
      Polynomial.aeval (t : LaurentSeries K) P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow,
      Polynomial.aeval_C, Polynomial.aeval_X, PowerSeries.algebraMap_eq,
      HahnSeries.ofPowerSeries_C,
      LaurentSeries.algebraMap_apply]

theorem lowHFiniteSeries_polynomial (P : K[X]) :
    lowHFiniteSeriesHom P.toLaurent = algebraMap K[X] (LaurentSeries K) P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, lowH_series_polynomial_monomial]
    simp only [map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]
    rw [← map_mul]
    change lowHFiniteSeries (LaurentPolynomial.C c * T (n : ℤ)) = _
    exact lowHFiniteSeries_monomial c n

/-- Every coefficient of an original polynomial is evaluated at the squared coordinate. -/
theorem lowHFiniteSeries_square_polynomial (P : K[X]) :
    lowHFiniteSeriesHom (lowHSquareSource P.toLaurent) =
      Polynomial.aeval ((((PowerSeries.X : PowerSeries K) : LaurentSeries K) ^ 2)) P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial n c =>
    rw [Polynomial.toLaurent_C_mul_T, lowHSquareSource_monomial, map_mul,
      lowHFiniteSeries_C, lowHFiniteSeries_T, Polynomial.aeval_def, Polynomial.eval₂_monomial]
    congr 1
    rw [PowerSeries.coe_X, HahnSeries.single_pow, HahnSeries.single_pow]
    simp only [one_pow, nsmul_eq_mul, mul_one]
    congr 1
    ring

theorem lowH_Dsym_square_series_Abar :
    lowHFiniteSeriesHom (lowHSquareSource ((WPFiniteZSource.Abar : K[X]).toLaurent)) =
      (4 - (HahnSeries.single 1 (1 : K) : LaurentSeries K) ^ 2) *
        (4 * (HahnSeries.single 1 (1 : K) : LaurentSeries K) ^ 2 - 1) := by
  have hx : (HahnSeries.single 1 (1 : K) : LaurentSeries K) ^ 2 = HahnSeries.single 2 (1 : K) := by
    rw [HahnSeries.single_pow]
    simp
  simp only [WPFiniteZSource.Abar, map_mul, map_sub, map_ofNat, map_one,
    Polynomial.toLaurent_X, lowHSquareSource_T, lowHFiniteSeries_T, hx]
  rfl

theorem lowH_Dsym_square_series_squaredCoordinate :
    lowHFiniteSeriesHom (lowHSquareSource ((WPFiniteWSource.squaredCoordinate : K[X]).toLaurent)) =
      algebraMap K (LaurentSeries K) (1 / 5 : K) *
        ((HahnSeries.single 1 (1 : K) : LaurentSeries K) ^ 2 + 1) := by
  have hx : (HahnSeries.single 1 (1 : K) : LaurentSeries K) ^ 2 = HahnSeries.single 2 (1 : K) := by
    rw [HahnSeries.single_pow]
    simp
  simp only [WPFiniteWSource.squaredCoordinate, map_mul, map_add, map_one,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X, lowHSquareSource_C,
    lowHSquareSource_T, lowHFiniteSeries_C, lowHFiniteSeries_T, hx, one_div]
  rfl

/-- All signed bands of the original cleared derivative enter the same whole series. -/
theorem lowH_Dsym_square_series_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    lowHFiniteSeriesHom (lowHSquareSource ((WPFiniteZSource.Abar : K[X]).toLaurent)) *
      LaurentSeries.derivative K (lowHFiniteSeriesHom (lowHSquareSource (Dsym p))) =
        algebraMap K (LaurentSeries K) (5 : K) * HahnSeries.single 1 (1 : K) *
          lowHFiniteSeriesHom (lowHSquareSource WPFiniteWSource.squaredCoordinate.toLaurent) ^ ((p - 1) / 2) *
          (HahnSeries.single (-2 * (((p - 1) / 2 : ℕ) : ℤ)) (1 : K) - 1) := by
  have he := congrArg lowHFiniteSeriesHom (lowH_Dsym_square_cleared_source (K := K) p hp)
  simp only [map_mul, map_pow, map_sub, map_one, lowHFiniteSeries_C] at he
  rw [lowHFiniteSeries_T, lowHFiniteSeries_T] at he
  change lowHFiniteSeries _ * lowHFiniteSeries (WPFiniteLaurentDifferential.D _) = _ at he
  rw [lowHFiniteSeries_derivative] at he
  exact he

/-- The literal density and its tame factor are preserved by the full series embedding. -/
theorem lowHSquareSource_series_residue (A : K[T;T⁻¹]) :
    (lowHFiniteSeriesHom (LaurentPolynomial.C (2 : K) * T 1 * lowHSquareSource A)).coeff (-1) =
      2 * A.coeff (-1) := by
  change (lowHFiniteSeries _).coeff (-1) = _
  rw [lowHFiniteSeries_coeff, lowHSquareSource_residue]

end WPFieldAssembly.ActualBpairContraction
