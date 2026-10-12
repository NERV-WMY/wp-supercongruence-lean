import WPFieldAssembly.ActualBpairLowHSourceSeries
import WPFieldAssembly.ActualBpairLowHTameSeries

open scoped LaurentSeries LaurentPolynomial
open LaurentPolynomial

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1200000

/-- The genuine whole-series x=w^2 map acts on every signed coefficient. -/
noncomputable def lowHSeriesSquareHom : LaurentSeries K →+* LaurentSeries K :=
  HahnSeries.embDomainRingHom lowHSquareExponent
    (by intro a b h; change (2 * a : ℤ) = 2 * b at h; omega)
    (by intro a b; change (2 * a : ℤ) ≤ 2 * b ↔ a ≤ b; omega)

theorem lowHSeriesSquareHom_apply (Q : LaurentSeries K) :
    lowHSeriesSquareHom Q = HahnSeries.embDomain lowHSeriesSquareEmbedding Q := rfl

theorem lowHSeriesSquareHom_single (a : K) (n : ℤ) :
    lowHSeriesSquareHom (HahnSeries.single n a) = HahnSeries.single (2 * n) a := by
  rw [lowHSeriesSquareHom_apply, HahnSeries.embDomain_single]
  rfl

/-- The infinite square map agrees with the literal finite-source map on all bands. -/
theorem lowHSeriesSquareHom_finite_source (A : K[T;T⁻¹]) :
    lowHSeriesSquareHom (lowHFiniteSeriesHom A) =
      lowHFiniteSeriesHom (lowHSquareSource A) := by
  induction A using LaurentPolynomial.induction_on' with
  | add A B hA hB => simp only [map_add, hA, hB]
  | C_mul_T n a =>
    change lowHSeriesSquareHom (lowHFiniteSeries (LaurentPolynomial.C a * T n)) =
      lowHFiniteSeries (lowHSquareSource (LaurentPolynomial.C a * T n))
    rw [lowHSquareSource_monomial, lowHFiniteSeries_monomial,
      lowHFiniteSeries_monomial, lowHSeriesSquareHom_single]

/-- The actual quotient is substituted as a whole, retaining both proper-end poles. -/
theorem lowHSeriesSquareHom_finite_quotient (A B : K[T;T⁻¹]) :
    lowHSeriesSquareHom (lowHFiniteSeriesHom A / lowHFiniteSeriesHom B) =
      lowHFiniteSeriesHom (lowHSquareSource A) /
        lowHFiniteSeriesHom (lowHSquareSource B) := by
  rw [map_div₀, lowHSeriesSquareHom_finite_source, lowHSeriesSquareHom_finite_source]

/-- The coefficient identity prints the full ramification-two Jacobian of the quotient. -/
theorem lowHSeriesSquareHom_quotient_residue (A B : K[T;T⁻¹]) :
    (HahnSeries.single 1 (2 : K) *
      (lowHFiniteSeriesHom (lowHSquareSource A) /
        lowHFiniteSeriesHom (lowHSquareSource B))).coeff (-1) =
      2 * (lowHFiniteSeriesHom A / lowHFiniteSeriesHom B).coeff (-1) := by
  rw [← lowHSeriesSquareHom_finite_quotient, lowHSeriesSquareHom_apply]
  exact lowHSeriesSquarePullback_residue _

end WPFieldAssembly.ActualBpairContraction
