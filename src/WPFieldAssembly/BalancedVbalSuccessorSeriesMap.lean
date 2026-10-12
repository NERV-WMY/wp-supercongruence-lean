import WPFieldAssembly.ActualBpairLowHLocalPole

open scoped LaurentPolynomial LaurentSeries
open LaurentPolynomial HahnSeries

namespace WPFieldAssembly.BalancedVbalSuccessorSeriesMap

open ActualBpairLowHLocalPole WPActualChiSource
variable {K L : Type*} [Field K] [Field L]

/-- The coefficient map retains every signed exponent of the full series. -/
noncomputable def seriesCoefficientHom (f : K →+* L) :
    LaurentSeries K →+* LaurentSeries L where
  toFun Q := Q.map f
  map_zero' := by ext j; simp
  map_one' := by
    ext j
    by_cases hj : j=0 <;> simp [HahnSeries.map_coeff,hj]
  map_add' Q R := by
    ext j
    simp only [HahnSeries.map_coeff,HahnSeries.coeff_add,map_add]
  map_mul' Q R := HahnSeries.map_mul f.toNonUnitalRingHom

theorem seriesCoefficientHom_coeff (f : K →+* L) (Q : LaurentSeries K) (j : ℤ) :
    (seriesCoefficientHom f Q).coeff j=f (Q.coeff j) := rfl

/-- The literal finite embedding commutes with the full series coefficient map. -/
theorem localFiniteSeriesHom_natural (f : K →+* L) (F : K[T;T⁻¹]) :
    seriesCoefficientHom f (localFiniteSeriesHom F)=
      localFiniteSeriesHom (coefficientMap f F) := by
  ext j
  simp only [seriesCoefficientHom_coeff,localFiniteSeries_coeff,coefficientMap_coeff]

end WPFieldAssembly.BalancedVbalSuccessorSeriesMap
