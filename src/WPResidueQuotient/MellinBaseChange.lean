import WPResidueQuotient.MellinMatrix
import WPResidueQuotient.ParameterRing

/-!
The rational Mellin coordinates are transported coefficient by coefficient
to an arbitrary characteristic-zero field. The parameter localization maps
injectively into its actual Laurent-series field by sending the polynomial
parameter to the degree-one monomial. No specialization of an infinite series
or abstract base-change assertion is used.
-/

noncomputable section

namespace WPResidueQuotient.MellinFactors

open scoped BigOperators LaurentSeries

variable (K : Type*) [Field K] [CharZero K]

abbrev LSK := LaurentSeries K

/-- The literal coefficientwise image of a rational Laurent series. -/
def rationalSeriesMap : LS →+* LSK K where
  toFun s := s.map (Rat.castHom K)
  map_zero' := HahnSeries.map_zero (Rat.castHom K).toZeroHom
  map_one' := HahnSeries.map_one (Rat.castHom K).toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add (Rat.castHom K).toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul (Rat.castHom K).toNonUnitalRingHom

@[simp] theorem rationalSeriesMap_coeff (s : LS) (d : ℤ) :
    (rationalSeriesMap K s).coeff d = (s.coeff d : K) := rfl

theorem rationalSeriesMap_injective : Function.Injective (rationalSeriesMap K) := by
  intro s t h
  ext d
  apply (Rat.castHom K).injective
  exact congrArg (fun z : LSK K => z.coeff d) h

def uSeries : LSK K := HahnSeries.single 1 1

@[simp] theorem rationalSeriesMap_u : rationalSeriesMap K uMonomial = uSeries K := by
  change (HahnSeries.single (1 : ℤ) (1 : ℚ)).map (Rat.castHom K) =
    HahnSeries.single 1 1
  exact (HahnSeries.map_single (Rat.castHom K).toZeroHom).trans
    (congrArg (HahnSeries.single (1 : ℤ)) (map_one (Rat.castHom K)))

/-- The actual embedding of the localized coefficient ring. -/
def parameterSeriesMap : Parameter.ParameterRing K →+* LSK K :=
  IsLocalization.Away.lift (Parameter.denominatorPolynomial K)
    (g := algebraMap (Polynomial K) (LSK K)) (by
      apply isUnit_iff_ne_zero.mpr
      exact fun h => Parameter.denominatorPolynomial_ne_zero
        (Polynomial.algebraMap_hahnSeries_injective ℤ (h.trans (map_zero _).symm)))

omit [CharZero K] in
@[simp] theorem parameterSeriesMap_polynomial (P : Polynomial K) :
    parameterSeriesMap K
      (algebraMap (Polynomial K) (Parameter.ParameterRing K) P) =
        algebraMap (Polynomial K) (LSK K) P := by
  simp [parameterSeriesMap]

omit [CharZero K] in
@[simp] theorem parameterSeriesMap_u :
    parameterSeriesMap K (Parameter.u : Parameter.ParameterRing K) = uSeries K := by
  rw [Parameter.u, parameterSeriesMap_polynomial]
  change (((Polynomial.X : Polynomial K) : PowerSeries K) : LSK K) = uSeries K
  simp only [Polynomial.coe_X, PowerSeries.coe_X, uSeries]

omit [CharZero K] in
theorem parameterSeriesMap_injective : Function.Injective (parameterSeriesMap K) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (Parameter.denominatorPolynomial K)) (parameterSeriesMap K)).2
  intro P Q
  rw [parameterSeriesMap_polynomial, parameterSeriesMap_polynomial]
  constructor
  · intro h
    exact congrArg (algebraMap (Polynomial K) (LSK K))
      (Parameter.polynomial_embedding_injective h)
  · intro h
    exact congrArg (algebraMap (Polynomial K) (Parameter.ParameterRing K))
      (Polynomial.algebraMap_hahnSeries_injective ℤ h)

def mellinSeriesK (r : Fin 5) (m : ℤ) (a : ExponentVector) : LSK K :=
  rationalSeriesMap K (mellinSeries r m a)

theorem mellinSeriesK_pole_relation (r : Fin 5) (m : ℤ) (a : ExponentVector) :
    mellinSeriesK K r (m + 1) a -
        ∑ i, uSeries K * mellinSeriesK K r (m + 1) (increment a i) =
      (m : LSK K) * mellinSeriesK K r m a := by
  have h := congrArg (rationalSeriesMap K) (mellinSeries_pole_relation r m a)
  rw [Int.cast_smul_eq_zsmul ℚ, zsmul_eq_mul] at h
  simpa only [mellinSeriesK, map_sub, map_sum, map_mul, rationalSeriesMap_u,
    map_intCast] using h

theorem mellinSeriesK_derivative_relation
    (r : Fin 5) (m : ℤ) (a : ExponentVector) (i j : Fin 6) :
    ((a i - a j : ℤ) : LSK K) * mellinSeriesK K r m a +
        uSeries K * mellinSeriesK K r (m + 1) (increment a i) -
        uSeries K * mellinSeriesK K r (m + 1) (increment a j) = 0 := by
  have h := congrArg (rationalSeriesMap K) (mellinSeries_derivative_relation r m a i j)
  rw [← Int.cast_sub, Int.cast_smul_eq_zsmul ℚ, zsmul_eq_mul] at h
  simpa only [mellinSeriesK, map_add, map_sub, map_mul, map_zero,
    rationalSeriesMap_u, map_intCast] using h

theorem mellinSeriesK_subtractDiagonal (r : Fin 5) (m : ℤ)
    (a : ExponentVector) (v : ℕ) (hv : ∀ i, (v : ℤ) ≤ a i) :
    mellinSeriesK K r m a = mellinSeriesK K r m (subtractDiagonal a (v : ℤ)) := by
  unfold mellinSeriesK
  rw [mellinSeries_subtractDiagonal r m a v hv]

def interiorMellinMatrixK : Matrix (Fin 5) (Fin 5) (LSK K) :=
  (rationalSeriesMap K).mapMatrix interiorMellinMatrix

theorem interiorMellinMatrixK_det_ne_zero : (interiorMellinMatrixK K).det ≠ 0 := by
  rw [interiorMellinMatrixK, ← RingHom.map_det]
  exact fun h => interiorMellinMatrix_det_ne_zero
    (rationalSeriesMap_injective K (h.trans (map_zero _).symm))

theorem interiorMellinMatrixK_columns_independent :
    LinearIndependent (LSK K) (fun c : Fin 5 => fun r : Fin 5 =>
      mellinSeriesK K r (c.val + 1 : ℤ) zeroExponent) := by
  change LinearIndependent (LSK K) (interiorMellinMatrixK K).col
  exact Matrix.linearIndependent_cols_of_det_ne_zero (interiorMellinMatrixK_det_ne_zero K)

end WPResidueQuotient.MellinFactors
