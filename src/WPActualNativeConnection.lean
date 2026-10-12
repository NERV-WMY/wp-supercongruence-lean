import WPFullNativeSixState
import WPRationalDifferential

open Polynomial

namespace WPForcedSourceStokes

/-- The rational coefficient version of the literal s10 cyclic matrix. -/
def cyclicCoefficientMatrix : Fin 6 → Fin 6 → ℚ :=
  ![![49456/125, 153648/125, 113472/125, 72/5, -3312/25, 113472/125],
    ![-1576/25, -4608/25, -3312/25, 0, 72/5, -3312/25],
    ![46/5, 108/5, 72/5, 0, 0, 72/5],
    ![-1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0]]

theorem cyclicCoefficientMatrix_literal (i j : Fin 6) :
    RatFunc.C (cyclicCoefficientMatrix i j) = cyclicMatrix i j := by
  fin_cases i <;> fin_cases j <;> norm_num [cyclicCoefficientMatrix, cyclicMatrix,
    map_ratCast]

private theorem actualSixState_coeff (p : ℕ) (i : Fin 6) (n : ℕ) :
    (actualSixState p i).coeff n =
      ![-(n : ℚ)^3, -(n : ℚ)^4, -(n : ℚ)^5,
        (n : ℚ)^3 + 3*(n : ℚ)^2/2 + 23*(n : ℚ)/36 + 5/72,
        (n : ℚ)*((n : ℚ)^3 + 3*(n : ℚ)^2/2 + 23*(n : ℚ)/36 + 5/72),
        (n : ℚ)^2*((n : ℚ)^3 + 3*(n : ℚ)^2/2 + 23*(n : ℚ)/36 + 5/72)] i *
        (squaredNativePolynomial p).coeff n := by
  fin_cases i <;> simp [actualSixState, thirdNativeShift, thetaPower_coeff,
    WPReview.nativeTheta_coeff, coeff_C_mul] <;> ring

/-- C*Y_H is the actual six Euler derivatives of the full squared native polynomial. -/
theorem actual_native_cyclic_state (p : ℕ) (j : Fin 6) :
    (∑ i : Fin 6, C (cyclicCoefficientMatrix j i) * actualSixState p i) =
      thetaPower j (squaredNativePolynomial p) := by
  ext n
  simp only [finsetSum_coeff, coeff_C_mul, actualSixState_coeff, thetaPower_coeff]
  fin_cases j <;> simp [cyclicCoefficientMatrix, Fin.sum_univ_succ] <;> ring

@[simp] theorem pullbackValue_monomial (p : ℕ) (a : ℚ) :
    pullbackValue (monomial p a) = RatFunc.C a * lambda^p := by
  change pullbackHom (monomial p a) = _
  rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
  simp

noncomputable def nativeStateValue (p : ℕ) (i : Fin 6) : RatFunc ℚ :=
  pullbackValue (actualSixState p i)

theorem pulled_native_connection (p : ℕ) (hp : 0 < p) (i : Fin 6) :
    (lambda-1) * pullbackValue (WPReview.nativeTheta (actualSixState p i)) =
      pullbackValue (nativeConnectionNumerator (actualSixState p) i) +
        RatFunc.C (WPReview.nativeEndpoint p^2 * nativeForcingVector i) * lambda^p := by
  have h := congrArg pullbackHom (native_six_state_connection p hp i)
  simpa only [map_add, map_mul, map_sub, map_one, pullbackHom_apply,
    pullbackValue_X, pullbackValue_monomial] using h

@[simp] theorem pullbackValue_add (P Q : ℚ[X]) :
    pullbackValue (P+Q) = pullbackValue P + pullbackValue Q := map_add pullbackHom _ _

@[simp] theorem pullbackValue_sub (P Q : ℚ[X]) :
    pullbackValue (P-Q) = pullbackValue P - pullbackValue Q := map_sub pullbackHom _ _

@[simp] theorem pullbackValue_mul (P Q : ℚ[X]) :
    pullbackValue (P*Q) = pullbackValue P * pullbackValue Q := map_mul pullbackHom _ _

@[simp] theorem pullbackValue_one : pullbackValue 1 = 1 := map_one pullbackHom

private theorem literal_lambda_ne_one : lambda-1 ≠ 0 := by
  have hP : (C (729/15625) * X^3 - 1 : ℚ[X]) ≠ 0 := by
    intro h
    have h0 := congrArg (fun P : ℚ[X] => P.coeff 0) h
    norm_num at h0
  have h := RatFunc.algebraMap_ne_zero hP
  simpa [lambda, symbol] using h

theorem nativeConnectionNumerator_pullback (p : ℕ) (i : Fin 6) :
    pullbackValue (nativeConnectionNumerator (actualSixState p) i) =
      (lambda-1) * ∑ j : Fin 6, sixConnection i j * nativeStateValue p j := by
  fin_cases i <;> simp [nativeConnectionNumerator, sixConnection,
    Fin.sum_univ_succ, nativeStateValue]
  all_goals field_simp [literal_lambda_ne_one]
  all_goals ring

/-- The actual cubic native state retains the inhomogeneous A_p squared term. -/
theorem actual_native_rational_connection (p : ℕ) (hp : 0 < p) (i : Fin 6) :
    rationalDerivative (nativeStateValue p i) =
      (3/symbol) * (∑ j : Fin 6, sixConnection i j * nativeStateValue p j) -
        3 * RatFunc.C (WPReview.nativeEndpoint p^2 * nativeForcingVector i) *
          lambda^p / (symbol*(1-lambda)) := by
  have hx : symbol ≠ 0 := RatFunc.algebraMap_ne_zero X_ne_zero
  have hl : 1-lambda ≠ 0 := by
    intro h
    apply literal_lambda_ne_one
    linear_combination -h
  rw [nativeStateValue, rationalDerivative_cubic_pullback]
  have h := pulled_native_connection p hp i
  rw [nativeConnectionNumerator_pullback] at h
  field_simp [hx, hl]
  linear_combination -h

/-- The outer polynomial row kills the actual square forcing vector. -/
theorem weighted_forcing_zero :
    (∑ i : Fin 6, weightedRow i * RatFunc.C (nativeForcingVector i)) = 0 := by
  have hw : weightedRow (2 : Fin 6) = weightedRow 5 := by rfl
  simp [Fin.sum_univ_succ, nativeForcingVector, hw]

theorem weighted_connection (j : Fin 6) :
    (∑ i : Fin 6, weightedRow i * sixConnection i j) = nextWeightedRow j := by
  fin_cases j <;> simp [Fin.sum_univ_succ, weightedRow, nextWeightedRow,
    cyclicMatrix, sixConnection]
  all_goals field_simp [literal_lambda_ne_one]
  all_goals ring

def weightedCoefficient (i : Fin 6) : ℚ :=
  9 * cyclicCoefficientMatrix 0 i + 126 * cyclicCoefficientMatrix 1 i +
    532 * cyclicCoefficientMatrix 2 i

theorem weighted_coefficient_literal (i : Fin 6) :
    RatFunc.C (weightedCoefficient i) = weightedRow i := by
  simp only [weightedCoefficient, weightedRow, map_add, map_mul, _root_.map_ofNat,
    cyclicCoefficientMatrix_literal]

@[simp] theorem rationalDerivative_weightedRow (i : Fin 6) :
    rationalDerivative (weightedRow i) = 0 := by
  rw [← weighted_coefficient_literal]
  exact rationalDerivative_constant _

noncomputable def nativeWeightedG (p : ℕ) : RatFunc ℚ :=
  ∑ i : Fin 6, weightedRow i * nativeStateValue p i

theorem actual_native_outer_derivative (p : ℕ) (hp : 0 < p) :
    rationalDerivative (nativeWeightedG p) =
      (3/symbol) * ∑ j : Fin 6, nextWeightedRow j * nativeStateValue p j := by
  rw [nativeWeightedG, rationalDerivative_sum]
  simp_rw [rationalDerivative_mul, rationalDerivative_weightedRow, zero_mul, zero_add,
    actual_native_rational_connection p hp]
  simp_rw [← weighted_connection]
  have hf := weighted_forcing_zero
  simp only [Fin.sum_univ_succ, map_mul] at hf ⊢
  linear_combination -3 * RatFunc.C (WPReview.nativeEndpoint p^2) * lambda^p /
    (symbol*(1-lambda)) * hf

noncomputable def nativePrimitive (p : ℕ) : RatFunc ℚ :=
  ∑ i : Fin 6, primitiveEntry i * nativeStateValue p i

noncomputable def nativeSourceValue (p : ℕ) : RatFunc ℚ :=
  ∑ i : Fin 6, sourceEntry i * nativeStateValue p i

noncomputable def nativeSquareForcing (p : ℕ) : RatFunc ℚ :=
  20250 * RatFunc.C (WPReview.nativeEndpoint p^2) * lambda^p * (1-symbol) /
    (symbol*(1-lambda)) *
      ∑ i : Fin 6, primitiveEntry i * RatFunc.C (nativeForcingVector i)

/-- The fixed outer primitive acts on the actual finite state and retains the printed square forcing. -/
theorem actual_native_primitive_forcing (p : ℕ) (hp : 0 < p) :
    2*symbol*rationalDerivative (nativeWeightedG p) + nativeWeightedG p =
      6750*((1-symbol)*rationalDerivative (nativePrimitive p) - nativePrimitive p/2) +
        3375*nativeSourceValue p + nativeSquareForcing p := by
  have hx : symbol ≠ 0 := RatFunc.algebraMap_ne_zero X_ne_zero
  have hl : 1-lambda ≠ 0 := by
    intro h
    apply literal_lambda_ne_one
    linear_combination -h
  have hrow :
      (∑ i : Fin 6, (weightedRow i + 6*nextWeightedRow i)*nativeStateValue p i) =
      ∑ i : Fin 6, (3375*sourceEntry i +
        6750*((1-symbol)*rationalDerivative (primitiveEntry i) +
          (3*(1-symbol)/symbol)*(∑ j : Fin 6, primitiveEntry j*sixConnection j i) -
            primitiveEntry i/2))*nativeStateValue p i := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [outer_row_identity]
  rw [actual_native_outer_derivative p hp]
  unfold nativeWeightedG nativePrimitive nativeSourceValue nativeSquareForcing
  rw [rationalDerivative_sum]
  simp_rw [rationalDerivative_mul, actual_native_rational_connection p hp]
  simp only [Fin.sum_univ_succ, map_mul] at hrow ⊢
  field_simp [hx] at hrow
  field_simp [hx, hl]
  linear_combination (1-lambda)*hrow

theorem native_weighted_polynomial (p : ℕ) :
    (∑ i : Fin 6, C (weightedCoefficient i)*actualSixState p i) =
      9*squaredNativePolynomial p + 126*thetaPower 1 (squaredNativePolynomial p) +
        532*thetaPower 2 (squaredNativePolynomial p) := by
  simp only [weightedCoefficient, map_add, map_mul, _root_.map_ofNat,
    add_mul, Finset.sum_add_distrib, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    actual_native_cyclic_state p 0, actual_native_cyclic_state p 1,
    actual_native_cyclic_state p 2]
  simp [thetaPower]

/-- The actual weighted G is precisely the literal quadratic operator on H. -/
theorem native_weighted_G_literal (p : ℕ) :
    nativeWeightedG p = pullbackValue
      (9*squaredNativePolynomial p + 126*thetaPower 1 (squaredNativePolynomial p) +
        532*thetaPower 2 (squaredNativePolynomial p)) := by
  have h := congrArg pullbackHom (native_weighted_polynomial p)
  simp only [map_sum, map_mul, pullbackHom_apply, pullbackValue_C,
    weighted_coefficient_literal] at h
  exact h

noncomputable def nativeAngularSource (p : ℕ) : RatFunc ℚ :=
  ∑ i : Fin 6, sourceEntry i * pullbackValue (angularSixState p i)

noncomputable def nativeEndpointCorrection (p : ℕ) : RatFunc ℚ :=
  RatFunc.C (WPReview.nativeEndpoint p) *
    ∑ i : Fin 6, sourceEntry i * pullbackValue (nativeEndpointState p i)

theorem native_source_angular_decomposition (p : ℕ) (hp : 0 < p) :
    nativeSourceValue p = nativeAngularSource p + nativeEndpointCorrection p := by
  have hi (i : Fin 6) : nativeStateValue p i =
      pullbackValue (angularSixState p i) +
        RatFunc.C (WPReview.nativeEndpoint p) * pullbackValue (nativeEndpointState p i) := by
    have h := congrArg pullbackHom (actual_angular_six_state p hp i)
    simp only [map_sub, map_mul, pullbackHom_apply, pullbackValue_C] at h
    unfold nativeStateValue
    linear_combination -h
  unfold nativeSourceValue nativeAngularSource nativeEndpointCorrection
  simp_rw [hi, mul_add]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring

end WPForcedSourceStokes
