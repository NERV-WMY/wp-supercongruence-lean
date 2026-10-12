import WPFieldAssembly.NativeJointSuccessorOddSource
import WPFieldAssembly.NativeJointSuccessorJSeries
import WPFieldAssembly.ActualBpairLowHBranchTail

open scoped BigOperators Polynomial LaurentPolynomial PowerSeries LaurentSeries
open Polynomial LaurentPolynomial HahnSeries

namespace WPFieldAssembly.NativeJointSuccessorOddResidues

open ActualBpairContraction ActualBpairLowHLocalPole ActualSimplePoleResidue
open NativeClosureMixedSource NativeJointSuccessorMixedPrimitive
open NativeJointSuccessorActualPhase NativeJointSuccessorJSeries
open NativeJointSuccessorOddSource ActualCubicNativeSource
open GreenLaurentOperators WPFiniteLaurentDifferential

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/-- The complete odd quotient, with its original branch denominator. -/
noncomputable def actualOddQuotientSeries (p : ℕ) : LaurentSeries K :=
  localFiniteSeriesHom (oddReciprocalS p) /
    localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)

private theorem finite_series_injective :
    Function.Injective (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K) := by
  intro F G he
  ext j
  exact congrArg (fun Q : LaurentSeries K => Q.coeff j) he

private theorem Abar_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent ≠ 0 := by
  intro hz
  apply WPFiniteZSource.Abar_nonzero (K := K) p hp
  exact finite_series_injective (hz.trans (map_zero _).symm)

private theorem squaredCoordinate_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent ≠ 0 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  intro hz
  have hpz : (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent = 0 :=
    finite_series_injective (hz.trans (map_zero _).symm)
  have hp0 : (WPFiniteWSource.squaredCoordinate : K[X]) = 0 :=
    Polynomial.toLaurent_injective (hpz.trans (map_zero _).symm)
  have hc := congrArg (fun P : K[X] => P.coeff 1) hp0
  have he : (WPFiniteWSource.squaredCoordinate : K[X]).coeff 1 = (5 : K)⁻¹ := by
    simp [WPFiniteWSource.squaredCoordinate, Polynomial.coeff_one]
  rw [he, Polynomial.coeff_zero] at hc
  exact inv_ne_zero h5 hc

private theorem linear_w_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (4 - 11 * T 1 : K[T;T⁻¹]) ≠ 0 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  intro hz
  have hc := congrArg (fun Q : LaurentSeries K => Q.coeff 0) hz
  have he : (4 - 11 * T 1 : K[T;T⁻¹]).coeff 0 = (4 : K) := by
    change (LaurentPolynomial.C (4 : K) - LaurentPolynomial.C (11 : K) * T 1).coeff 0 = 4
    rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, LaurentPolynomial.C_apply,
      GreenLaurentOperators.C_mul_coeff, LaurentPolynomial.T_apply]
    simp
  rw [localFiniteSeries_coeff, he, HahnSeries.coeff_zero] at hc
  exact h4 hc

private theorem half_quotient_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (F : K[T;T⁻¹]) :
    localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2 + 1) *
        LaurentSeries.derivative K
          (localFiniteSeriesHom F /
            localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) =
      localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate.toLaurent * D F +
        LaurentPolynomial.C (1 / 10 : K) * F) := by
  let N := (p - 1) / 2
  let s : K[T;T⁻¹] := WPFiniteWSource.squaredCoordinate.toLaurent
  let Q : LaurentSeries K := localFiniteSeriesHom F / localFiniteSeriesHom s ^ N
  have hF : localFiniteSeriesHom (s ^ N) * Q = localFiniteSeriesHom F := by
    dsimp only [Q]
    rw [map_pow]
    rw [mul_comm]
    exact div_mul_cancel₀ _ (pow_ne_zero N (squaredCoordinate_series_ne_zero p hp))
  have he := congrArg (LaurentSeries.derivative K) hF
  rw [finite_series_derivative_product] at he
  have hd : LaurentSeries.derivative K (localFiniteSeriesHom F) =
      localFiniteSeriesHom (D F) := (lowHFiniteSeries_derivative F).symm
  rw [hd] at he
  have hh := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
    (mixedHalfPower_homogeneous (K := K) p hp)
  simp only [map_add, map_mul, map_pow, map_zero] at hh
  change localFiniteSeriesHom s * localFiniteSeriesHom (D (s ^ N)) +
    localFiniteSeriesHom (LaurentPolynomial.C (1 / 10 : K)) * localFiniteSeriesHom s ^ N = 0 at hh
  simp only [map_pow] at he hF
  change localFiniteSeriesHom s ^ (N + 1) * LaurentSeries.derivative K Q = _
  simp only [map_add, map_mul, pow_succ]
  linear_combination localFiniteSeriesHom s * he - Q * hh +
    localFiniteSeriesHom (LaurentPolynomial.C (1 / 10 : K)) * hF

/-- The actual odd derivative uses the reciprocal original A source, with all phases. -/
theorem actual_odd_series_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    LaurentSeries.derivative K (actualOddQuotientSeries p : LaurentSeries K) =
      NativeJointSuccessorJSeries.actualOddSeries p - localFiniteSeriesHom (frobeniusPhi p) *
        (actualLogSeries +
          localFiniteSeriesHom (D (invert (actualAK p : K[X]).toLaurent))) := by
  let N := (p - 1) / 2
  let s : K[T;T⁻¹] := WPFiniteWSource.squaredCoordinate.toLaurent
  let A : K[T;T⁻¹] := (WPFiniteZSource.Abar : K[X]).toLaurent
  let w : K[T;T⁻¹] := 4 - 11 * T 1
  have ho := oddReciprocalS_cleared_source (K := K) p hp
  have hl := actual_odd_log_cleared_source (K := K) p hp
  have he := actual_AQ_cleared_derivative (K := K) p hp
  have hf : A * (s * D (oddReciprocalS p) + LaurentPolynomial.C (1 / 10 : K) *
        oddReciprocalS p) * w =
      oddDensityCleared p * w - s ^ N * frobeniusPhi p * oddLogCleared * A -
        s ^ (N + 1) * frobeniusPhi p * A * D (invert (actualAK p : K[X]).toLaurent) * w := by
    dsimp only [N, s, A, w]
    unfold oddDensityCleared
    rw [show 2 * ((p - 1) / 2) + 1 = ((p - 1) / 2 + 1) + (p - 1) / 2 by omega, pow_add]
    change (WPFiniteZSource.Abar : K[X]).toLaurent * D (invert (actualAK p : K[X]).toLaurent) =
      -LaurentPolynomial.C (3 / 2 : K) *
        (4 * T (-1) - 11 - T (-(((p - 1) / 2 : ℕ) : ℤ)) *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * frobeniusPhi p) at he
    linear_combination (norm := ring_nf) (4 - 11 * T 1) * ho +
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * hl +
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2 + 1) *
        frobeniusPhi p * (4 - 11 * T 1) * he
  have hm := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K) hf
  simp only [map_mul] at hm
  rw [← half_quotient_cleared_derivative p hp (oddReciprocalS p)] at hm
  simp only [map_sub, map_mul, map_pow] at hm
  let S : LaurentSeries K := localFiniteSeriesHom s
  let AS : LaurentSeries K := localFiniteSeriesHom A
  let W : LaurentSeries K := localFiniteSeriesHom w
  have hS : S ≠ 0 := squaredCoordinate_series_ne_zero p hp
  have hA : AS ≠ 0 := Abar_series_ne_zero p hp
  have hW : W ≠ 0 := linear_w_series_ne_zero p hp
  change AS * (S ^ (N + 1) * LaurentSeries.derivative K
      (actualOddQuotientSeries p : LaurentSeries K)) * W =
    localFiniteSeriesHom (oddDensityCleared p) * W -
      S ^ N * localFiniteSeriesHom (frobeniusPhi p) * localFiniteSeriesHom oddLogCleared * AS -
      S ^ (N + 1) * localFiniteSeriesHom (frobeniusPhi p) * AS *
        localFiniteSeriesHom (D (invert (actualAK p : K[X]).toLaurent)) * W at hm
  change LaurentSeries.derivative K (actualOddQuotientSeries p : LaurentSeries K) =
    localFiniteSeriesHom (oddDensityCleared p) / (S ^ (N + 1) * AS) -
      localFiniteSeriesHom (frobeniusPhi p) * (localFiniteSeriesHom oddLogCleared / (S * W) +
        localFiniteSeriesHom (D (invert (actualAK p : K[X]).toLaurent)))
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hA (pow_ne_zero (N + 1) hS)) hW)
  calc
    _ = localFiniteSeriesHom (oddDensityCleared p) * W -
        S ^ N * localFiniteSeriesHom (frobeniusPhi p) * localFiniteSeriesHom oddLogCleared * AS -
        S ^ (N + 1) * localFiniteSeriesHom (frobeniusPhi p) * AS *
          localFiniteSeriesHom (D (invert (actualAK p : K[X]).toLaurent)) * W := by
      linear_combination (norm := ring_nf) hm
    _ = _ := by field_simp [hS, hA, hW]; ring

/-- The original branch cancellation is an exact primitive, with its full Lambda retained. -/
theorem actual_odd_exact_primitive_reduction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (actualOddQuotientSeries p * actualLambdaSeries p -
        localFiniteSeriesHom (calL p) * NativeJointSuccessorJSeries.actualOddSeries p : LaurentSeries K).coeff (-1) =
      (actualOddQuotientSeries p * actualKSeries p - localFiniteSeriesHom (calL p) *
        localFiniteSeriesHom (frobeniusPhi p) *
          (actualLogSeries +
            localFiniteSeriesHom (D (invert (actualAK p : K[X]).toLaurent)))).coeff (-1) := by
  have hi := lowH_finite_series_IBP (calL p : K[T;T⁻¹]) (actualOddQuotientSeries (K := K) p)
  change (localFiniteSeriesHom (D (calL p : K[T;T⁻¹])) * actualOddQuotientSeries (K := K) p).coeff (-1) +
    (localFiniteSeriesHom (calL p : K[T;T⁻¹]) *
      LaurentSeries.derivative K (actualOddQuotientSeries (K := K) p)).coeff (-1) = 0 at hi
  have hi' : (actualOddQuotientSeries (K := K) p *
      LaurentSeries.derivative K (localFiniteSeriesHom (calL p : K[T;T⁻¹])) +
        localFiniteSeriesHom (calL p : K[T;T⁻¹]) * LaurentSeries.derivative K
          (actualOddQuotientSeries (K := K) p) : LaurentSeries K).coeff (-1) = 0 := by
    have hd : LaurentSeries.derivative K (localFiniteSeriesHom (calL p : K[T;T⁻¹])) =
        localFiniteSeriesHom (D (calL p)) := (lowHFiniteSeries_derivative (calL p)).symm
    rw [HahnSeries.coeff_add, hd]
    simpa only [mul_comm] using hi
  rw [actual_odd_series_source p hp] at hi'
  rw [actual_adjoint_series_source p hp]
  simp only [mul_add, mul_sub, mul_assoc, HahnSeries.coeff_add, HahnSeries.coeff_sub] at *
  linear_combination (norm := ring_nf) -hi'

/-- Reflection is applied to the complete actual density and to its differential. -/
noncomputable def actualOddInfinitySeries (p : ℕ) : LaurentSeries K :=
  -localFiniteSeriesHom (T (-2) * invert (oddDensityCleared p : K[T;T⁻¹])) /
    (localFiniteSeriesHom (invert WPFiniteWSource.squaredCoordinate.toLaurent) ^
      ((p - 1) / 2 + 1) *
        localFiniteSeriesHom (invert (WPFiniteZSource.Abar : K[X]).toLaurent))

/-- The actual reflected odd numerator retains its full squared Frobenius phase. -/
theorem actual_odd_density_inverse_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    invert (oddDensityCleared p : K[T;T⁻¹]) =
      T (-((((p - 1) / 2 + 1 : ℕ) : ℤ))) *
        (LaurentPolynomial.C (3 / 2 : K) *
            WPFiniteWSource.squaredCoordinate.toLaurent ^ p * (4 * T (p : ℤ) - 11) ^ 2 -
          LaurentPolynomial.C (75 / 2 : K)) := by
  let N := (p - 1) / 2
  have hN : 2 * N + 1 = p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with he | ho <;> dsimp [N] <;> omega
  simp only [oddDensityCleared, map_sub, map_mul, map_pow, invert_C, invert_T,
    neg_neg, frobeniusPhi, map_ofNat, WPFiniteZSource.invert_squaredCoordinate]
  change LaurentPolynomial.C (3 / 2 : K) * T (N : ℤ) *
      (T (-1) * WPFiniteWSource.squaredCoordinate.toLaurent) ^ (2 * N + 1) *
        (4 * T (p : ℤ) - 11) ^ 2 -
      LaurentPolynomial.C (75 / 2 : K) * T (-((N + 1 : ℕ) : ℤ)) = _
  rw [mul_pow, T_pow]
  have ht : (T (N : ℤ) * T (-1 * ((2 * N + 1 : ℕ) : ℤ)) : K[T;T⁻¹]) =
      T (-((N + 1 : ℕ) : ℤ)) := by rw [← T_add]; congr 1; omega
  calc
    _ = LaurentPolynomial.C (3 / 2 : K) *
        (T (N : ℤ) * T (-1 * ((2 * N + 1 : ℕ) : ℤ))) *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ (2 * N + 1) *
            (4 * T (p : ℤ) - 11) ^ 2 -
        LaurentPolynomial.C (75 / 2 : K) * T (-((N + 1 : ℕ) : ℤ)) := by ring
    _ = _ := by rw [ht, hN]; ring

/-- The reciprocal density is the same original Sodd, including both infinity terms. -/
theorem actual_odd_infinity_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (actualOddInfinitySeries p : LaurentSeries K) =
      localFiniteSeriesHom (LaurentPolynomial.C (75 / 2 : K)) *
          localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) /
          localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ p /
          localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent -
        localFiniteSeriesHom (LaurentPolynomial.C (3 / 2 : K)) *
          localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          localFiniteSeriesHom (4 * T (p : ℤ) - 11 : K[T;T⁻¹]) ^ 2 /
          localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent := by
  let N := (p - 1) / 2
  let S : LaurentSeries K := localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent
  let A : LaurentSeries K := localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent
  have hS : S ≠ 0 := squaredCoordinate_series_ne_zero p hp
  have hA : A ≠ 0 := Abar_series_ne_zero p hp
  have hT (j : ℤ) : localFiniteSeriesHom (T j : K[T;T⁻¹]) ≠ 0 := by
    rw [localFiniteSeries_T]
    exact HahnSeries.single_ne_zero one_ne_zero
  have hN : 2 * N + 1 = p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with he | ho <;> dsimp [N] <;> omega
  have ht : (localFiniteSeriesHom (T (-1) : K[T;T⁻¹])) ^ (N + 1) =
      localFiniteSeriesHom (T (-((N + 1 : ℕ) : ℤ)) : K[T;T⁻¹]) := by
    rw [← map_pow, T_pow]
    congr 2
    omega
  have hn : localFiniteSeriesHom (invert (oddDensityCleared p : K[T;T⁻¹])) =
      localFiniteSeriesHom (T (-((N + 1 : ℕ) : ℤ)) : K[T;T⁻¹]) *
        (localFiniteSeriesHom (LaurentPolynomial.C (3 / 2 : K)) * S ^ p *
            localFiniteSeriesHom (4 * T (p : ℤ) - 11 : K[T;T⁻¹]) ^ 2 -
          localFiniteSeriesHom (LaurentPolynomial.C (75 / 2 : K))) := by
    simpa only [map_mul, map_sub, map_pow, S, N] using
      congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
        (actual_odd_density_inverse_source (K := K) p hp)
  have hsi : localFiniteSeriesHom (invert WPFiniteWSource.squaredCoordinate.toLaurent) =
      localFiniteSeriesHom (T (-1) : K[T;T⁻¹]) * S := by
    rw [WPFiniteZSource.invert_squaredCoordinate, map_mul]
  have hai : localFiniteSeriesHom (invert (WPFiniteZSource.Abar : K[X]).toLaurent) =
      localFiniteSeriesHom (T (-2) : K[T;T⁻¹]) * A := by
    rw [WPFiniteZSource.invert_Abar, map_mul]
  unfold actualOddInfinitySeries
  rw [map_mul, hn, hsi, hai, mul_pow]
  change -(localFiniteSeriesHom (T (-2) : K[T;T⁻¹]) *
      (localFiniteSeriesHom (T (-((N + 1 : ℕ) : ℤ)) : K[T;T⁻¹]) *
        (localFiniteSeriesHom (LaurentPolynomial.C (3 / 2 : K)) * S ^ p *
            localFiniteSeriesHom (4 * T (p : ℤ) - 11 : K[T;T⁻¹]) ^ 2 -
          localFiniteSeriesHom (LaurentPolynomial.C (75 / 2 : K))))) /
      ((localFiniteSeriesHom (T (-1) : K[T;T⁻¹])) ^ (N + 1) * S ^ (N + 1) *
        (localFiniteSeriesHom (T (-2) : K[T;T⁻¹]) * A)) = _
  change _ = localFiniteSeriesHom (LaurentPolynomial.C (75 / 2 : K)) * S ^ N / S ^ p / A -
    localFiniteSeriesHom (LaurentPolynomial.C (3 / 2 : K)) * S ^ N *
      localFiniteSeriesHom (4 * T (p : ℤ) - 11 : K[T;T⁻¹]) ^ 2 / A
  rw [ht]
  have hSp : S ^ p = S ^ N * S ^ (N + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hSp]
  let U : LaurentSeries K := localFiniteSeriesHom (T (-((N + 1 : ℕ) : ℤ)) : K[T;T⁻¹])
  let V : LaurentSeries K := localFiniteSeriesHom (T (-2) : K[T;T⁻¹])
  have hU : U ≠ 0 := hT _
  have hV : V ≠ 0 := hT _
  change -(V * (U *
      (localFiniteSeriesHom (LaurentPolynomial.C (3 / 2 : K)) * (S ^ N * S ^ (N + 1)) *
        localFiniteSeriesHom (4 * T (p : ℤ) - 11 : K[T;T⁻¹]) ^ 2 -
          localFiniteSeriesHom (LaurentPolynomial.C (75 / 2 : K))))) /
      (U * S ^ (N + 1) * (V * A)) =
    localFiniteSeriesHom (LaurentPolynomial.C (75 / 2 : K)) * S ^ N / (S ^ N * S ^ (N + 1)) / A -
    localFiniteSeriesHom (LaurentPolynomial.C (3 / 2 : K)) * S ^ N *
      localFiniteSeriesHom (4 * T (p : ℤ) - 11 : K[T;T⁻¹]) ^ 2 / A
  field_simp [hS, hA, hU, hV]
  ring

private theorem polynomial_powerSeries_embedding (P : K[X]) :
    localFiniteSeriesHom P.toLaurent = ((P : PowerSeries K) : LaurentSeries K) := by
  have he : localFiniteSeriesHom P.toLaurent = algebraMap K[X] (LaurentSeries K) P := by
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | monomial n c =>
        rw [← C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow]
        change lowHFiniteSeries (LaurentPolynomial.C c * T (n : ℤ)) = _
        rw [lowHFiniteSeries_monomial, lowH_series_polynomial_monomial]
  simpa only [Polynomial.algebraMap_hahnSeries_apply] using he

private theorem power_inverse_embedding (Q : PowerSeries K)
    (hc : PowerSeries.constantCoeff Q ≠ 0) (hQ : (Q : LaurentSeries K) ≠ 0) :
    ((Q⁻¹ : PowerSeries K) : LaurentSeries K) = (Q : LaurentSeries K)⁻¹ := by
  apply mul_right_cancel₀ hQ
  rw [inv_mul_cancel₀ hQ, ← PowerSeries.coe_mul,
    PowerSeries.inv_mul_cancel Q hc, PowerSeries.coe_one]

private theorem finite_regular_product_below (F : K[T;T⁻¹]) (Q : PowerSeries K)
    (M k : ℤ) (hF : ∀ j : ℤ, j < M → F.coeff j = 0) (hk : k < M) :
    (localFiniteSeriesHom F * (Q : LaurentSeries K)).coeff k = 0 := by
  let P := LaurentPolynomial.trunc (T (-M) * F)
  have hP : (T (-M) * F : K[T;T⁻¹]) = P.toLaurent := by
    ext j
    by_cases hj : 0 ≤ j
    · have hjn : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj
      rw [← hjn, WPFiniteJCarrier.toLaurent_coeff_nat]
      dsimp only [P]
      rw [WPFiniteJWeightedResidue.trunc_coeff]
    · rw [WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))]
      have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-M) j F
      simp only [map_one, one_mul] at hs
      rw [hs, hF _ (by omega)]
  have hsource : (T M * P.toLaurent : K[T;T⁻¹]) = F := by
    rw [← hP, ← mul_assoc, ← T_add, add_neg_cancel, T_zero, one_mul]
  have hs : localFiniteSeriesHom F * (Q : LaurentSeries K) =
      HahnSeries.single M (1 : K) * (((P : PowerSeries K) * Q : PowerSeries K) : LaurentSeries K) := by
    rw [← hsource, map_mul, localFiniteSeries_T, polynomial_powerSeries_embedding,
      PowerSeries.coe_mul, mul_assoc]
  rw [hs, HahnSeries.coeff_single_mul, one_mul, PowerSeries.coeff_coe,
    if_pos (by omega : k - M < 0)]

private theorem squaredCoordinate_frobenius (p : ℕ) [Fact p.Prime] [CharP K p] :
    (WPFiniteWSource.squaredCoordinate : K[X]) ^ p =
      Polynomial.C (1 / 5 : K) * (X ^ p + 1) := by
  have h5 : (5 : K) ^ p = 5 := WPFiniteField.natCast_pow_char p 5
  rw [WPFiniteWSource.squaredCoordinate, mul_pow, ← map_pow, inv_pow, h5,
    add_pow_char, one_pow]
  rw [one_div]

private theorem Abar_power_inverse (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (((((WPFiniteZSource.Abar : K[X]) : PowerSeries K)⁻¹) : PowerSeries K) : LaurentSeries K) =
      (localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent)⁻¹ := by
  let Q : PowerSeries K := (WPFiniteZSource.Abar : K[X])
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hc0 : PowerSeries.constantCoeff Q = -4 := by
    simp [Q, WPFiniteZSource.Abar]
  have hc : PowerSeries.constantCoeff Q ≠ 0 := by
    rw [hc0]
    exact neg_ne_zero.mpr h4
  have hQ : (Q : LaurentSeries K) ≠ 0 := by
    rw [← polynomial_powerSeries_embedding]
    exact Abar_series_ne_zero p hp
  simpa only [Q, ← polynomial_powerSeries_embedding] using power_inverse_embedding Q hc
    (by simpa only [Q, ← polynomial_powerSeries_embedding] using hQ)

private theorem reciprocal_calL_below (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (j : ℤ) (hj : j < -(((p - 1) / 2 - 1 : ℕ) : ℤ)) :
    (invert (calL p : K[T;T⁻¹])).coeff j = 0 := by
  rw [invert_apply]
  exact calL_coeff_outside p hp (-j) (Or.inr (by omega))

/-- The support bound alone permits the Frobenius denominator at this infinity residue. -/
theorem actual_odd_infinity_denominator_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (localFiniteSeriesHom (invert (calL p : K[T;T⁻¹])) *
        localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) /
        localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ p /
        localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent).coeff (-1) =
      5 * originPole (invert (calL p) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) := by
  let N := (p - 1) / 2
  let F : K[T;T⁻¹] := invert (calL p) * WPFiniteWSource.squaredCoordinate.toLaurent ^ N
  let AP : PowerSeries K := (WPFiniteZSource.Abar : K[X])
  let W : PowerSeries K := PowerSeries.X ^ p + 1
  let WS : LaurentSeries K := W
  let G : LaurentSeries K := localFiniteSeriesHom F /
    localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent
  have hW : WS = localFiniteSeriesHom (T (p : ℤ) + 1 : K[T;T⁻¹]) := by
    dsimp only [WS, W]
    simp only [PowerSeries.coe_pow, PowerSeries.coe_X,
      map_add, localFiniteSeries_T, map_one,
      HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
  have hWS : WS = localFiniteSeriesHom (T (p : ℤ) : K[T;T⁻¹]) + 1 := by
    simpa only [map_add, map_one] using hW
  have hW0 : PowerSeries.constantCoeff W ≠ 0 := by
    simp [W, show p ≠ 0 by omega]
  have hWN : WS ≠ 0 := by
    intro hz
    have hc := congrArg (fun Q : LaurentSeries K => Q.coeff 0) hz
    rw [hW, localFiniteSeries_coeff] at hc
    simp [LaurentPolynomial.T_apply, show p ≠ 0 by omega] at hc
  have hiW : ((W⁻¹ : PowerSeries K) : LaurentSeries K) = WS⁻¹ :=
    power_inverse_embedding W hW0 hWN
  have hI : ((AP⁻¹ : PowerSeries K) : LaurentSeries K) =
      (localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent)⁻¹ :=
    Abar_power_inverse p hp
  have hQ : G / WS = localFiniteSeriesHom (invert (calL p)) *
      (((((WPFiniteWSource.squaredCoordinate : K[X]) ^ N : K[X]) : PowerSeries K) *
        AP⁻¹ * W⁻¹ : PowerSeries K) : LaurentSeries K) := by
    dsimp only [G, F]
    rw [map_mul, ← map_pow, polynomial_powerSeries_embedding,
      PowerSeries.coe_mul, PowerSeries.coe_mul, hI, hiW]
    ring
  have hz : (G / WS).coeff (-1 - (p : ℤ)) = 0 := by
    rw [hQ]
    exact finite_regular_product_below _ _ (-((N - 1 : ℕ) : ℤ)) _
      (fun j hj => reciprocal_calL_below p hp j hj) (by dsimp only [N]; omega)
  have hquot : G / WS + localFiniteSeriesHom (T (p : ℤ) : K[T;T⁻¹]) * (G / WS) = G := by
    calc
      _ = (localFiniteSeriesHom (T (p : ℤ) : K[T;T⁻¹]) + 1) * (G / WS) := by ring
      _ = WS * (G / WS) := by rw [← hWS]
      _ = G := by field_simp [hWN]
  have hres := congrArg (fun Q : LaurentSeries K => Q.coeff (-1)) hquot
  rw [HahnSeries.coeff_add, localFiniteSeries_T, HahnSeries.coeff_single_mul,
    one_mul, hz, add_zero] at hres
  have hs := congrArg (fun P : K[X] => localFiniteSeriesHom P.toLaurent)
    (squaredCoordinate_frobenius (K := K) p)
  simp only [map_pow, map_mul, Polynomial.toLaurent_C, map_add, map_one,
    Polynomial.toLaurent_X, T_pow, mul_one] at hs
  rw [← hWS] at hs
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h5S : (localFiniteSeriesHom (LaurentPolynomial.C (5 : K)) : LaurentSeries K) ≠ 0 := by
    rw [localFiniteSeries_C, LaurentSeries.algebraMap_apply]
    exact HahnSeries.C_ne_zero h5
  have hcinv : localFiniteSeriesHom (LaurentPolynomial.C (1 / 5 : K)) =
      (localFiniteSeriesHom (LaurentPolynomial.C (5 : K)))⁻¹ := by
    simpa only [localFiniteSeries_C, one_div] using
      map_inv₀ (algebraMap K (LaurentSeries K)) (5 : K)
  have he : localFiniteSeriesHom (invert (calL p)) *
      localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ N /
      localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ p /
      localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent =
        localFiniteSeriesHom (LaurentPolynomial.C (5 : K)) * (G / WS) := by
    rw [hs, hcinv]
    dsimp only [G, F]
    rw [map_mul, map_pow]
    field_simp [hWN, Abar_series_ne_zero p hp, h5S]
  rw [he, localFiniteSeries_C, LaurentSeries.algebraMap_apply, HahnSeries.C_apply,
    HahnSeries.coeff_single_mul, sub_zero, hres]
  dsimp only [G]
  rw [local_Abar_quotient_residue p hp]

private theorem actual_odd_infinity_phase_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (localFiniteSeriesHom (invert (calL p : K[T;T⁻¹])) *
        localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        localFiniteSeriesHom (4 * T (p : ℤ) - 11 : K[T;T⁻¹]) ^ 2 /
        localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent).coeff (-1) =
      121 * originPole (invert (calL p) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) := by
  let N := (p - 1) / 2
  let F : K[T;T⁻¹] := invert (calL p) * WPFiniteWSource.squaredCoordinate.toLaurent ^ N
  let AP : PowerSeries K := (WPFiniteZSource.Abar : K[X])
  let G : LaurentSeries K := localFiniteSeriesHom F /
    localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent
  have hI : ((AP⁻¹ : PowerSeries K) : LaurentSeries K) =
      (localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent)⁻¹ :=
    Abar_power_inverse p hp
  have hG : G = localFiniteSeriesHom (invert (calL p)) *
      (((((WPFiniteWSource.squaredCoordinate : K[X]) ^ N : K[X]) : PowerSeries K) *
        AP⁻¹ : PowerSeries K) : LaurentSeries K) := by
    dsimp only [G, F]
    rw [map_mul, ← map_pow, polynomial_powerSeries_embedding,
      PowerSeries.coe_mul, hI]
    ring
  have hz1 : G.coeff (-1 - (p : ℤ)) = 0 := by
    rw [hG]
    exact finite_regular_product_below _ _ (-((N - 1 : ℕ) : ℤ)) _
      (fun j hj => reciprocal_calL_below p hp j hj) (by dsimp only [N]; omega)
  have hz2 : G.coeff (-1 - 2 * (p : ℤ)) = 0 := by
    rw [hG]
    exact finite_regular_product_below _ _ (-((N - 1 : ℕ) : ℤ)) _
      (fun j hj => reciprocal_calL_below p hp j hj) (by dsimp only [N]; omega)
  have he : localFiniteSeriesHom (invert (calL p)) *
      localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ N *
      localFiniteSeriesHom (4 * T (p : ℤ) - 11 : K[T;T⁻¹]) ^ 2 /
      localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent =
        localFiniteSeriesHom (LaurentPolynomial.C (16 : K) * T (2 * (p : ℤ))) * G -
          localFiniteSeriesHom (LaurentPolynomial.C (88 : K) * T (p : ℤ)) * G +
          localFiniteSeriesHom (LaurentPolynomial.C (121 : K)) * G := by
    have ht : (T (p : ℤ) : K[T;T⁻¹]) ^ 2 = T (2 * (p : ℤ)) := by
      rw [T_pow]
      congr 1
    have hsource : ((4 * T (p : ℤ) - 11 : K[T;T⁻¹]) ^ 2) =
        LaurentPolynomial.C (16 : K) * T (2 * (p : ℤ)) -
          LaurentPolynomial.C (88 : K) * T (p : ℤ) + LaurentPolynomial.C (121 : K) := by
      rw [← ht]
      simp only [map_ofNat]
      ring
    have hphase := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K) hsource
    rw [map_pow] at hphase
    rw [hphase, map_add, map_sub]
    dsimp only [G, F]
    simp only [map_mul, map_pow]
    ring
  rw [he, HahnSeries.coeff_add, HahnSeries.coeff_sub]
  simp only [map_mul, localFiniteSeries_C, localFiniteSeries_T,
    LaurentSeries.algebraMap_apply, HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add, HahnSeries.coeff_single_mul,
    sub_zero, hz1, hz2, mul_zero, sub_zero, zero_add]
  dsimp only [G]
  rw [local_Abar_quotient_residue p hp]

/-- The infinity contribution is six times the SAME full reciprocal unit residue. -/
theorem actual_odd_infinity_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (localFiniteSeriesHom (invert (calL p : K[T;T⁻¹])) *
        actualOddInfinitySeries p).coeff (-1) =
      6 * originPole (invert (calL p) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) := by
  rw [actual_odd_infinity_source p hp]
  have he : localFiniteSeriesHom (invert (calL p)) *
      (localFiniteSeriesHom (LaurentPolynomial.C (75 / 2 : K)) *
          localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) /
          localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ p /
          localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent -
        localFiniteSeriesHom (LaurentPolynomial.C (3 / 2 : K)) *
          localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          localFiniteSeriesHom (4 * T (p : ℤ) - 11 : K[T;T⁻¹]) ^ 2 /
          localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent) =
      localFiniteSeriesHom (LaurentPolynomial.C (75 / 2 : K)) *
        (localFiniteSeriesHom (invert (calL p)) *
          localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) /
          localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ p /
          localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent) -
      localFiniteSeriesHom (LaurentPolynomial.C (3 / 2 : K)) *
        (localFiniteSeriesHom (invert (calL p)) *
          localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          localFiniteSeriesHom (4 * T (p : ℤ) - 11 : K[T;T⁻¹]) ^ 2 /
          localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent) := by ring
  rw [he, HahnSeries.coeff_sub]
  simp only [localFiniteSeries_C, LaurentSeries.algebraMap_apply, HahnSeries.C_apply,
    HahnSeries.coeff_single_mul, sub_zero]
  rw [actual_odd_infinity_denominator_residue p hp, actual_odd_infinity_phase_residue p hp]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  field_simp [h2]
  ring

/-- The actual branch factor makes the entire odd times Kj product a finite quotient. -/
theorem actual_odd_K_series_carrier (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (actualOddQuotientSeries p * actualKSeries p : LaurentSeries K) =
      localFiniteSeriesHom
        (oddReciprocalS p * T (-(((p - 1) / 2 - 1 : ℕ) : ℤ)) *
          (actualCtilde p).toLaurent) /
            localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent := by
  let N := (p - 1) / 2
  let s : K[T;T⁻¹] := WPFiniteWSource.squaredCoordinate.toLaurent
  have ht : (T (-((N - 1 : ℕ) : ℤ)) * T ((N - 1 : ℕ) : ℤ) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  have hb := lowH_Dsym_full_branch_factor (K := K) p hp
  have hn : (actualAdjointNumerator p : K[T;T⁻¹]) =
      s ^ N * T (-((N - 1 : ℕ) : ℤ)) * (actualCtilde p).toLaurent := by
    unfold actualAdjointNumerator actualCtilde
    rw [hb]
    simp only [map_sub, map_mul, map_ofNat, map_pow, Polynomial.toLaurent_C,
      Polynomial.toLaurent_X, T_pow]
    change LaurentPolynomial.C (2 / 5 : K) * (33 - 12 * T 1) *
        (T (-((N - 1 : ℕ) : ℤ)) * s ^ (N + 1) * (branchPolynomial p).toLaurent) -
      2 * LaurentPolynomial.C (WPFiniteNC122.h p) * s ^ N = _
    rw [show ((N - 1 : ℕ) : ℤ) * 1 = ((N - 1 : ℕ) : ℤ) by ring]
    rw [pow_succ]
    dsimp only [s]
    linear_combination (norm := ring_nf) 2 * LaurentPolynomial.C (WPFiniteNC122.h p) *
      (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent ^ N * ht
  unfold actualOddQuotientSeries actualKSeries
  rw [hn]
  simp only [map_mul, map_pow]
  field_simp [squaredCoordinate_series_ne_zero p hp, Abar_series_ne_zero p hp]
  ring

/-- This exact primitive retains the original branch and all proper-end data in finite carriers. -/
theorem actual_odd_branch_residue_reduction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (actualOddQuotientSeries p * actualLambdaSeries p -
        localFiniteSeriesHom (calL p) * NativeJointSuccessorJSeries.actualOddSeries p :
          LaurentSeries K).coeff (-1) =
      originPole (oddReciprocalS p * T (-(((p - 1) / 2 - 1 : ℕ) : ℤ)) *
          (actualCtilde p).toLaurent) - (oddLogLaurentCarrier p : K[T;T⁻¹]).coeff (-1) -
        (calL p * frobeniusPhi p * D (invert (actualAK p : K[X]).toLaurent)).coeff (-1) := by
  rw [actual_odd_exact_primitive_reduction p hp]
  have he : actualOddQuotientSeries p * actualKSeries p - localFiniteSeriesHom (calL p) *
      localFiniteSeriesHom (frobeniusPhi p) *
        (actualLogSeries + localFiniteSeriesHom (D (invert (actualAK p : K[X]).toLaurent))) =
      actualOddQuotientSeries p * actualKSeries p -
        localFiniteSeriesHom (calL p) * localFiniteSeriesHom (frobeniusPhi p) * actualLogSeries -
        localFiniteSeriesHom (calL p * frobeniusPhi p * D (invert (actualAK p : K[X]).toLaurent)) := by
    simp only [map_mul]
    ring
  rw [he, HahnSeries.coeff_sub, HahnSeries.coeff_sub, actual_odd_K_series_carrier p hp,
    actual_calL_log_series_carrier p hp, local_Abar_quotient_residue p hp,
    localFiniteSeries_coeff, localFiniteSeries_coeff]

end WPFieldAssembly.NativeJointSuccessorOddResidues


