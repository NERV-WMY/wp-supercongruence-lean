import WPFieldAssembly.ActualBpairLowHSeriesIBP
import WPFieldAssembly.ActualSimplePoleResidue

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries
open WPFieldAssembly.GreenLaurentOperators
open WPFieldAssembly.ActualBpairContraction

namespace WPFieldAssembly.ActualBpairLowHLocalPole

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/- STATEMENT_FIDELITY: For prime p >= 19 and any characteristic-p field K,
   the residue of the entire literal finite Laurent source divided by the
   original Abar is originPole F. The embedding retains every signed coefficient.
   DD uses the original endpoints 1/4 and 4, and their original inverse values.
   No finite manifest, rational descent, or final scalar identity is asserted. -/

/-- The whole coefficient embedding, with its already proved product identity. -/
noncomputable def localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K where
  toFun := lowHFiniteSeries
  map_zero' := map_zero _
  map_one' := by
    rw [show (1 : K[T;T⁻¹]) = LaurentPolynomial.C (1 : K) * T 0 by simp,
      lowHFiniteSeries_monomial]
    rfl
  map_add' := map_add _
  map_mul' := lowHFiniteSeries_mul

theorem localFiniteSeries_coeff (F : K[T;T⁻¹]) (n : ℤ) :
    (localFiniteSeriesHom F).coeff n = F.coeff n := rfl

theorem localFiniteSeries_C (c : K) :
    localFiniteSeriesHom (LaurentPolynomial.C c) = algebraMap K (LaurentSeries K) c := by
  change lowHFiniteSeries (LaurentPolynomial.C c) = _
  rw [show LaurentPolynomial.C c = LaurentPolynomial.C c * T 0 by simp,
    lowHFiniteSeries_monomial]
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply]

theorem localFiniteSeries_T (n : ℤ) :
    localFiniteSeriesHom (T n : K[T;T⁻¹]) = HahnSeries.single n (1 : K) := by
  change lowHFiniteSeries (T n : K[T;T⁻¹]) = _
  simpa only [map_one, one_mul] using lowHFiniteSeries_monomial (1 : K) n

private theorem linear_series_ne_zero (c : K) :
    (HahnSeries.single 1 (1 : K) - algebraMap K (LaurentSeries K) c) ≠ 0 := by
  intro h
  have he := congrArg (fun Q : LaurentSeries K => Q.coeff 1) h
  simp [LaurentSeries.algebraMap_apply, HahnSeries.C_apply] at he

/-- A proper-end pole has an actual power-series inverse at zero. -/
theorem local_linear_inverse_residue (c : K) (hc : c ≠ 0) :
    ((HahnSeries.single 1 (1 : K) - algebraMap K (LaurentSeries K) c)⁻¹).coeff (-1) = 0 := by
  let Q : PowerSeries K := PowerSeries.X - PowerSeries.C c
  have hQ : PowerSeries.constantCoeff Q ≠ 0 := by
    simpa only [Q, map_sub, PowerSeries.constantCoeff_X,
      PowerSeries.constantCoeff_C, zero_sub, neg_ne_zero] using hc
  have hcoe : (Q : LaurentSeries K) =
      HahnSeries.single 1 (1 : K) - algebraMap K (LaurentSeries K) c := by
    dsimp only [Q]
    simp only [PowerSeries.coe_sub, PowerSeries.coe_X, PowerSeries.coe_C,
      LaurentSeries.algebraMap_apply]
  have hinv : ((Q⁻¹ : PowerSeries K) : LaurentSeries K) =
      (HahnSeries.single 1 (1 : K) - algebraMap K (LaurentSeries K) c)⁻¹ := by
    apply mul_right_cancel₀ (linear_series_ne_zero c)
    rw [inv_mul_cancel₀ (linear_series_ne_zero c), ← hcoe, ← PowerSeries.coe_mul,
      PowerSeries.inv_mul_cancel Q hQ, PowerSeries.coe_one]
  rw [← hinv, PowerSeries.coeff_coe, if_pos (by omega : (-1 : ℤ) < 0)]

/-- The literal DD identity and its endpoint correction are attached to the whole quotient. -/
theorem local_linear_quotient_residue (c : K) (hc : c ≠ 0) (F : K[T;T⁻¹]) :
    (localFiniteSeriesHom F /
      (HahnSeries.single 1 (1 : K) - algebraMap K (LaurentSeries K) c)).coeff (-1) =
        (DD c c⁻¹ F).coeff (-1) := by
  let L : LaurentSeries K := HahnSeries.single 1 (1 : K) - algebraMap K (LaurentSeries K) c
  have hL : L ≠ 0 := linear_series_ne_zero c
  have he := congrArg localFiniteSeriesHom (DD_identity c hc F)
  simp only [map_mul, map_sub, localFiniteSeries_T, localFiniteSeries_C] at he
  have hquot : localFiniteSeriesHom F / L =
      localFiniteSeriesHom (DD c c⁻¹ F) + algebraMap K (LaurentSeries K) (ev c hc F) / L := by
    have hsource : localFiniteSeriesHom F =
        L * localFiniteSeriesHom (DD c c⁻¹ F) + algebraMap K (LaurentSeries K) (ev c hc F) := by
      dsimp only [L]
      linear_combination -he
    rw [hsource, add_div, mul_div_cancel_left₀ _ hL]
  rw [hquot, HahnSeries.coeff_add, localFiniteSeries_coeff]
  have hz : (algebraMap K (LaurentSeries K) (ev c hc F) / L).coeff (-1) = 0 := by
    rw [div_eq_mul_inv,
      show algebraMap K (LaurentSeries K) (ev c hc F) = HahnSeries.single 0 (ev c hc F) by
        rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply],
      HahnSeries.coeff_single_mul, sub_zero, local_linear_inverse_residue c hc, mul_zero]
  rw [hz, add_zero]

/-- Both original proper-end poles and every signed input coefficient are retained. -/
theorem local_Abar_quotient_residue (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (F : K[T;T⁻¹]) :
    (localFiniteSeriesHom F /
      localFiniteSeriesHom ((WPFiniteZSource.Abar : K[X]).toLaurent)).coeff (-1) =
        WPFieldAssembly.ActualSimplePoleResidue.originPole F := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have ha : (1 / 4 : K) ≠ 0 := div_ne_zero one_ne_zero h4
  let x : LaurentSeries K := HahnSeries.single 1 (1 : K)
  let a : LaurentSeries K := algebraMap K (LaurentSeries K) (1 / 4 : K)
  let A : LaurentSeries K := localFiniteSeriesHom ((WPFiniteZSource.Abar : K[X]).toLaurent)
  have h4S : (4 : LaurentSeries K) ≠ 0 := by
    change HahnSeries.C (4 : K) ≠ 0
    exact HahnSeries.C_ne_zero h4
  have h15S : (15 : LaurentSeries K) ≠ 0 := by
    change HahnSeries.C (15 : K) ≠ 0
    exact HahnSeries.C_ne_zero h15
  have hunit : (4 : LaurentSeries K) * a = 1 := by
    have hu := congrArg (algebraMap K (LaurentSeries K)) (mul_one_div_cancel h4)
    simpa only [map_mul, map_ofNat, map_one] using hu
  have hA : A = -4 * (x - a) * (x - 4) := by
    dsimp only [A, x, a]
    simp only [WPFiniteZSource.Abar, map_mul, map_sub, map_ofNat, map_one,
      Polynomial.toLaurent_X, localFiniteSeries_T]
    linear_combination (4 - HahnSeries.single 1 (1 : K)) * hunit
  have hxa : x - a ≠ 0 := linear_series_ne_zero (1 / 4 : K)
  have hxb : x - (4 : LaurentSeries K) ≠ 0 := by
    simpa only [map_ofNat] using linear_series_ne_zero (4 : K)
  have hAN : A ≠ 0 := by rw [hA]; exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h4S) hxa) hxb
  have hquotients : localFiniteSeriesHom F / A =
      (localFiniteSeriesHom F / (x - a) - localFiniteSeriesHom F / (x - 4)) / 15 := by
    apply (div_eq_iff hAN).mpr
    rw [hA]
    field_simp [hxa, hxb, h15S]
    linear_combination localFiniteSeriesHom F * hunit
  have hinv15 : (15 : LaurentSeries K)⁻¹ = HahnSeries.single 0 ((15 : K)⁻¹) := by
    have hh := (map_inv₀ (algebraMap K (LaurentSeries K)) (15 : K)).symm
    simpa only [map_ofNat, LaurentSeries.algebraMap_apply, HahnSeries.C_apply] using hh
  have hqa : (localFiniteSeriesHom F / (x - a)).coeff (-1) =
      (DD (1 / 4 : K) 4 F).coeff (-1) := by
    dsimp only [x, a]
    simpa only [one_div, inv_inv] using local_linear_quotient_residue (1 / 4 : K) ha F
  have hqb : (localFiniteSeriesHom F / (x - 4)).coeff (-1) =
      (DD (4 : K) (1 / 4) F).coeff (-1) := by
    simpa only [map_ofNat, one_div] using local_linear_quotient_residue (4 : K) h4 F
  rw [hquotients, div_eq_mul_inv, hinv15,
    HahnSeries.coeff_mul_single, sub_zero, HahnSeries.coeff_sub, hqa, hqb]
  simp only [WPFieldAssembly.ActualSimplePoleResidue.originPole,
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, div_eq_mul_inv]

end WPFieldAssembly.ActualBpairLowHLocalPole
