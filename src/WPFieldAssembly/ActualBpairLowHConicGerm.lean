import WPFieldAssembly.ActualBpairLowHLocal
import WPFieldAssembly.ActualBpairLowHSeries
import WPFieldAssembly.ActualBpairLowHGreen

open scoped Polynomial PowerSeries LaurentSeries
open Polynomial HahnSeries

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/-- A regular primitive may have infinite support; the entire rational Frobenius factor remains. -/
theorem lowH_regular_exact_series_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (Q : LaurentSeries K) (J : PowerSeries K) :
    (Q ^ p * (PowerSeries.derivative K J : LaurentSeries K)).coeff (-1) = 0 := by
  classical
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hsum : ij.1 + ij.2 = -1 := (Finset.mem_antidiagonal.mp hij).2.2
  by_cases hi : (p : ℤ) ∣ ij.1
  · have hd : (PowerSeries.derivative K J : LaurentSeries K).coeff ij.2 = 0 := by
      rw [PowerSeries.coeff_coe]
      by_cases hj : ij.2 < 0
      · rw [if_pos hj]
      · rw [if_neg hj]
        have hj' : ((ij.2.natAbs : ℕ) : ℤ) = ij.2 := (Int.eq_natAbs_of_nonneg (by omega)).symm
        have hu : ((ij.2.natAbs + 1 : ℕ) : K) = 0 := by
          have he : (p : ℤ) ∣ (ij.2.natAbs : ℤ) + 1 := by
            rw [hj']
            convert Int.dvd_neg.mpr hi using 1; omega
          have heK := (CharP.intCast_eq_zero_iff K p _).mpr he
          simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one] using heK
        rw [PowerSeries.coeff_derivative]
        have hu' : (ij.2.natAbs : K) + 1 = 0 := by
          simpa only [Nat.cast_add, Nat.cast_one] using hu
        rw [hu', mul_zero]
    rw [hd, mul_zero]
  · rw [lowH_series_frobenius_coeff p Q _ hi, zero_mul]

/-- This is the literal r=epsilon+z germ, with epsilon nonzero. -/
noncomputable def lowHConicGermR (ε : Kˣ) : PowerSeries K := PowerSeries.C (ε : K) + PowerSeries.X

noncomputable def lowHConicGermW (ε : Kˣ) : PowerSeries K :=
  PowerSeries.C (1 / 2 : K) * (lowHConicGermR ε - (lowHConicGermR ε)⁻¹)

noncomputable def lowHConicGermT (ε : Kˣ) (η : K) : PowerSeries K :=
  PowerSeries.C (η / 2) * (lowHConicGermR ε + (lowHConicGermR ε)⁻¹)

theorem lowHConicGermR_inverse (ε : Kˣ) :
    lowHConicGermR ε * (lowHConicGermR ε)⁻¹ = 1 := by
  exact PowerSeries.mul_inv_cancel _ (by simp [lowHConicGermR])

theorem lowHConicGermW_derivative (ε : Kˣ) :
    PowerSeries.derivative K (lowHConicGermW ε) =
      PowerSeries.C (1 / 2 : K) * (1 + (lowHConicGermR ε)⁻¹ ^ 2) := by
  have hr : PowerSeries.derivative K (lowHConicGermR ε) = 1 := by
    simp [lowHConicGermR]
  simp only [lowHConicGermW, Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_C, mul_zero, add_zero,
    map_sub, PowerSeries.derivative_inv', hr, mul_one, sub_neg_eq_add]

theorem lowHConicGermT_derivative (ε : Kˣ) (η : K) :
    PowerSeries.derivative K (lowHConicGermT ε η) =
      PowerSeries.C (η / 2) * (1 - (lowHConicGermR ε)⁻¹ ^ 2) := by
  have hr : PowerSeries.derivative K (lowHConicGermR ε) = 1 := by
    simp [lowHConicGermR]
  simp only [lowHConicGermT, Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_C, mul_zero, add_zero,
    map_add, PowerSeries.derivative_inv', hr, mul_one]
  ring

/-- Both original points are actual unit germs, with w(0)=0 and w'(0)=1. -/
theorem lowHConicGerm_two_parameters (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (∀ ε : Kˣ, ε = 1 ∨ ε = -1 →
      PowerSeries.constantCoeff (lowHConicGermW ε) = 0 ∧
      PowerSeries.constantCoeff (PowerSeries.derivative K (lowHConicGermW ε)) = 1) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  intro ε hε
  rcases hε with rfl | rfl
  all_goals constructor
  all_goals simp [lowHConicGermW, lowHConicGermR]
  all_goals field_simp [h2]
  all_goals ring

theorem lowHConicGerm_relation (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (ε : Kˣ) (η : K) (hη : (5 : K) * η ^ 2 = 1) :
    (5 : PowerSeries K) * lowHConicGermT ε η ^ 2 = lowHConicGermW ε ^ 2 + 1 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hηC := congrArg (PowerSeries.C : K →+* PowerSeries K) hη
  simp only [map_mul, map_pow, map_ofNat, map_one] at hηC
  have h2C := congrArg (PowerSeries.C : K →+* PowerSeries K) (mul_one_div_cancel h2)
  simp only [map_mul, map_ofNat, map_one] at h2C
  have hAB := lowHConicGermR_inverse ε
  have hdiv : PowerSeries.C (η / 2) = PowerSeries.C η * PowerSeries.C (1 / 2 : K) := by
    simp only [div_eq_mul_inv, one_mul, map_mul]
  rw [lowHConicGermT, lowHConicGermW, hdiv]
  linear_combination (PowerSeries.C (1 / 2 : K)) ^ 2 *
      (lowHConicGermR ε + (lowHConicGermR ε)⁻¹) ^ 2 * hηC +
    4 * (PowerSeries.C (1 / 2 : K)) ^ 2 * hAB +
    (2 * PowerSeries.C (1 / 2 : K) + 1) * h2C

theorem lowHConicGerm_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (η : K) (hη : (5 : K) * η ^ 2 = 1) :
    (5 : PowerSeries K) * lowHConicGermT ε η * PowerSeries.derivative K (lowHConicGermT ε η) =
      lowHConicGermW ε * PowerSeries.derivative K (lowHConicGermW ε) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h2C := congrArg (PowerSeries.C : K →+* PowerSeries K) (mul_one_div_cancel h2)
  simp only [map_mul, map_ofNat, map_one] at h2C
  have ht : PowerSeries.derivative K (lowHConicGermT ε η ^ 2) =
      2 * lowHConicGermT ε η * PowerSeries.derivative K (lowHConicGermT ε η) := by
    rw [pow_two, Derivation.leibniz]
    ring
  have hw : PowerSeries.derivative K (lowHConicGermW ε ^ 2) =
      2 * lowHConicGermW ε * PowerSeries.derivative K (lowHConicGermW ε) := by
    rw [pow_two, Derivation.leibniz]
    ring
  have h5 : PowerSeries.derivative K (5 : PowerSeries K) = 0 := by
    simpa only [map_ofNat] using (PowerSeries.derivative_C (r := (5 : K)))
  have he := congrArg (PowerSeries.derivative K) (lowHConicGerm_relation p hp ε η hη)
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, h5, mul_zero, add_zero, ht, map_add, hw,
    PowerSeries.derivative_one, add_zero] at he
  linear_combination PowerSeries.C (1 / 2 : K) * he -
    (5 * lowHConicGermT ε η * PowerSeries.derivative K (lowHConicGermT ε η) -
      lowHConicGermW ε * PowerSeries.derivative K (lowHConicGermW ε)) * h2C

/-- The complete odd source is identified in the genuine r=epsilon+z expansion. -/
theorem lowHConicGerm_local_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (η : K) (hη : (5 : K) * η ^ 2 = 1) (P : K[X])
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) :
    Polynomial.aeval (lowHConicGermT ε η) P * lowHConicGermW ε *
        PowerSeries.derivative K (lowHConicGermT ε η) =
      Polynomial.aeval (lowHConicGermW ε) (lowHConicLocalP P) *
        PowerSeries.derivative K (lowHConicGermW ε) := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hc := congrArg (PowerSeries.C : K →+* PowerSeries K) (mul_one_div_cancel h5)
  simp only [map_mul, map_ofNat, map_one] at hc
  have hs : lowHConicGermT ε η ^ 2 = PowerSeries.C (1 / 5 : K) * (1 + lowHConicGermW ε ^ 2) := by
    have he := lowHConicGerm_relation p hp ε η hη
    linear_combination PowerSeries.C (1 / 5 : K) * he - lowHConicGermT ε η ^ 2 * hc
  have ht := lowHConicGerm_cleared_derivative p hp ε η hη
  have he := congrArg (fun Q : K[X] => Polynomial.eval₂ PowerSeries.C (lowHConicGermT ε η) Q)
    (lowHOddHalfP_source P hodd)
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_comp,
    Polynomial.eval₂_pow] at he
  simp only [Polynomial.aeval_def, PowerSeries.algebraMap_eq, Polynomial.eval₂_mul, Polynomial.eval₂_X,
    Polynomial.eval₂_comp, Polynomial.eval₂_pow, lowHConicLocalP, Polynomial.eval₂_C,
    Polynomial.eval₂_add, Polynomial.eval₂_one]
  rw [he, ← hs]
  linear_combination PowerSeries.C (1 / 5 : K) * lowHConicGermW ε *
      Polynomial.eval₂ PowerSeries.C (lowHConicGermT ε η ^ 2) (lowHOddHalfP P) * ht -
    lowHConicGermT ε η * lowHConicGermW ε * PowerSeries.derivative K (lowHConicGermT ε η) *
      Polynomial.eval₂ PowerSeries.C (lowHConicGermT ε η ^ 2) (lowHOddHalfP P) * hc

/-- The full primitive in the local w coordinate is composed before any residue is extracted. -/
theorem lowHConicGerm_polynomial_primitive (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (P : K[X]) (hdeg : P.natDegree ≤ p - 8)
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) (ε : Kˣ) :
    ∃ J : PowerSeries K, PowerSeries.derivative K J =
      Polynomial.aeval (lowHConicGermW ε) (lowHConicLocalP P) *
        PowerSeries.derivative K (lowHConicGermW ε) := by
  let I : K[X] := lowHIntegralP p (lowHConicLocalP P)
  have hder : I.derivative = lowHConicLocalP P := lowHIntegralP_derivative p hp _
    (by have := lowHConicLocalP_degree P hodd; omega)
  refine ⟨Polynomial.aeval (lowHConicGermW ε) I, ?_⟩
  have he := Derivation.comp_aeval_eq (a := lowHConicGermW ε) (PowerSeries.derivative K) I
  simpa only [hder, smul_eq_mul] using he

/-- The actual reciprocal denominator poles remain in Q; no finite surrogate replaces them. -/
theorem lowHConicGerm_full_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (P : K[X]) (hdeg : P.natDegree ≤ p - 8)
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) (ε : Kˣ) (Q : LaurentSeries K) :
    (Q ^ p * ((Polynomial.aeval (lowHConicGermW ε) (lowHConicLocalP P) *
      PowerSeries.derivative K (lowHConicGermW ε) : PowerSeries K) : LaurentSeries K)).coeff (-1) = 0 := by
  obtain ⟨J, hJ⟩ := lowHConicGerm_polynomial_primitive p hp P hdeg hodd ε
  rw [← hJ]
  exact lowH_regular_exact_series_residue p Q J

/-- This retains the actual moving reciprocal t/w and every additional full Frobenius multiplier. -/
theorem lowHConicGerm_reciprocal_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (P : K[X]) (hdeg : P.natDegree ≤ p - 8)
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0)
    (ε : Kˣ) (η : K) (hη : (5 : K) * η ^ 2 = 1) (B : LaurentSeries K) :
    ((((lowHConicGermT ε η : PowerSeries K) : LaurentSeries K) /
        ((lowHConicGermW ε : PowerSeries K) : LaurentSeries K) * B) ^ p *
      ((Polynomial.aeval (lowHConicGermT ε η) P * lowHConicGermW ε *
        PowerSeries.derivative K (lowHConicGermT ε η) : PowerSeries K) : LaurentSeries K)).coeff (-1) = 0 := by
  rw [lowHConicGerm_local_source p hp ε η hη P hodd]
  exact lowHConicGerm_full_residue p hp P hdeg hodd ε _

end WPFieldAssembly.ActualBpairContraction
