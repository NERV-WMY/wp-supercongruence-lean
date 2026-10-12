import WPFiniteJHighCoefficient

open Polynomial

namespace WPFiniteFifthSourceContraction

open WPFiniteNC122 WPFiniteJNormalization WPFiniteJHighCoefficient

variable {K : Type*} [Field K]

def k (p : ℕ) : K := (WPFiniteInversion.integerFermatQuotient p 5 : K)

private theorem fifth_phase_square (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) (hu : u ^ 2 = 1 / 5) : (u ^ p) ^ 2 = 1 / 5 := by
  have h5 : (5 : K) ^ p = 5 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 5
  calc
    _ = (u ^ 2) ^ p := by rw [← pow_mul, ← pow_mul, Nat.mul_comm p 2]
    _ = (1 / 5 : K) ^ p := by rw [hu]
    _ = 1 / 5 := by rw [div_pow, one_pow, h5]

theorem actual_a0_fifth (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    a0 p u = 11 * WPFifthEntropy.C p u / 5 - q p / 5 + 3 * (r p + k p) / 2 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have hT : (4 * u ^ 3 - 3 * u : K) = T0 u := by
    unfold T0
    rw [pow_succ, hu]
    field_simp [h5]
    ring
  have he := WPFiniteCubicLog.UW1_literal (K := K) p hp u
  rw [hT, WPFifthEntropy.E_at_double_fifth,
    WPFifthEntropy.E_at_fifth p hp u hu,
    WPFifthEntropy.O_at_fifth p hp u hu,
    WPFifthEntropy.O_at_double_fifth p hp u hu] at he
  unfold a0 L
  rw [show WPFiniteField.E p (T0 u) = (q p + WPFiniteField.E p (T0 u)) - q p by ring]
  rw [he]
  unfold h r k
  simp only [q]
  rw [show (u ^ p) ^ 2 = (1 / 5 : K) from fifth_phase_square p u hu]
  have hs := fifth_phase_square p u hu
  rw [← pow_mul] at hs
  field_simp [h5] at hs
  field_simp [h2, h5]
  linear_combination 20 * (3 * (WPFiniteInversion.integerFermatQuotient p 2 : K) + WPFifthEntropy.C p u) * hs

theorem actual_UJ_fifth (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    U_J p u = WPFiniteLoop.A p u - WPFiniteLoop.B p u + WPFiniteDReciprocity.At p u -
      WPFiniteDReciprocity.Bt p u + WPFiniteLoop.Chi p u - 2 * (WPFifthEntropy.C p u) ^ 2 +
      (4 * q p - 3 * r p) * (3 * k p / 2 - 18 * q p / 5 + 8 * WPFifthEntropy.C p u / 5) - 2 * (q p) ^ 2 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have hu0 : u ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by omega : (2 : ℕ) ≠ 0)] at hu
    exact (one_div_ne_zero h5) hu.symm
  rw [U_J_original_contraction p hp u hu0, WPFifthEntropy.E_at_double_fifth]
  simp only [add_sub_cancel_left]
  rw [WPFifthEntropy.E_at_fifth p hp u hu]
  unfold q k
  field_simp [h2, h5]
  ring

theorem original_KJ_attachment (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    (WPFiniteNC122Residue.canceledDensity (WPFiniteNC122Residue.bracketQ p (h p))).coeff 1 +
      JendpointFunctional p =
        2 * Aeven p (T0 u) - 4 * (a0 p u) ^ 2 / 3 +
          2 * (q p - h p) * a0 p u - 2 * (h p) ^ 2 / 3 + 2 * q p * h p - (q p) ^ 2 +
          77 * U_J p u / 75 := by
  rw [WPFiniteNC122Residue.actual_NC122_corrected_value p hp u hu]
  have he := actual_J_endpoint_attachment (K := K) p hp u hu
  rw [WPFiniteJSource.HJP_origin p hp u hu] at he
  linear_combination he

theorem original_KJ_fifth_contraction (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    (WPFiniteNC122Residue.canceledDensity (WPFiniteNC122Residue.bracketQ p (h p))).coeff 1 +
      JendpointFunctional p =
        2 * Aeven p (T0 u) -
          4 * (11 * WPFifthEntropy.C p u / 5 - q p / 5 + 3 * (r p + k p) / 2) ^ 2 / 3 +
          2 * (q p - h p) * (11 * WPFifthEntropy.C p u / 5 - q p / 5 + 3 * (r p + k p) / 2) -
          2 * (h p) ^ 2 / 3 + 2 * q p * h p - (q p) ^ 2 +
          77 * (WPFiniteLoop.A p u - WPFiniteLoop.B p u + WPFiniteDReciprocity.At p u -
            WPFiniteDReciprocity.Bt p u + WPFiniteLoop.Chi p u - 2 * (WPFifthEntropy.C p u) ^ 2 +
            (4 * q p - 3 * r p) * (3 * k p / 2 - 18 * q p / 5 + 8 * WPFifthEntropy.C p u / 5) -
            2 * (q p) ^ 2) / 75 := by
  rw [original_KJ_attachment p hp u hu, actual_a0_fifth p hp u hu, actual_UJ_fifth p hp u hu]

/-- Original JT1c strict high band: the invisible p coefficient is excluded. -/
noncomputable def strictHigh (p : ℕ) : K[X] :=
  highBand p (WPFiniteJSource.HJP p) - Polynomial.C ((WPFiniteJSource.HJP p).coeff p)

theorem strictHigh_coeff (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (j : ℕ) :
    (strictHigh p : K[X]).coeff j =
      if j = 0 then 0 else if j < p then (WPFiniteJSource.HJP p).coeff (p + j) else 0 := by
  rw [strictHigh, coeff_sub, highBand_coeff, coeff_C]
  by_cases hj : j = 0
  · subst j
    simp only [ite_true, if_pos (by omega : 0 < p), Nat.add_zero, sub_self]
  · simp only [if_neg hj, sub_zero]

/-- Full original JT3b finite functional, including both strict high endpoint terms. -/
noncomputable def JfullFunctional (p : ℕ) : K :=
  JendpointFunctional p + 16 * (strictHigh p : K[X]).eval (1 / 4) / 45 +
    8 * (strictHigh p : K[X]).eval 4 / 45

theorem full_J_endpoint_attachment (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    JfullFunctional p + 22 * (WPFiniteJSource.HJP p : K[X]).eval 0 / 15 =
      77 * U_J p u / 75 + 16 * (strictHigh p : K[X]).eval (1 / 4) / 45 +
        8 * (strictHigh p : K[X]).eval 4 / 45 := by
  unfold JfullFunctional
  linear_combination actual_J_endpoint_attachment (K := K) p hp u hu

theorem original_KJ_full_attachment (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    (WPFiniteNC122Residue.canceledDensity (WPFiniteNC122Residue.bracketQ p (h p))).coeff 1 +
      JfullFunctional p =
        2 * Aeven p (T0 u) -
          4 * (11 * WPFifthEntropy.C p u / 5 - q p / 5 + 3 * (r p + k p) / 2) ^ 2 / 3 +
          2 * (q p - h p) * (11 * WPFifthEntropy.C p u / 5 - q p / 5 + 3 * (r p + k p) / 2) -
          2 * (h p) ^ 2 / 3 + 2 * q p * h p - (q p) ^ 2 + 77 * U_J p u / 75 +
          16 * (strictHigh p : K[X]).eval (1 / 4) / 45 + 8 * (strictHigh p : K[X]).eval 4 / 45 := by
  unfold JfullFunctional
  have he := original_KJ_attachment (K := K) p hp u hu
  rw [actual_a0_fifth p hp u hu] at he
  linear_combination he

end WPFiniteFifthSourceContraction
