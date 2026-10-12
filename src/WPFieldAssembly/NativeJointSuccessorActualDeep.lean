import WPFieldAssembly.NativeJointSuccessorActualPhase
import WPFieldAssembly.NativeClosureMixedJDeepPhase
import WPFieldAssembly.ActualBpairMetric
import WPFieldAssembly.ActualRationalSignRows
import WPFieldAssembly.ActualBpairNativeTail

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.NativeJointSuccessorActualDeep

open ActualBpairContraction ActualCubicNativeSource NativeClosureMixedSource
open NativeJointSuccessorActualPhase NativeClosureMixedJDeepPhase

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

noncomputable def actualP2 (p : ℕ) : K[X] :=
  4 * actualCtilde p * WPFiniteWSource.squaredCoordinate ^ ((p - 1) / 2) *
    (actualU p).reflect ((p - 1) / 2 - 1)

noncomputable def actualP1 (p : ℕ) : K[X] :=
  actualCtilde p * WPFiniteWSource.squaredCoordinate ^ ((p - 1) / 2) *
    (4 * (actualV p).reflect (p - 1) +
      Polynomial.C (4 * (4 * nativeConstant p / 3 - WPFiniteNC122.q p + WPFiniteNC122.h p)) *
        X ^ (p - 1) - 11 * X ^ ((p - 1) / 2 + 1) *
          (actualU p).reflect ((p - 1) / 2 - 1))

noncomputable def actualPpos (p : ℕ) : K[X] :=
  -Polynomial.C (11 / 3 : K) * X ^ ((p - 1) / 2 + 2) * actualCtilde p *
    WPFiniteWSource.squaredCoordinate ^ ((p - 1) / 2) * actualU p

private theorem reflect_toLaurent (n : ℕ) (P : K[X]) (hP : P.natDegree ≤ n) :
    (P.reflect n).toLaurent = T (n : ℤ) * invert P.toLaurent := by
  refine induction_with_natDegree_le
    (fun P : K[X] => (P.reflect n).toLaurent = T (n : ℤ) * invert P.toLaurent)
    n ?_ ?_ ?_ P hP
  · simp
  · intro j c _ hj
    rw [reflect_C_mul_X_pow, revAt_le hj]
    simp only [map_mul, map_pow, Polynomial.toLaurent_C, Polynomial.toLaurent_X,
      T_pow, invert_C, invert_T, mul_one]
    rw [show ((n - j : ℕ) : ℤ) = (n : ℤ) + -(j : ℤ) by omega, T_add]
    ring
  · intro P Q _ _ hP hQ
    rw [reflect_add, map_add, hP, hQ]
    simp only [map_add, mul_add]

private theorem squaredCoordinate_degree :
    (WPFiniteWSource.squaredCoordinate : K[X]).natDegree ≤ 1 := by
  unfold WPFiniteWSource.squaredCoordinate
  compute_degree

private theorem reciprocal_polynomial_evaluation (P : K[X]) (a : K) (ha : a ≠ 0) :
    GreenLaurentOperators.ev a ha (invert P.toLaurent) = P.eval a⁻¹ := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [map_add, map_add, map_add, hP, hQ, eval_add]
  | monomial n c =>
      rw [← C_mul_X_pow_eq_monomial]
      simp [map_mul, map_pow, Polynomial.toLaurent_C, Polynomial.toLaurent_X,
        invert_C, invert_T, GreenLaurentOperators.ev]

private theorem reflection_evaluation (n : ℕ) (P : K[X]) (hP : P.natDegree ≤ n)
    (a : K) (ha : a ≠ 0) :
    (P.reflect n).eval a = a ^ n * P.eval a⁻¹ := by
  have he := congrArg (GreenLaurentOperators.ev a ha) (reflect_toLaurent n P hP)
  rw [map_mul, reciprocal_polynomial_evaluation P a ha] at he
  simpa [GreenLaurentOperators.ev, LaurentPolynomial.eval₂_toLaurent] using he

/-- The first original block has no regular coefficient after its entire shift. -/
theorem actual_P2_strict_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualP2 p : K[X]).natDegree < 3 * p - 3 := by
  have hu : ((actualU p : K[X]).reflect ((p - 1) / 2 - 1)).natDegree ≤
      (p - 1) / 2 - 1 :=
    natDegree_reflect_le.trans (max_le (le_refl _) (actual_U_degree p hp))
  have hs : (WPFiniteWSource.squaredCoordinate ^ ((p - 1) / 2) : K[X]).natDegree ≤
      (p - 1) / 2 := by
    exact (natDegree_pow_le.trans (Nat.mul_le_mul_left _ squaredCoordinate_degree)).trans_eq
      (Nat.mul_one _)
  unfold actualP2
  exact (natDegree_mul_le_of_le
    (natDegree_mul_le_of_le ((natDegree_C_mul_le _ _).trans (actual_Ctilde_degree p hp)) hs)
    hu).trans_lt (by omega)

/-- The second original block is strictly negative, including its inclusive p band. -/
theorem actual_P1_strict_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualP1 p : K[X]).natDegree < 2 * p + (p - 1) / 2 - 2 := by
  have hu : ((actualU p : K[X]).reflect ((p - 1) / 2 - 1)).natDegree ≤
      (p - 1) / 2 - 1 :=
    natDegree_reflect_le.trans (max_le (le_refl _) (actual_U_degree p hp))
  have hv : ((actualV p : K[X]).reflect (p - 1)).natDegree ≤ p - 1 :=
    natDegree_reflect_le.trans (max_le (le_refl _) (actual_V_degree p hp))
  have hs : (WPFiniteWSource.squaredCoordinate ^ ((p - 1) / 2) : K[X]).natDegree ≤
      (p - 1) / 2 := by
    exact (natDegree_pow_le.trans (Nat.mul_le_mul_left _ squaredCoordinate_degree)).trans_eq
      (Nat.mul_one _)
  have hlast : (11 * X ^ ((p - 1) / 2 + 1) *
      (actualU p).reflect ((p - 1) / 2 - 1) : K[X]).natDegree ≤ p - 1 := by
    have hx : (11 * X ^ ((p - 1) / 2 + 1) : K[X]).natDegree ≤ (p - 1) / 2 + 1 :=
      (natDegree_C_mul_le _ _).trans (by simp)
    exact (natDegree_mul_le_of_le hx hu).trans
      (by have := WPFiniteWSource.half_exponent p hp; omega)
  unfold actualP1
  exact (natDegree_mul_le_of_le
    (natDegree_mul_le_of_le (actual_Ctilde_degree p hp) hs)
    ((natDegree_sub_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hv)
        ((natDegree_C_mul_le _ _).trans (by simp)))) hlast))).trans_lt (by omega)

/-- The actual window defect is the whole three-block numerator, before taking any residue. -/
theorem actual_Nj_window_three_blocks (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p) -
        T (-(((p - 1) / 2 - 1 : ℕ) : ℤ)) * (actualCtilde p).toLaurent * actualRWindow p =
      deepPhaseNumerator (3 * p - 3) (2 * p + (p - 1) / 2 - 2)
        (actualP2 p) (actualP1 p) (actualPpos p) := by
  let N := (p - 1) / 2
  have hpN : p = 2 * N + 1 := WPFiniteWSource.half_exponent p hp
  have h2 : (T (-((3 * p - 3 : ℕ) : ℤ)) * T ((N - 1 : ℕ) : ℤ) : K[T;T⁻¹]) =
      T (-((N - 1 : ℕ) : ℤ)) * T (-2 * (p : ℤ)) := by
    rw [← T_add, ← T_add]
    congr 1
    omega
  have h1 : (T (-((2 * p + N - 2 : ℕ) : ℤ)) * T ((p - 1 : ℕ) : ℤ) : K[T;T⁻¹]) =
      T (-((N - 1 : ℕ) : ℤ)) * T (-(p : ℤ)) := by
    rw [← T_add, ← T_add]
    congr 1
    omega
  have hu : (T ((N + 1 : ℕ) : ℤ) * T ((N - 1 : ℕ) : ℤ) : K[T;T⁻¹]) =
      T ((p - 1 : ℕ) : ℤ) := by
    rw [← T_add]
    congr 1
    omega
  have hpos : (T ((N + 2 : ℕ) : ℤ) : K[T;T⁻¹]) =
      T (-((N - 1 : ℕ) : ℤ)) * T (p : ℤ) := by
    rw [← T_add]
    congr 1
    omega
  rw [actual_Nj_factor p hp, ← mul_sub, actual_R_window_difference p hp]
  simp only [deepPhaseNumerator, actualP2, actualP1, actualPpos, map_add, map_sub,
    map_mul, map_neg, map_pow, map_ofNat, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, T_pow, mul_one,
    reflect_toLaurent _ _ (actual_U_degree p hp),
    reflect_toLaurent _ _ (actual_V_degree p hp)]
  dsimp only [N] at h2 h1 hu hpos
  linear_combination (norm := skip) -4 * (actualCtilde p).toLaurent *
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * invert (actualU p).toLaurent * h2 -
    (actualCtilde p).toLaurent * WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
      (4 * invert (actualV p).toLaurent + LaurentPolynomial.C
        (4 * (4 * nativeConstant p / 3 - WPFiniteNC122.q p + WPFiniteNC122.h p)) -
          11 * invert (actualU p).toLaurent) * h1 +
    11 * T (-((2 * p + (p - 1) / 2 - 2 : ℕ) : ℤ)) * (actualCtilde p).toLaurent *
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * invert (actualU p).toLaurent * hu +
    LaurentPolynomial.C (11 / 3 : K) * (actualCtilde p).toLaurent *
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * (actualU p).toLaurent * hpos
  simp only [map_add, map_sub, map_mul, map_ofNat]
  ring

/-- Both endpoint weights come from the original branch quotient and full Ctilde. -/
theorem actual_Ctilde_endpoints (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualCtilde p : K[X]).eval (1 / 4) = -16 * WPFiniteNC122.h p ∧
      (actualCtilde p : K[X]).eval 4 = -WPFiniteNC122.h p / 4 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 6
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4m : (4 : K) ^ ((p - 1) / 2 - 1) = 1 / 4 := by
    apply mul_right_cancel₀ h4
    rw [← pow_succ, show (p - 1) / 2 - 1 + 1 = (p - 1) / 2 by omega,
      WPFiniteWSource.four_half_power p hp, one_div_mul_cancel h4]
  have ham : (1 / 4 : K) ^ ((p - 1) / 2 - 1) = 4 := by
    rw [one_div, inv_pow, h4m]
    simp only [one_div, inv_inv]
  obtain ⟨hBa, hBb⟩ := branchPolynomial_metric_endpoints (K := K) p hp
  obtain ⟨hDa, hDb⟩ := Dstar_endpoints (K := K) p hp
  rw [hDa, hDb] at hBa hBb
  constructor
  · simp only [actualCtilde, WPFiniteWSource.squaredCoordinate, eval_sub, eval_mul,
      eval_C, eval_ofNat, eval_add, eval_X, eval_one, eval_pow, ham, hBa]
    field_simp [h3, h4, h5, h6]
    ring
  · simp only [actualCtilde, WPFiniteWSource.squaredCoordinate, eval_sub, eval_mul,
      eval_C, eval_ofNat, eval_add, eval_X, eval_one, eval_pow, h4m, hBb]
    field_simp [h3, h4, h5, h6]
    ring

/-- The whole negative shifts have their actual endpoint phases, with no fifth-power premise. -/
theorem actual_deep_endpoint_phases (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (4 : K) ^ (-((3 * p - 3 : ℕ) : ℤ)) = 1 ∧
      (4 : K) ^ (-((2 * p + (p - 1) / 2 - 2 : ℕ) : ℤ)) = 1 ∧
      (1 / 4 : K) ^ (-((3 * p - 3 : ℕ) : ℤ)) = 1 ∧
      (1 / 4 : K) ^ (-((2 * p + (p - 1) / 2 - 2 : ℕ) : ℤ)) = 1 := by
  have hpN := WPFiniteWSource.half_exponent p hp
  have hn2 : 3 * p - 3 = (p - 1) / 2 * 6 := by omega
  have hn1 : 2 * p + (p - 1) / 2 - 2 = (p - 1) / 2 * 5 := by omega
  have hNa : (1 / 4 : K) ^ ((p - 1) / 2) = 1 := by
    rw [one_div, inv_pow, WPFiniteWSource.four_half_power p hp, inv_one]
  simp only [hn2, hn1, zpow_neg, zpow_natCast, pow_mul,
    WPFiniteWSource.four_half_power p hp, hNa, one_pow, inv_one, and_self]

/-- The two cleared blocks retain their literal swapped endpoints and all constants. -/
theorem actual_deep_block_endpoints (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualP2 p : K[X]).eval (1 / 4) =
        -256 * WPFiniteNC122.h p * (actualU p).eval 4 ∧
      (actualP2 p : K[X]).eval 4 =
        -WPFiniteNC122.h p * (actualU p).eval (1 / 4) / 4 ∧
      (actualP1 p : K[X]).eval (1 / 4) =
        -16 * WPFiniteNC122.h p * (4 * (actualV p).eval 4 +
          4 * (4 * nativeConstant p / 3 - WPFiniteNC122.q p + WPFiniteNC122.h p) -
            11 * (actualU p).eval 4) ∧
      (actualP1 p : K[X]).eval 4 =
        -WPFiniteNC122.h p * (4 * (actualV p).eval (1 / 4) +
          4 * (4 * nativeConstant p / 3 - WPFiniteNC122.q p + WPFiniteNC122.h p) -
            11 * (actualU p).eval (1 / 4)) / 4 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hpN := WPFiniteWSource.half_exponent p hp
  have hNb := WPFiniteWSource.four_half_power (K := K) p hp
  have hNa : (1 / 4 : K) ^ ((p - 1) / 2) = 1 := by
    rw [one_div, inv_pow, hNb, inv_one]
  have hbm : (4 : K) ^ ((p - 1) / 2 - 1) = 1 / 4 := by
    apply mul_right_cancel₀ h4
    rw [← pow_succ, show (p - 1) / 2 - 1 + 1 = (p - 1) / 2 by omega,
      hNb, one_div_mul_cancel h4]
  have ham : (1 / 4 : K) ^ ((p - 1) / 2 - 1) = 4 := by
    rw [one_div, inv_pow, hbm]
    simp only [one_div, inv_inv]
  have hpm : p - 1 = (p - 1) / 2 * 2 := by omega
  have hpa : (1 / 4 : K) ^ (p - 1) = 1 := by rw [hpm, pow_mul, hNa, one_pow]
  have hpb : (4 : K) ^ (p - 1) = 1 := by rw [hpm, pow_mul, hNb, one_pow]
  have hsa : (WPFiniteWSource.squaredCoordinate : K[X]).eval (1 / 4) = 1 / 4 := by
    simp only [WPFiniteWSource.squaredCoordinate, eval_mul, eval_C, eval_add, eval_X, eval_one]
    field_simp [h4, h5]
    ring
  have hsb : (WPFiniteWSource.squaredCoordinate : K[X]).eval 4 = 1 := by
    simp only [WPFiniteWSource.squaredCoordinate, eval_mul, eval_C, eval_add, eval_X, eval_one]
    field_simp [h5]
    ring
  have hUa := reflection_evaluation _ (actualU p) (actual_U_degree p hp)
    (1 / 4 : K) (one_div_ne_zero h4)
  have hUb := reflection_evaluation _ (actualU p) (actual_U_degree p hp) (4 : K) h4
  have hVa := reflection_evaluation _ (actualV p) (actual_V_degree p hp)
    (1 / 4 : K) (one_div_ne_zero h4)
  have hVb := reflection_evaluation _ (actualV p) (actual_V_degree p hp) (4 : K) h4
  have hia : (1 / 4 : K)⁻¹ = 4 := by simp only [one_div, inv_inv]
  have hib : (4 : K)⁻¹ = 1 / 4 := by rw [one_div]
  rw [ham, hia] at hUa
  rw [hbm, hib] at hUb
  rw [hpa, one_mul, hia] at hVa
  rw [hpb, one_mul, hib] at hVb
  obtain ⟨hCa, hCb⟩ := actual_Ctilde_endpoints (K := K) p hp
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [actualP2, actualP1, eval_mul, eval_ofNat, eval_C, eval_add, eval_sub,
      eval_X, eval_pow, hCa, hCb, hsa, hsb, hNa, one_pow, hUa, hUb, hVa, hVb,
      hpa, hpb, pow_succ, hNb]
  all_goals field_simp [h4]
  all_goals ring

theorem actual_two_band_endpoints (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualU p : K[X]).eval (1 / 4) / 4 + (actualV p).eval (1 / 4) + nativeConstant p =
        -WPFiniteNC122.h p ∧
      4 * (actualU p : K[X]).eval 4 + (actualV p).eval 4 + nativeConstant p =
        -WPFiniteNC122.h p := by
  have hpb : (4 : K) ^ p = 4 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 4
  have hpa : (1 / 4 : K) ^ p = 1 / 4 := by rw [one_div, inv_pow, hpb]
  obtain ⟨hAa, hAb⟩ := ActualBpairNativeTail.actual_AK_endpoints (K := K) p hp
  have ha := congrArg (fun P : K[X] => P.eval (1 / 4)) (actual_A_two_bands (K := K) p hp)
  have hb := congrArg (fun P : K[X] => P.eval 4) (actual_A_two_bands (K := K) p hp)
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, hpa, hAa] at ha
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, hpb, hAb] at hb
  constructor
  · calc
      _ = (1 / 4 : K) * (actualU p).eval (1 / 4) +
          (actualV p).eval (1 / 4) + nativeConstant p := by ring
      _ = _ := ha.symm
  · exact hb.symm

/-- This is the entire phase correction for the actual origin-pole detector. -/
theorem actual_deep_phase_correction (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    ActualSimplePoleResidue.originPole
      (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p) -
        T (-(((p - 1) / 2 - 1 : ℕ) : ℤ)) * (actualCtilde p).toLaurent * actualRWindow p) =
      WPFiniteNC122.h p * (1083 * WPFiniteNC122.q p / 5 -
        3627 * ActualRationalSignRows.q3 p / 20 +
          63 * (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2) / 15 := by
  obtain ⟨hAa, hAb⟩ := actual_two_band_endpoints (K := K) p hp
  obtain ⟨h2a, h2b, h1a, h1b⟩ := actual_deep_block_endpoints (K := K) p hp
  obtain ⟨hph2b, hph1b, hph2a, hph1a⟩ := actual_deep_endpoint_phases (K := K) p hp
  rw [actual_Nj_window_three_blocks p hp]
  have hc := deep_phase_correction_from_two_band p hp
    (3 * p - 3) (2 * p + (p - 1) / 2 - 2) (actualP2 p) (actualP1 p) (actualPpos p)
    (actual_P2_strict_degree p hp) (actual_P1_strict_degree p hp)
    ((actualU p).eval (1 / 4)) ((actualU p).eval 4)
    ((actualV p).eval (1 / 4)) ((actualV p).eval 4) (nativeConstant p)
    (WPFiniteNC122.h p) (WPFiniteNC122.q p) hAa hAb
    (by rw [hph2a, hph1a, h2a, h1a]; simp only [one_mul]; ring)
    (by rw [hph2b, hph1b, h2b, h1b]; simp only [one_mul]; ring)
  rw [hc]
  obtain ⟨hDa, hDb⟩ := Dstar_endpoints (K := K) p hp
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 6
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h20 : (20 : K) ≠ 0 := by
    rw [show (20 : K) = 4 * 5 by ring]
    exact mul_ne_zero h4 h5
  simp only [actualU, eval_sub, eval_mul, eval_C, hDa, hDb, nativeConstant]
  dsimp only [WPFiniteNC122.h, WPFiniteNC122.q, ActualRationalSignRows.q3]
  field_simp [h2, h3, h4, h5, h6, h15, h20]
  ring

end WPFieldAssembly.NativeJointSuccessorActualDeep
