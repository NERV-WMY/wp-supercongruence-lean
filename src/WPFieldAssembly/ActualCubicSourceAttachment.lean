import WPFieldAssembly.ActualCubicFiniteSource
import WPFieldAssembly.ActualSB72Finite
import WPFiniteLVSource

open scoped Polynomial
open Polynomial WPFiniteAffineLog WPFiniteKSource WPFiniteCubicLog
  WPFiniteJHighCoefficient WPFiniteWSource WPFiniteLVSource
  WPFieldAssembly.ActualCubicFiniteSource WPFieldAssembly.ActualBpairContraction

namespace WPFieldAssembly.ActualCubicSourceAttachment

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

private theorem conic_injective (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (P Q : K[X]) (h : P.comp conic = Q.comp conic) : P = Q := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hdeg : (conic : K[X]).natDegree = 2 := by
    unfold conic
    change (C (5 : K) * X ^ 2 - 1).natDegree = 2
    compute_degree
    exact h5
  have hz : (P - Q).comp conic = 0 := by rw [sub_comp, h, sub_self]
  apply sub_eq_zero.mp
  rcases Polynomial.comp_eq_zero_iff.mp hz with hz | ⟨_, hc⟩
  · exact hz
  · have hd := congrArg Polynomial.natDegree hc
    rw [hdeg, natDegree_C] at hd
    omega

private theorem C_five_fraction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (c : K) : (5 : K[X]) * C (c / 5) = C c := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  change C (5 : K) * C (c / 5) = C c
  rw [← C_mul]
  congr 1
  field_simp [h5]

/-- The original cubic LV source descends with every Frobenius coefficient retained. -/
theorem LV_cubic_entropy_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (LV p : K[X]) =
      C (3 / 5 : K) * (4 * X ^ p - 11) * Dstar p +
        2 * (LP p).comp squaredCoordinate -
        C (1 / 2 : K) * (LP p).comp (4 * squaredCoordinate) -
        C (4 * WPFiniteNC122.q p / 5) * X ^ p + C (WPFiniteNC122.q p / 5) := by
  apply conic_injective p hp
  have h5p : (5 : K[X]) ^ p = 5 := by
    change C (5 : K) ^ p = C (5 : K)
    rw [← map_pow]
    congr 1
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 5
  have hc : (conic : K[X]) ^ p = 5 * (X ^ p) ^ 2 - 1 := by
    rw [conic, sub_pow_char (p := p), mul_pow, h5p, one_pow,
      ← pow_mul, Nat.mul_comm 2 p, pow_mul]
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h3unit : (3 : K[X]) * C (1 / 3 : K) = 1 := by
    change C (3 : K) * C (1 / 3 : K) = C (1 : K)
    rw [← C_mul]
    congr 1
    field_simp [h3]
  have hD : (3 : K[X]) * (Dstar p).comp conic = EP p - (EP p).comp (2 * X) := by
    rw [Dstar, mul_comp, neg_comp, C_comp, comp_assoc,
      squaredCoordinate_conic p hp, deltaE_square p hp]
    linear_combination -((EP p).comp (2 * X) - EP p) * h3unit
  have hcu := cubic_even_entropy_polynomial (K := K) p hp
  have ha := C_five_fraction (K := K) p hp 3
  have hb := C_five_fraction (K := K) p hp (4 * WPFiniteNC122.q p)
  have hd := C_five_fraction (K := K) p hp (WPFiniteNC122.q p)
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h5C : (5 : K[X]) ≠ 0 := by
    change C (5 : K) ≠ 0
    exact C_ne_zero.mpr h5
  apply mul_left_cancel₀ h5C
  rw [LV_conic p hp, LPsrc, add_comp, C_comp]
  simp only [add_comp, sub_comp, mul_comp, ofNat_comp, C_comp, pow_comp,
    X_comp, comp_assoc, squaredCoordinate_conic p hp, hc]
  simp only [map_mul, map_ofNat] at ha hb hcu ⊢
  linear_combination 5 * hcu - 5 * (4 * (X ^ p) ^ 2 - 3) * hD -
    5 * (4 * (X ^ p) ^ 2 - 3) * (Dstar p).comp conic * ha +
      (5 * (X ^ p) ^ 2 - 1) * hb - hd

noncomputable def affineEntropyPair (p : ℕ) : K[X] :=
  2 * (LP p).comp squaredCoordinate -
    C (1 / 2 : K) * (LP p).comp (4 * squaredCoordinate)

/-- The complete cubic source determines the affine entropy derivative. -/
theorem affineEntropyPair_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]) * (affineEntropyPair p).derivative =
      6 * (X - X ^ p) := by
  have hs : (LV p : K[X]) = C (3 / 5 : K) * (4 * X ^ p - 11) * Dstar p +
      affineEntropyPair p - C (4 * WPFiniteNC122.q p / 5) * X ^ p +
        C (WPFiniteNC122.q p / 5) := by
    dsimp only [affineEntropyPair]
    linear_combination LV_cubic_entropy_source (K := K) p hp
  have hder := congrArg Polynomial.derivative hs
  have hp0 : (p : K) = 0 := CharP.cast_eq_zero K p
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_C,
    derivative_ofNat, derivative_X_pow, hp0, map_zero, zero_mul,
    mul_zero, zero_add, add_zero, sub_zero] at hder
  have hLV := LV_cleared_source (K := K) p hp
  change (WPFiniteZSource.Abar : K[X]) * (LV p).derivative = _ at hLV
  have hD := Dstar_cleared_source (K := K) p hp
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hscalar : (C (3 / 5 : K) : K[X]) * C (5 / 2 : K) = C (3 / 2 : K) := by
    rw [← C_mul]
    congr 1
    field_simp [h2, h5]
  have hscalar4 : (4 : K[X]) * C (3 / 2 : K) = 6 := by
    change C (4 : K) * C (3 / 2 : K) = C (6 : K)
    rw [← C_mul]
    congr 1
    field_simp [h2]; ring
  linear_combination hLV - C (3 / 5 : K) * (4 * X ^ p - 11) * hD -
    (WPFiniteZSource.Abar : K[X]) * hder -
      (4 * X ^ p - 11) * (1 - squaredCoordinate ^ ((p - 1) / 2)) * hscalar +
        (X - X ^ p) * hscalar4

private theorem LP_scaled_degree (p : ℕ) (U : K[X]) (hU : U.natDegree ≤ 1) :
    ((LP p).comp U : K[X]).natDegree ≤ p - 1 :=
  natDegree_comp_le.trans ((Nat.mul_le_mul (LP_natDegree_le p) hU).trans (by simp))

private theorem LP_zero (p : ℕ) : (LP p : K[X]).eval 0 = 0 := by
  rw [LP, eval_finsetSum]
  apply Finset.sum_eq_zero
  intro j hj
  have hj0 : j ≠ 0 := by have := (Finset.mem_Ico.mp hj).1; omega
  simp only [eval_mul, eval_C, eval_pow, eval_X, zero_pow hj0, mul_zero]

private theorem pair_degree (p : ℕ) : (affineEntropyPair p : K[X]).natDegree ≤ p - 1 := by
  have hs : (squaredCoordinate : K[X]).natDegree ≤ 1 := by
    unfold squaredCoordinate
    exact natDegree_C_mul_le _ _ |>.trans ((natDegree_add_le _ _).trans (by simp))
  have h4s : (4 * squaredCoordinate : K[X]).natDegree ≤ 1 := by
    change (C (4 : K) * squaredCoordinate).natDegree ≤ 1
    exact (natDegree_C_mul_le _ _).trans hs
  unfold affineEntropyPair
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · change (C (2 : K) * (LP p).comp squaredCoordinate).natDegree ≤ p - 1
    exact (natDegree_C_mul_le _ _).trans (LP_scaled_degree p _ hs)
  · exact (natDegree_C_mul_le _ _).trans (LP_scaled_degree p _ h4s)

private theorem affinePair_origin (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (affineEntropyPair p : K[X]).eval 0 =
      3 * (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 -
        12 * WPFiniteNC122.q p / 5 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hs0 : (squaredCoordinate : K[X]).eval 0 = 1 / 5 := by simp [squaredCoordinate]
  have h4s0 : (4 * squaredCoordinate : K[X]).eval 0 = 4 / 5 := by
    simp only [eval_mul, eval_ofNat, hs0]
    ring
  have href : WPFiniteField.ell p (4 / 5 : K) = WPFiniteField.ell p (1 / 5) := by
    have he := WPFiniteField.ell_reflection p (by omega : 3 ≤ p) (1 / 5 : K)
    have hh : (1 - 1 / 5 : K) = 4 / 5 := by field_simp [h5]; ring
    rw [hh] at he
    exact he
  rw [affineEntropyPair, eval_sub, eval_mul, eval_ofNat, eval_comp, hs0,
    eval_mul, eval_C, eval_comp, h4s0, LP_eval_eq, LP_eval_eq, href,
    WPFiniteField.ell_one_fifth_eq_fermat p hp]
  unfold WPFiniteNC122.q
  field_simp [h2, h5]; ring

/-- IR70 fixes the whole degree-p-1 affine pair by its actual origin Fermat quotient. -/
theorem affineEntropyPair_endLog (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (affineEntropyPair p : K[X]) =
      C (2 / 5 : K) * WPFiniteABSourceTail.logTrace p +
        C (3 * (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 -
          12 * WPFiniteNC122.q p / 5) := by
  let c : K := 3 * (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 -
    12 * WPFiniteNC122.q p / 5
  let Q : K[X] := affineEntropyPair p -
    C (2 / 5 : K) * WPFiniteABSourceTail.logTrace p - C c
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hscalar : (C (2 / 5 : K) : K[X]) * 15 = 6 := by
    change C (2 / 5 : K) * C (15 : K) = C (6 : K)
    rw [← C_mul]
    congr 1
    field_simp [h5]; ring
  have hT := WPFinitePSource.logTrace_cleared_source (K := K) p hp
  change (WPFiniteZSource.Abar : K[X]) *
    (WPFiniteABSourceTail.logTrace p).derivative = _ at hT
  have hxp : (X : K[X]) * X ^ (p - 1) = X ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
  have hTs : (WPFiniteZSource.Abar : K[X]) *
      (C (2 / 5 : K) * WPFiniteABSourceTail.logTrace p).derivative =
        6 * (X - X ^ p) := by
    rw [derivative_mul, derivative_C, zero_mul, zero_add]
    linear_combination C (2 / 5 : K) * hT +
      X * (1 - X ^ (p - 1)) * hscalar - 6 * hxp
  have hA : (WPFiniteZSource.Abar : K[X]) ≠ 0 := by
    intro hz
    apply WPFiniteZSource.Abar_nonzero (K := K) p hp
    rw [hz, map_zero]
  have hder : Q.derivative = 0 := by
    apply (mul_eq_zero.mp (show (WPFiniteZSource.Abar : K[X]) * Q.derivative = 0 by
      dsimp only [Q]
      rw [derivative_sub, derivative_sub, derivative_C, sub_zero]
      linear_combination affineEntropyPair_cleared_source (K := K) p hp - hTs)).resolve_left hA
  have hdeg : Q.natDegree < p := by
    have hsc : (C (2 / 5 : K) * WPFiniteABSourceTail.logTrace p).natDegree ≤ p - 1 :=
      (natDegree_C_mul_le _ _).trans (WPFiniteABSourceTail.logTrace_degree p)
    have hQ := (natDegree_sub_le _ _).trans (max_le
      ((natDegree_sub_le _ _).trans (max_le (pair_degree (K := K) p) hsc))
      (show (C c : K[X]).natDegree ≤ p - 1 by simp))
    change (affineEntropyPair p - C (2 / 5 : K) *
      WPFiniteABSourceTail.logTrace p - C c).natDegree < p
    omega
  have h0 : Q.eval 0 = 0 := by
    dsimp only [Q, c]
    rw [eval_sub, eval_sub, affinePair_origin p hp, eval_mul, eval_C, eval_C]
    simp only [WPFiniteABSourceTail.logTrace, eval_add, eval_mul, eval_neg,
      eval_C, eval_comp, eval_X, mul_zero, LP_zero, zero_add, sub_zero]
    ring
  have hs := derivative_support_three p Q (hdeg.trans (by omega : p < 3 * p)) hder
  have hc0 : Q.coeff 0 = 0 := by simpa only [coeff_zero_eq_eval_zero] using h0
  have hcp : Q.coeff p = 0 := coeff_eq_zero_of_natDegree_lt hdeg
  have hc2p : Q.coeff (2 * p) = 0 := coeff_eq_zero_of_natDegree_lt (hdeg.trans_le (by omega))
  simp only [hc0, hcp, hc2p, C_0, zero_mul, zero_add] at hs
  dsimp only [Q, c] at hs
  linear_combination hs

/-- NC126a's whole two-band source, before any tail or quadratic projection. -/
theorem LV_two_band_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (LV p : K[X]) =
      X ^ p * (C (12 / 5 : K) * Dstar p - C (4 * WPFiniteNC122.q p / 5)) -
        C (33 / 5 : K) * Dstar p + C (2 / 5 : K) * WPFiniteABSourceTail.logTrace p +
          C (3 * (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 -
            11 * WPFiniteNC122.q p / 5) := by
  have hc := LV_cubic_entropy_source (K := K) p hp
  have he := affineEntropyPair_endLog (K := K) p hp
  dsimp only [affineEntropyPair] at he
  simp only [div_eq_mul_inv, map_mul, map_sub, map_ofNat] at hc he ⊢
  linear_combination hc + he

end WPFieldAssembly.ActualCubicSourceAttachment
