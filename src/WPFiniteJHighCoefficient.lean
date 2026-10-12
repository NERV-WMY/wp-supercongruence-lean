import WPFiniteCubicJ

open scoped BigOperators
open Polynomial

namespace WPFiniteJHighCoefficient

open WPFiniteAffineLog WPFiniteKSource WPFiniteDSource WPFiniteJSource
  WPFiniteJNormalization WPFiniteCubicLog WPFiniteCubicJ

variable {K : Type*} [Field K]

noncomputable def lowBand (n : ℕ) (P : K[X]) : K[X] :=
  ∑ j ∈ Finset.range n, C (P.coeff j) * X ^ j

noncomputable def highBand (n : ℕ) (P : K[X]) : K[X] :=
  ∑ j ∈ Finset.range n, C (P.coeff (n + j)) * X ^ j

theorem lowBand_coeff (n : ℕ) (P : K[X]) (j : ℕ) :
    (lowBand n P).coeff j = if j < n then P.coeff j else 0 := by
  simp [lowBand]

theorem highBand_coeff (n : ℕ) (P : K[X]) (j : ℕ) :
    (highBand n P).coeff j = if j < n then P.coeff (n + j) else 0 := by
  simp [highBand]

theorem full_cutoff_split (n : ℕ) (P : K[X]) (hP : P.natDegree < 2 * n) :
    P = lowBand n P + X ^ n * highBand n P := by
  ext j
  rw [coeff_add, lowBand_coeff, coeff_X_pow_mul', highBand_coeff]
  by_cases hj : j < n
  · simp only [if_pos hj, if_neg (show ¬n ≤ j by omega), add_zero]
  · rw [if_neg hj, if_pos (show n ≤ j by omega), zero_add]
    by_cases hhigh : j < 2 * n
    · rw [if_pos (show j - n < n by omega), Nat.add_sub_of_le (by omega : n ≤ j)]
    · rw [if_neg (show ¬j - n < n by omega)]
      exact coeff_eq_zero_of_natDegree_lt (hP.trans_le (by omega))

theorem cutoff_band_degree (n : ℕ) (P : K[X]) :
    (lowBand n P).natDegree ≤ n - 1 ∧ (highBand n P).natDegree ≤ n - 1 := by
  constructor
  · unfold lowBand
    apply natDegree_sum_le_of_forall_le
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact (natDegree_C_mul_le _ _).trans (by simpa using (show j ≤ n - 1 by omega))
  · unfold highBand
    apply natDegree_sum_le_of_forall_le
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact (natDegree_C_mul_le _ _).trans (by simpa using (show j ≤ n - 1 by omega))

theorem shifted_low_unique (n : ℕ) (A B : K[X]) (hB : B.natDegree < n)
    (h : X ^ n * A + B = 0) : A = 0 := by
  ext j
  have he := congrArg (fun P : K[X] => P.coeff (j + n)) h
  rw [coeff_add, coeff_X_pow_mul, coeff_zero,
    coeff_eq_zero_of_natDegree_lt (hB.trans_le (by omega)), add_zero] at he
  exact he

noncomputable def conic : K[X] := 5 * X ^ 2 - 1

noncomputable def UJP (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  X ^ p * FbP p + FdP p + MEP p - C (K_J p)

noncomputable def VJP (p : ℕ) : K[X] := X ^ p * (FeP p + MOP p)

theorem HJP_conic_pullback (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (HJP p : K[X]).comp conic = X ^ p * (JLP p).comp Tc := by
  have hpn : p = 2 * ((p - 1) / 2) + 1 := by
    obtain ⟨a, ha⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    omega
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have hu : (C (5 : K)⁻¹ : K[X]) * 5 = 1 := by
    change C (5 : K)⁻¹ * C (5 : K) = 1
    rw [← C_mul, inv_mul_cancel₀ h5, C_1]
  have hs : (C (5 : K)⁻¹ * (X + 1) : K[X]).comp conic = X ^ 2 := by
    simp only [mul_comp, C_comp, add_comp, X_comp, one_comp, conic]
    linear_combination X ^ 2 * hu
  have hb : (4 * X - 11 : K[X]).comp conic = 5 * (4 * X ^ 2 - 3) := by
    simp only [sub_comp, mul_comp, X_comp, ofNat_comp, conic]
    ring
  have ht : (Tc : K[X]) = X * (4 * X ^ 2 - 3) := by unfold Tc; ring
  rw [JLP_eq_harmonic p hp]
  unfold HJP JHP
  simp only [sum_comp, mul_comp, C_comp, pow_comp, hs, hb, X_comp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hpow : (X ^ 2 : K[X]) ^ ((p - 1) / 2 + j + 1) = X ^ p * X ^ (2 * j + 1) := by
    rw [← pow_mul, show 2 * ((p - 1) / 2 + j + 1) = p + (2 * j + 1) by omega, pow_add]
  rw [ht, mul_pow, mul_pow, hpow]
  have huj : C ((5 : K) ^ (2 * j + 1))⁻¹ * (5 : K[X]) ^ (2 * j + 1) = 1 := by
    change C ((5 : K) ^ (2 * j + 1))⁻¹ * (C (5 : K)) ^ (2 * j + 1) = 1
    rw [← C_pow, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ h5), C_1]
  rw [show C (((WPFiniteNC122.q p + H j / 2) / ((2 * j + 1 : ℕ) : K)) /
      (5 : K) ^ (2 * j + 1)) =
      C ((WPFiniteNC122.q p + H j / 2) / ((2 * j + 1 : ℕ) : K)) *
        C ((5 : K) ^ (2 * j + 1))⁻¹ by rw [div_eq_mul_inv, map_mul]]
  linear_combination C ((WPFiniteNC122.q p + H j / 2) / ((2 * j + 1 : ℕ) : K)) *
    X ^ p * X ^ (2 * j + 1) * (4 * X ^ 2 - 3) ^ (2 * j + 1) * huj

theorem HJP_cubic_split (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (HJP p : K[X]).comp conic = X ^ (2 * p) * UJP p + VJP p := by
  rw [HJP_conic_pullback p hp, cubic_J_polynomial p hp]
  unfold VcubP UJP VJP
  rw [show (X : K[X]) ^ (2 * p) = (X ^ p) ^ 2 by rw [pow_mul]; ring]
  ring

theorem UJP_eval (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    (UJP p : K[X]).eval t = U_J p t := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  unfold U_J
  rw [F_b_Z p t h2, F_d_Z p t h2]
  simp only [UJP, FbP, FdP, MEP, M_E, eval_sub, eval_add, eval_mul,
    eval_pow, eval_X, eval_C, eval_ofNat, eval_comp, ZP_eval]
  have hE : ∀ s : K, (EP p : K[X]).eval s = WPFiniteField.E p s := by
    intro s
    simp only [EP, eval_mul, eval_C, eval_add, eval_comp, eval_neg, eval_X,
      LP_eval_eq, WPFiniteField.E, div_eq_mul_inv]
    ring
  rw [hE, hE]

private theorem scale_degree (a : ℕ) (P : K[X]) (n : ℕ) (hP : P.natDegree ≤ n) :
    ((a : K[X]) * P).natDegree ≤ n := by
  change (C (a : K) * P).natDegree ≤ n
  exact (natDegree_C_mul_le _ _).trans hP

theorem VJP_small_degree (p : ℕ) [Fact p.Prime] : (VJP p : K[X]).natDegree < 2 * p := by
  have hp := (Fact.out : p.Prime).two_le
  have hFe : (FeP p : K[X]).natDegree ≤ p - 1 := by
    unfold FeP
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le
        ((natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans
          (max_le (ZP_natDegree_le p 1) (ZP_natDegree_le p (-1))))) (ZP_natDegree_le p 2))) (ZP_natDegree_le p (-2)))
  have hn : ((LP p : K[X]).comp (-X)).natDegree ≤ p - 1 :=
    natDegree_comp_le.trans ((Nat.mul_le_mul (LP_natDegree_le p)
      (show (-X : K[X]).natDegree ≤ 1 by simp)).trans (by simp))
  have hO : (OP p : K[X]).natDegree ≤ p - 1 := by
    unfold OP
    exact natDegree_C_mul_le _ _ |>.trans (natDegree_sub_le _ _ |>.trans (max_le (LP_natDegree_le p) hn))
  have hO2 : ((OP p).comp (2 * X) : K[X]).natDegree ≤ p - 1 :=
    natDegree_comp_le.trans ((Nat.mul_le_mul hO (scale_degree 2 X 1 (by simp))).trans (by simp))
  have hMO : (MOP p : K[X]).natDegree ≤ p - 1 := by
    unfold MOP
    exact natDegree_add_le _ _ |>.trans (max_le ((natDegree_C_mul_le _ _).trans hO) ((natDegree_C_mul_le _ _).trans hO2))
  have h := natDegree_mul_le (p := (X : K[X]) ^ p) (q := FeP p + MOP p) |>.trans
    (Nat.add_le_add (show (X ^ p : K[X]).natDegree ≤ p by simp)
      (natDegree_add_le _ _ |>.trans (max_le hFe hMO)))
  dsimp only [VJP]
  omega

theorem UJP_high_band_transport (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (UJP p : K[X]) = 5 * (highBand p (HJP p)).comp conic := by
  have hH : (HJP p : K[X]).natDegree < 2 * p := by
    have he := HJP_natDegree_le (K := K) p hp
    omega
  have h5pow : (5 : K[X]) ^ p = 5 := by
    change C (5 : K) ^ p = C (5 : K)
    rw [← map_pow]
    congr 1
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 5
  have hc : (conic : K[X]) ^ p = 5 * X ^ (2 * p) - 1 := by
    unfold conic
    rw [sub_pow_char (p := p), one_pow, mul_pow, h5pow, ← pow_mul]
  have he := congrArg (fun P : K[X] => P.comp conic) (full_cutoff_split p (HJP p) hH)
  simp only [add_comp, mul_comp, pow_comp, X_comp] at he
  rw [hc, HJP_cubic_split p hp] at he
  let A : K[X] := 5 * (highBand p (HJP p)).comp conic - UJP p
  let B : K[X] := (lowBand p (HJP p)).comp conic -
    (highBand p (HJP p)).comp conic - VJP p
  have hcone : (conic : K[X]).natDegree ≤ 2 := by
    unfold conic
    exact natDegree_sub_le _ _ |>.trans (max_le (scale_degree 5 _ _ (by simp)) (by simp))
  have hband := cutoff_band_degree (K := K) p (HJP p)
  have hLo : ((lowBand p (HJP p)).comp conic : K[X]).natDegree ≤ 2 * p - 1 := by
    have h := natDegree_comp_le (p := lowBand p (HJP p)) (q := conic) |>.trans
      (Nat.mul_le_mul hband.1 hcone)
    omega
  have hHi : ((highBand p (HJP p)).comp conic : K[X]).natDegree ≤ 2 * p - 1 := by
    have h := natDegree_comp_le (p := highBand p (HJP p)) (q := conic) |>.trans
      (Nat.mul_le_mul hband.2 hcone)
    omega
  have hB : B.natDegree < 2 * p := by
    have hv := VJP_small_degree (K := K) p
    have h := natDegree_sub_le ((lowBand p (HJP p)).comp conic - (highBand p (HJP p)).comp conic) (VJP p) |>.trans
      (max_le (natDegree_sub_le _ _ |>.trans (max_le hLo hHi)) (show (VJP p : K[X]).natDegree ≤ 2 * p - 1 by omega))
    dsimp only [B]
    omega
  have hz : X ^ (2 * p) * A + B = 0 := by
    dsimp only [A, B]
    linear_combination -he
  have ha := shifted_low_unique (2 * p) A B hB hz
  dsimp only [A] at ha
  exact (sub_eq_zero.mp ha).symm

theorem actual_J_high_coefficient (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) : (HJP p : K[X]).coeff p = U_J p u / 5 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have hcu : (conic : K[X]).eval u = 0 := by
    simp only [conic, eval_sub, eval_mul, eval_ofNat, eval_pow, eval_X, eval_one, hu]
    field_simp [h5]
    ring
  have he := congrArg (fun P : K[X] => P.eval u) (UJP_high_band_transport (K := K) p hp)
  rw [UJP_eval p hp, eval_mul, eval_ofNat, eval_comp, hcu,
    ← coeff_zero_eq_eval_zero, highBand_coeff, if_pos (by omega : 0 < p), Nat.add_zero] at he
  apply (eq_div_iff h5).mpr
  linear_combination -he

theorem actual_J_high_contraction (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) : (HJP p : K[X]).coeff p =
      (WPFiniteLoop.A p u - WPFiniteLoop.B p u + WPFiniteDReciprocity.At p u -
        WPFiniteDReciprocity.Bt p u + WPFiniteLoop.Chi p u -
        2 * (WPFiniteField.E p (2 * u) - WPFiniteField.E p u) ^ 2 +
        (4 * WPFiniteNC122.q p - 3 * r p) *
          (2 * WPFiniteField.E p u + WPFiniteField.E p (2 * u)) - 2 * (WPFiniteNC122.q p) ^ 2) / 5 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have hu0 : u ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by omega : (2 : ℕ) ≠ 0)] at hu
    exact (one_div_ne_zero h5) hu.symm
  rw [actual_J_high_coefficient p hp u hu, U_J_original_contraction p hp u hu0]

noncomputable def V_J (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) : K :=
  t ^ p * (F_e p t + M_O p t)

theorem VJP_eval (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) :
    (VJP p : K[X]).eval t = V_J p t := by
  simp only [VJP, FeP, MOP, V_J, F_e, M_O, eval_mul, eval_pow,
    eval_X, eval_add, eval_C, eval_comp, eval_ofNat, ZP_eval, OP_eval, div_eq_mul_inv]
  ring

theorem actual_J_origin_split (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) : (HJP p : K[X]).eval 0 = U_J p u / 5 + V_J p u := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h5pow : (5 : K) ^ p = 5 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 5
  have hu2p : u ^ (2 * p) = 1 / 5 := by rw [pow_mul, hu, div_pow, one_pow, h5pow]
  have hcu : (conic : K[X]).eval u = 0 := by
    simp only [conic, eval_sub, eval_mul, eval_ofNat, eval_pow, eval_X, eval_one, hu]
    field_simp [h5]
    ring
  have he := congrArg (fun P : K[X] => P.eval u) (HJP_cubic_split (K := K) p hp)
  simp only [eval_comp, hcu, eval_add, eval_mul, eval_pow, eval_X,
    hu2p, UJP_eval p hp, VJP_eval] at he
  linear_combination he

/-- The original JT3 finite endpoint functional, before native residue transport. -/
noncomputable def JendpointFunctional (p : ℕ) : K :=
  -22 * (HJP p : K[X]).eval 0 / 15 + 77 * (HJP p).coeff p / 15

theorem actual_J_endpoint_attachment (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    JendpointFunctional p + 22 * (HJP p : K[X]).eval 0 / 15 = 77 * U_J p u / 75 := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15 (Finset.mem_Ico.mpr (by omega))
  have h75 : (75 : K) ≠ 0 := by
    rw [show (75 : K) = 3 * 5 ^ 2 by ring]
    exact mul_ne_zero h3 (pow_ne_zero _ h5)
  unfold JendpointFunctional
  rw [actual_J_high_coefficient p hp u hu]
  field_simp [h5, h15, h75]
  ring

end WPFiniteJHighCoefficient
