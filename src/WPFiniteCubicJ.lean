import WPFiniteCubicLog

open scoped BigOperators
open Polynomial

namespace WPFiniteCubicJ

open WPFiniteAffineLog WPFiniteKSource WPFiniteDSource WPFiniteJNormalization WPFiniteCubicLog

variable {K : Type*} [Field K]

noncomputable def ZP (p : ℕ) (r : K) : K[X] :=
  C (2 : K)⁻¹ * ((DP p (-r)).comp (C r * X) - (DP p r).comp (C r * X)) +
    (DP p (r / 2)).comp (C r * X) - (DP p (-(r / 2))).comp (C r * X)

theorem ZP_eval (p : ℕ) [Fact p.Prime] (r t : K) : (ZP p r).eval t = Z p r t := by
  simp only [ZP, Z, eval_sub, eval_add, eval_mul, eval_C, eval_comp, eval_X, DP_eval, div_eq_mul_inv]
  ring

theorem DP_affine_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (r c : K) (hr : r ≠ 0) :
    (X - C c) * ((DP p (r * c)).comp (C r * X)).derivative =
      (LP p).comp (C r * X) - C (WPFiniteField.ell p (r * c)) := by
  have he := congrArg (fun P : K[X] => P.comp (C r * X)) (DP_cleared_derivative p (r * c))
  simp only [mul_comp, sub_comp, X_comp, C_comp] at he
  rw [derivative_comp]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_X, mul_one]
  apply mul_left_cancel₀ (C_ne_zero.mpr hr)
  rw [map_mul] at he
  linear_combination C r * he

noncomputable def ZRP (p : ℕ) [Fact p.Prime] [CharP K p] (r : K) : K[X] :=
  C (2 : K)⁻¹ * ((1 + X) * (4 * X ^ 2 - 1) * C (WPFiniteField.ell p r) +
    (1 - X) * (4 * X ^ 2 - 1) * C (WPFiniteField.ell p (-r))) +
    (1 - X ^ 2) * ((4 * X + 2) * C (WPFiniteField.ell p (r / 2)) -
      (4 * X - 2) * C (WPFiniteField.ell p (-(r / 2))))

theorem ZP_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (r : K) (hr : r ≠ 0) :
    (1 - X ^ 2) * (4 * X ^ 2 - 1) * (ZP p r).derivative =
      3 * (LP p).comp (C r * X) - ZRP p r := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hunit : (C (2 : K)⁻¹ : K[X]) * 2 = 1 := by
    change C (2 : K)⁻¹ * C (2 : K) = 1
    rw [← C_mul, inv_mul_cancel₀ h2, C_1]
  have hpos := DP_affine_source p r 1 hr
  have hneg := DP_affine_source p r (-1) hr
  have hhalf := DP_affine_source p r (1 / 2) hr
  have hnhalf := DP_affine_source p r (-(1 / 2)) hr
  simp only [mul_one, mul_neg, map_one, map_neg, sub_neg_eq_add] at hpos hneg
  rw [show r * (1 / 2) = r / 2 by ring, one_div] at hhalf
  rw [show r * (-(1 / 2)) = -(r / 2) by ring, one_div, map_neg, sub_neg_eq_add] at hnhalf
  unfold ZP ZRP
  simp only [derivative_sub, derivative_add, derivative_mul, derivative_C, zero_mul, zero_add]
  linear_combination C (2 : K)⁻¹ * (1 - X) * (4 * X ^ 2 - 1) * hneg +
    C (2 : K)⁻¹ * (1 + X) * (4 * X ^ 2 - 1) * hpos +
    (1 - X ^ 2) * (4 * X + 2) * hhalf -
    (1 - X ^ 2) * (4 * X - 2) * hnhalf +
    ((1 - X ^ 2) * ((2 * X + 1) * ((DP p (r / 2)).comp (C r * X)).derivative +
      (2 * X - 1) * ((DP p (-(r / 2))).comp (C r * X)).derivative) +
      (4 * X ^ 2 - 1) * (LP p).comp (C r * X)) * hunit

theorem ZRP_four (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (r : K) :
    4 * ZRP p r =
      2 * ((1 + X) * (4 * X ^ 2 - 1) * C (WPFiniteField.ell p r) +
        (1 - X) * (4 * X ^ 2 - 1) * C (WPFiniteField.ell p (-r))) +
      2 * (1 - X ^ 2) * ((4 * X + 2) * C (2 * WPFiniteField.ell p (r / 2)) -
        (4 * X - 2) * C (2 * WPFiniteField.ell p (-(r / 2)))) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hunit : (C (2 : K)⁻¹ : K[X]) * 2 = 1 := by
    change C (2 : K)⁻¹ * C (2 : K) = 1
    rw [← C_mul, inv_mul_cancel₀ h2, C_1]
  unfold ZRP
  simp only [map_mul, map_ofNat]
  linear_combination 2 * ((1 + X) * (4 * X ^ 2 - 1) * C (WPFiniteField.ell p r) +
    (1 - X) * (4 * X ^ 2 - 1) * C (WPFiniteField.ell p (-r))) * hunit

theorem rational_ell_sources (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteField.ell p (1 : K) = 0 ∧
    WPFiniteField.ell p (-1 : K) = -2 * WPFiniteNC122.q p ∧
    WPFiniteField.ell p (2 : K) = -2 * WPFiniteNC122.q p ∧
    WPFiniteField.ell p (-2 : K) = 2 * WPFiniteNC122.q p - 3 * r p ∧
    2 * WPFiniteField.ell p (1 / 2 : K) = 2 * WPFiniteNC122.q p ∧
    2 * WPFiniteField.ell p (-(1 / 2) : K) = 2 * WPFiniteNC122.q p - 3 * r p := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hpow : (2 : K) ^ p = 2 := by
    simpa only [Nat.cast_ofNat] using (WPFiniteField.natCast_pow_char (K := K) p 2)
  have h1 : WPFiniteField.ell p (1 : K) = 0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K) (WPFiniteInversion.ell_one_eq_zero p (by omega))
    simpa only [← WPFiniteField.ell_castHom, map_one, map_zero] using he
  have hn1 : WPFiniteField.ell p (-1 : K) = -2 * WPFiniteNC122.q p := by
    have he := WPFiniteField.ell_reflection p (by omega) (-1 : K)
    rw [show (1 - -1 : K) = 2 by ring, WPFiniteLoop.ell_two p hp] at he
    exact he.symm
  have he2 : WPFiniteField.ell p (2 : K) = -2 * WPFiniteNC122.q p := WPFiniteLoop.ell_two p hp
  have hen2 : WPFiniteField.ell p (-2 : K) = 2 * WPFiniteNC122.q p - 3 * r p := WPFiniteLoop.ell_neg_two p hp
  have hh := WPFiniteField.ell_inversion p (2 : K) h2
  rw [hpow, he2] at hh
  simp only [← one_div] at hh
  have hnh := WPFiniteField.ell_inversion p (-2 : K) (neg_ne_zero.mpr h2)
  rw [hodd.neg_pow, hpow, hen2] at hnh
  simp only [inv_neg] at hnh
  simp only [← one_div] at hnh
  refine ⟨h1, hn1, he2, hen2, ?_, ?_⟩
  · rw [hh]; field_simp [h2]
  · rw [hnh]; field_simp [h2]

noncomputable def FbP (p : ℕ) : K[X] := 2 * ZP p 1 + 2 * ZP p (-1) - 2 * ZP p 2 - 2 * ZP p (-2)
noncomputable def FdP (p : ℕ) : K[X] := 2 * ZP p 1 - 2 * ZP p (-1) - ZP p 2 + ZP p (-2)
noncomputable def FeP (p : ℕ) : K[X] := C (2 : K)⁻¹ * (ZP p 1 + ZP p (-1)) + ZP p 2 + ZP p (-2)
noncomputable def MEP (p : ℕ) : K[X] :=
  C (8 * WPFiniteNC122.q p - 6 * r p) * EP p +
    C (4 * WPFiniteNC122.q p - 3 * r p) * (EP p).comp (2 * X)
noncomputable def MOP (p : ℕ) : K[X] :=
  C (-3 * r p) * OP p + C (3 * r p / 2) * (OP p).comp (2 * X)
noncomputable def VcubP (p : ℕ) : K[X] :=
  (X ^ p) ^ 2 * FbP p + X ^ p * FdP p + FeP p + X ^ p * MEP p + MOP p

private theorem MOP_eight_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    8 * (MOP p : K[X]).derivative =
      C (-24 * r p) * (OP p).derivative + C (12 * r p) * ((OP p).comp (2 * X)).derivative := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hu : (C (2 : K)⁻¹ : K[X]) * 2 = 1 := by
    change C (2 : K)⁻¹ * C (2 : K) = 1
    rw [← C_mul, inv_mul_cancel₀ h2, C_1]
  unfold MOP
  simp only [map_mul, map_neg, map_ofNat, div_eq_mul_inv]
  simp only [derivative_add, derivative_mul, derivative_C, derivative_ofNat,
    derivative_neg, neg_zero, zero_mul, zero_add]
  linear_combination 12 * C (r p) * ((OP p).comp (2 * X)).derivative * hu

theorem cubic_compensation (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (1 - X ^ 2) * (4 * X ^ 2 - 1) *
        (8 * X ^ p * (MEP p : K[X]).derivative + 8 * (MOP p).derivative) =
      24 * C (WPFiniteNC122.q p) * (1 - 4 * (X ^ p) ^ 2) +
        (4 * (X ^ p) ^ 2 + 4 * X ^ p + 1) * (4 * ZRP p 1) +
        (4 * (X ^ p) ^ 2 - 4 * X ^ p + 1) * (4 * ZRP p (-1)) +
        (-4 * (X ^ p) ^ 2 - 2 * X ^ p + 2) * (4 * ZRP p 2) +
        (-4 * (X ^ p) ^ 2 + 2 * X ^ p + 2) * (4 * ZRP p (-2)) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  obtain ⟨h1, hn1, he2, hen2, hh, hnh⟩ := rational_ell_sources (K := K) p hp
  have hZ1 := ZRP_four (K := K) p hp 1
  have hZn1 := ZRP_four (K := K) p hp (-1)
  have hZ2 := ZRP_four (K := K) p hp 2
  have hZn2 := ZRP_four (K := K) p hp (-2)
  simp only [one_div] at hh hnh
  simp only [one_div, neg_div, neg_neg] at hZ1 hZn1
  simp only [neg_div, div_self h2, neg_neg] at hZ2 hZn2
  rw [hZ1, hZn1, hZ2, hZn2, h1, hn1, he2, hen2, hh, hnh, MOP_eight_derivative p hp]
  have hE : (1 - X ^ 2 : K[X]) * (EP p).derivative = X - X ^ p := by
    have he := LPsrc_cleared_derivative (K := K) p hp
    simpa only [LPsrc, derivative_add, derivative_C, zero_add] using he
  have h2pow : (2 : K[X]) ^ p = 2 := by
    change C (2 : K) ^ p = C (2 : K)
    rw [← map_pow]
    congr 1
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 2
  have hE2 := EP_comp_source (K := K) p hp (2 * X : K[X])
  simp only [derivative_mul, derivative_ofNat, zero_mul, zero_add, derivative_X,
    mul_one, mul_pow, h2pow] at hE2
  have hE2' : (4 * X ^ 2 - 1 : K[X]) * ((EP p).comp (2 * X)).derivative = -4 * (X - X ^ p) := by
    linear_combination -hE2
  have hO := OP_cleared_derivative (K := K) p hp
  have h2pred : (2 : K) ^ (p - 1) = 1 := by
    apply mul_right_cancel₀ h2
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    simpa only [one_mul, Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 2
  have h2predP : (2 : K[X]) ^ (p - 1) = 1 := by
    change C (2 : K) ^ (p - 1) = 1
    rw [← map_pow, h2pred, C_1]
  have hO2 := OP_comp_source (K := K) p hp (2 * X : K[X])
  simp only [derivative_mul, derivative_ofNat, zero_mul, zero_add, derivative_X,
    mul_one, mul_pow, h2predP, one_mul] at hO2
  have hO2' : (4 * X ^ 2 - 1 : K[X]) * ((OP p).comp (2 * X)).derivative = -2 * (1 - X ^ (p - 1)) := by
    linear_combination -hO2
  have hxp : X * X ^ (p - 1) = (X : K[X]) ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
  unfold MEP
  simp only [map_mul, map_sub, map_neg, map_ofNat, map_zero]
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_C,
    derivative_ofNat, zero_mul, zero_add]
  linear_combination
    8 * X ^ p * (8 * C (WPFiniteNC122.q p) - 6 * C (r p)) * (4 * X ^ 2 - 1) * hE +
    8 * X ^ p * (4 * C (WPFiniteNC122.q p) - 3 * C (r p)) * (1 - X ^ 2) * hE2' +
    (-24 * C (r p)) * (4 * X ^ 2 - 1) * hO +
    (12 * C (r p)) * (1 - X ^ 2) * hO2' + 72 * C (r p) * X * hxp

theorem VcubP_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (1 - X ^ 2) * (4 * X ^ 2 - 1) * (VcubP p : K[X]).derivative =
      3 * (LPsrc p).comp Tc := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hu : (C (2 : K)⁻¹ : K[X]) * 2 = 1 := by
    change C (2 : K)⁻¹ * C (2 : K) = 1
    rw [← C_mul, inv_mul_cancel₀ h2, C_1]
  have hZ1 := ZP_cleared_source (K := K) p hp 1 one_ne_zero
  have hZn1 := ZP_cleared_source (K := K) p hp (-1) (neg_ne_zero.mpr one_ne_zero)
  have hZ2 := ZP_cleared_source (K := K) p hp 2 h2
  have hZn2 := ZP_cleared_source (K := K) p hp (-2) (neg_ne_zero.mpr h2)
  have hW := UW1_four_logs_polynomial (K := K) p hp
  have hC := cubic_compensation (K := K) p hp
  have hDXp : (X ^ p : K[X]).derivative = 0 := by
    rw [derivative_X_pow, CharP.cast_eq_zero K p, C_0, zero_mul]
  have hLneg : (LP p).comp (C (-1 : K) * X) = (LP p).comp (-X) := by simp
  have hL2 : (LP p).comp (C (2 : K) * X) = (LP p).comp (2 * X) := rfl
  have hLn2 : (LP p).comp (C (-2 : K) * X) = (LP p).comp (-2 * X) := by
    simp only [map_neg, map_ofNat]
  simp only [C_1, one_mul, comp_X] at hZ1
  rw [hLneg] at hZn1
  rw [hL2] at hZ2
  rw [hLn2] at hZn2
  apply mul_left_cancel₀ (show (8 : K[X]) ≠ 0 by
    change C (8 : K) ≠ 0
    exact C_ne_zero.mpr (WPFiniteField.denominator_ne_zero p 8 (Finset.mem_Ico.mpr (by omega))))
  unfold VcubP FbP FdP FeP
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_C, derivative_ofNat, hDXp, zero_mul, mul_zero, zero_add]
  linear_combination
    4 * (4 * (X ^ p) ^ 2 + 4 * X ^ p + 1) * hZ1 +
    4 * (4 * (X ^ p) ^ 2 - 4 * X ^ p + 1) * hZn1 +
    4 * (-4 * (X ^ p) ^ 2 - 2 * X ^ p + 2) * hZ2 +
    4 * (-4 * (X ^ p) ^ 2 + 2 * X ^ p + 2) * hZn2 + hC - 24 * hW +
    (4 * (1 - X ^ 2) * (4 * X ^ 2 - 1) * ((ZP p 1).derivative + (ZP p (-1)).derivative) -
      12 * ((LP p : K[X]) + (LP p).comp (-X))) * hu

private theorem EP_eval (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) :
    (EP p : K[X]).eval t = WPFiniteField.E p t := by
  simp only [EP, eval_mul, eval_C, eval_add, eval_comp, eval_neg, eval_X,
    LP_eval_eq, WPFiniteField.E, div_eq_mul_inv]
  ring

theorem VcubP_eval (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    (VcubP p : K[X]).eval t = V_cub p t := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  unfold V_cub
  rw [F_b_Z p t h2, F_d_Z p t h2]
  simp only [VcubP, FbP, FdP, FeP, MEP, MOP, F_e, M_E, M_O, eval_add,
    eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_ofNat, eval_comp,
    ZP_eval, EP_eval, OP_eval, div_eq_mul_inv]
  ring

theorem ZP_neg_comp (p : ℕ) (r : K) : (ZP p r).comp (-X) = -ZP p (-r) := by
  have ha : (C r * X : K[X]).comp (-X) = C (-r) * X := by simp
  unfold ZP
  simp only [mul_comp, C_comp, sub_comp, add_comp, comp_assoc, ha, neg_neg, neg_div]
  ring

private theorem EP_even (p : ℕ) : (EP p : K[X]).comp (-X) = EP p := by
  unfold EP
  simp only [mul_comp, C_comp, add_comp, comp_neg_X_comp_neg_X]
  ring

private theorem OP_odd (p : ℕ) : (OP p : K[X]).comp (-X) = -OP p := by
  unfold OP
  simp only [mul_comp, C_comp, sub_comp, comp_neg_X_comp_neg_X]
  ring

theorem VcubP_odd (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (VcubP p : K[X]).comp (-X) = -VcubP p := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have ha : (2 * X : K[X]).comp (-X) = (-X).comp (2 * X) := by simp
  have hE2 : ((EP p).comp (2 * X) : K[X]).comp (-X) = (EP p).comp (2 * X) := by
    rw [comp_assoc, ha, ← comp_assoc, EP_even]
  have hO2 : ((OP p).comp (2 * X) : K[X]).comp (-X) = -(OP p).comp (2 * X) := by
    rw [comp_assoc, ha, ← comp_assoc, OP_odd, neg_comp]
  have hFb : (FbP p : K[X]).comp (-X) = -FbP p := by
    unfold FbP
    simp only [sub_comp, add_comp, mul_comp, ofNat_comp, ZP_neg_comp, neg_neg]
    ring
  have hFd : (FdP p : K[X]).comp (-X) = FdP p := by
    unfold FdP
    simp only [sub_comp, add_comp, mul_comp, ofNat_comp, ZP_neg_comp, neg_neg]
    ring
  have hFe : (FeP p : K[X]).comp (-X) = -FeP p := by
    unfold FeP
    simp only [add_comp, mul_comp, C_comp, ZP_neg_comp, neg_neg]
    ring
  have hME : (MEP p : K[X]).comp (-X) = MEP p := by
    unfold MEP
    rw [add_comp, mul_comp, mul_comp, C_comp, C_comp, EP_even, hE2]
  have hMO : (MOP p : K[X]).comp (-X) = -MOP p := by
    unfold MOP
    rw [add_comp, mul_comp, mul_comp, C_comp, C_comp, OP_odd, hO2]
    ring
  unfold VcubP
  simp only [add_comp, mul_comp, pow_comp, X_comp, hodd.neg_pow, hFb, hFd, hFe, hME, hMO]
  ring

theorem ZP_natDegree_le (p : ℕ) (r : K) : (ZP p r).natDegree ≤ p - 1 := by
  have ha : (C r * X : K[X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp)
  have hd : ∀ y : K, ((DP p y).comp (C r * X)).natDegree ≤ p - 1 := by
    intro y
    exact (natDegree_comp_le).trans ((Nat.mul_le_mul (DP_natDegree_le p y) ha).trans (by simp))
  unfold ZP
  exact (natDegree_sub_le _ _).trans (max_le
    ((natDegree_add_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (max_le (hd _) (hd _)))) (hd _))) (hd _))

private theorem scale_degree (a : ℕ) (P : K[X]) (n : ℕ) (hP : P.natDegree ≤ n) :
    ((a : K[X]) * P).natDegree ≤ n := by
  change (C (a : K) * P).natDegree ≤ n
  exact (natDegree_C_mul_le _ _).trans hP

private theorem mul_degree (P Q : K[X]) (m n : ℕ) (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) :
    (P * Q).natDegree ≤ m + n := natDegree_mul_le.trans (Nat.add_le_add hP hQ)

theorem VcubP_natDegree_le (p : ℕ) [Fact p.Prime] : (VcubP p : K[X]).natDegree ≤ 3 * p - 1 := by
  have hp := (Fact.out : p.Prime).two_le
  have hZ1 := ZP_natDegree_le (K := K) p 1
  have hZn1 := ZP_natDegree_le (K := K) p (-1)
  have hZ2 := ZP_natDegree_le (K := K) p 2
  have hZn2 := ZP_natDegree_le (K := K) p (-2)
  have hFb : (FbP p : K[X]).natDegree ≤ p - 1 := by
    unfold FbP
    exact (natDegree_sub_le _ _).trans (max_le
      ((natDegree_sub_le _ _).trans (max_le
        ((natDegree_add_le _ _).trans (max_le (scale_degree 2 _ _ hZ1) (scale_degree 2 _ _ hZn1)))
        (scale_degree 2 _ _ hZ2))) (scale_degree 2 _ _ hZn2))
  have hFd : (FdP p : K[X]).natDegree ≤ p - 1 := by
    unfold FdP
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_sub_le _ _).trans (max_le
        ((natDegree_sub_le _ _).trans (max_le (scale_degree 2 _ _ hZ1) (scale_degree 2 _ _ hZn1))) hZ2)) hZn2)
  have hFe : (FeP p : K[X]).natDegree ≤ p - 1 := by
    unfold FeP
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le
        ((natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (max_le hZ1 hZn1))) hZ2)) hZn2)
  have hn : ((LP p : K[X]).comp (-X)).natDegree ≤ p - 1 :=
    natDegree_comp_le.trans ((Nat.mul_le_mul (LP_natDegree_le p) (show (-X : K[X]).natDegree ≤ 1 by simp)).trans (by simp))
  have hE : (EP p : K[X]).natDegree ≤ p - 1 := by
    unfold EP
    exact natDegree_C_mul_le _ _ |>.trans (natDegree_add_le _ _ |>.trans (max_le (LP_natDegree_le p) hn))
  have hO : (OP p : K[X]).natDegree ≤ p - 1 := by
    unfold OP
    exact natDegree_C_mul_le _ _ |>.trans (natDegree_sub_le _ _ |>.trans (max_le (LP_natDegree_le p) hn))
  have hE2 : ((EP p).comp (2 * X) : K[X]).natDegree ≤ p - 1 :=
    natDegree_comp_le.trans ((Nat.mul_le_mul hE (scale_degree 2 X 1 (by simp))).trans (by simp))
  have hO2 : ((OP p).comp (2 * X) : K[X]).natDegree ≤ p - 1 :=
    natDegree_comp_le.trans ((Nat.mul_le_mul hO (scale_degree 2 X 1 (by simp))).trans (by simp))
  have hME : (MEP p : K[X]).natDegree ≤ p - 1 := by
    unfold MEP
    exact natDegree_add_le _ _ |>.trans (max_le ((natDegree_C_mul_le _ _).trans hE) ((natDegree_C_mul_le _ _).trans hE2))
  have hMO : (MOP p : K[X]).natDegree ≤ p - 1 := by
    unfold MOP
    exact natDegree_add_le _ _ |>.trans (max_le ((natDegree_C_mul_le _ _).trans hO) ((natDegree_C_mul_le _ _).trans hO2))
  have hXP : (X ^ p : K[X]).natDegree ≤ p := by simp
  have hXP2 : ((X ^ p) ^ 2 : K[X]).natDegree ≤ 2 * p := natDegree_pow_le.trans (by omega)
  have hA : ((X ^ p) ^ 2 * FbP p : K[X]).natDegree ≤ 3 * p - 1 :=
    (mul_degree _ _ _ _ hXP2 hFb).trans (by omega)
  have hB : (X ^ p * FdP p : K[X]).natDegree ≤ 3 * p - 1 :=
    (mul_degree _ _ _ _ hXP hFd).trans (by omega)
  have hC : (FeP p : K[X]).natDegree ≤ 3 * p - 1 := hFe.trans (by omega)
  have hD : (X ^ p * MEP p : K[X]).natDegree ≤ 3 * p - 1 :=
    (mul_degree _ _ _ _ hXP hME).trans (by omega)
  have hF : (MOP p : K[X]).natDegree ≤ 3 * p - 1 := hMO.trans (by omega)
  unfold VcubP
  exact natDegree_add_le _ _ |>.trans (max_le
    (natDegree_add_le _ _ |>.trans (max_le
      (natDegree_add_le _ _ |>.trans (max_le (natDegree_add_le _ _ |>.trans (max_le hA hB)) hC)) hD)) hF)

theorem cubic_J_polynomial (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (JLP p : K[X]).comp Tc = VcubP p - C (K_J p) * X ^ p := by
  let Q : K[X] := (JLP p).comp Tc - VcubP p
  have hB : (4 * X ^ 2 - 1 : K[X]) ≠ 0 := by
    intro hz
    have he := congrArg (fun P : K[X] => P.eval 0) hz
    simp at he
  have hqT : (1 - X ^ 2 : K[X]) ≠ 0 := by
    intro hz
    have he := congrArg (fun P : K[X] => P.eval 0) hz
    simp at he
  have hTcD : (Tc : K[X]).derivative = 3 * (4 * X ^ 2 - 1) := by
    unfold Tc
    simp only [derivative_sub, derivative_mul, derivative_ofNat, zero_mul, zero_add,
      derivative_X_pow, derivative_X, mul_one, Nat.cast_ofNat, map_ofNat]
    norm_num only [Nat.reduceSub]
    ring
  have hc := congrArg (fun P : K[X] => P.comp (Tc : K[X])) (JLP_cleared_derivative (K := K) p hp)
  simp only [mul_comp, sub_comp, one_comp, pow_comp, X_comp] at hc
  have hfactor : (1 - (Tc : K[X]) ^ 2) = (1 - X ^ 2) * (4 * X ^ 2 - 1) ^ 2 := by unfold Tc; ring
  have hJL : (1 - X ^ 2) * (4 * X ^ 2 - 1) * ((JLP p : K[X]).comp Tc).derivative = 3 * (LPsrc p).comp Tc := by
    rw [derivative_comp, hTcD]
    rw [hfactor] at hc
    linear_combination 3 * hc
  have hd : Q.derivative = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero hqT hB)
    simp only [Q, derivative_sub, mul_zero]
    linear_combination hJL - VcubP_cleared_source (K := K) p hp
  have hAP : (AP : K[X]).comp (-X) = BP := by
    unfold AP BP
    simp only [mul_comp, C_comp, add_comp, one_comp, X_comp]
    ring
  have hBP : (BP : K[X]).comp (-X) = AP := by
    unfold AP BP
    simp only [mul_comp, C_comp, sub_comp, one_comp, X_comp]
    ring
  have hJO : (JLP p : K[X]).comp (-X) = -JLP p := by
    unfold JLP
    rw [mul_comp, C_comp, sub_comp, comp_assoc, comp_assoc, hAP, hBP]
    ring
  have hTc : (Tc : K[X]).comp (-X) = (-X).comp Tc := by
    simp only [Tc, sub_comp, mul_comp, ofNat_comp, pow_comp, X_comp, neg_comp]
    ring
  have hod : Q.comp (-X) = -Q := by
    dsimp only [Q]
    rw [sub_comp, comp_assoc, hTc, ← comp_assoc, hJO, neg_comp, VcubP_odd p hp]
    ring
  have hTcdeg : (Tc : K[X]).natDegree ≤ 3 := by
    unfold Tc
    exact natDegree_sub_le _ _ |>.trans (max_le (scale_degree 4 _ _ (by simp)) (scale_degree 3 _ _ (by simp)))
  have hJdeg : ((JLP p : K[X]).comp Tc).natDegree ≤ (p - 1) * 3 :=
    natDegree_comp_le.trans (Nat.mul_le_mul (WPFiniteJSource.JLP_natDegree_le p) hTcdeg)
  have hdeg : Q.natDegree < 3 * p := by
    have h := natDegree_sub_le ((JLP p : K[X]).comp Tc) (VcubP p) |>.trans
      (max_le (hJdeg.trans (by omega)) (VcubP_natDegree_le p))
    dsimp only [Q]
    omega
  have hTc1 : (Tc : K[X]).eval 1 = 1 := by norm_num [Tc]
  have he1 : Q.eval 1 = -K_J p := by
    simp only [Q, eval_sub, eval_comp, hTc1, JLP_eval, VcubP_eval p hp]
    rw [(WPFiniteJSource.J_L_normalized_ends (K := K) p hp).1]
    simp only [zero_sub, K_J]
  have he := odd_kernel_three p hp Q hdeg hd hod
  rw [he1, map_neg] at he
  dsimp only [Q] at he
  linear_combination he

theorem cubic_J_literal (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    WPFiniteNC122.J_L p (4 * t ^ 3 - 3 * t) = V_cub p t - t ^ p * K_J p := by
  have he := congrArg (fun P : K[X] => P.eval t) (cubic_J_polynomial (K := K) p hp)
  simp only [eval_comp, Tc, eval_sub, eval_mul, eval_ofNat, eval_pow, eval_X,
    eval_C, JLP_eval, VcubP_eval p hp] at he
  linear_combination he

end WPFiniteCubicJ
