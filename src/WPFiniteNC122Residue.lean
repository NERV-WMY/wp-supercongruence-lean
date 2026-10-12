import WPFiniteJSource

open scoped BigOperators
open Polynomial

namespace WPFiniteNC122Residue

open WPFiniteAffineLog WPFiniteKSource

variable {K : Type*} [Field K]

noncomputable def Qrev : K[X] :=
  C (4 / 125 : K) - C (33 / 125 : K) * X + C (72 / 125 : K) * X ^ 2 -
    C (16 / 125 : K) * X ^ 3

noncomputable def Frev : K[X] :=
  C (132 / 125 : K) * X ^ 3 - C (81 / 125 : K) * X ^ 2 + C (12 / 125 : K) * X

noncomputable def canceledDensity (P : K[X]) : K[X] := P.divX.comp Qrev * Frev

theorem canceled_density_full_coefficient (P : K[X]) (hz : P.eval 0 = 0) :
    (canceledDensity P).coeff 1 = 3 * P.eval (4 / 125) := by
  have hF0 : (Frev : K[X]).coeff 0 = 0 := by simp [Frev]
  have hF1 : (Frev : K[X]).coeff 1 = 12 / 125 := by simp [Frev]
  have hQ0 : (Qrev : K[X]).eval 0 = 4 / 125 := by simp [Qrev]
  have hcoeff0 : P.coeff 0 = 0 := by simpa only [coeff_zero_eq_eval_zero] using hz
  have hdiv : X * P.divX = P := by
    simpa only [hcoeff0, map_zero, add_zero] using X_mul_divX_add P
  have he := congrArg (fun F : K[X] => F.eval (4 / 125)) hdiv
  simp only [eval_mul, eval_X] at he
  unfold canceledDensity
  rw [mul_coeff_one, hF0, hF1, mul_zero, add_zero, coeff_zero_eq_eval_zero,
    eval_comp, hQ0, ← he]
  simp only [div_eq_mul_inv]
  ring

theorem Qrev_factored : (Qrev : K[X]) = C (125 : K)⁻¹ * (4 * X - 1) ^ 2 * (4 - X) := by
  unfold Qrev
  simp only [div_eq_mul_inv, map_mul, map_ofNat]
  ring

theorem original_canceled_Q_density (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (x : K) (hx : x ≠ 0) (hx4 : x - 4 ≠ 0) (h4x1 : 4 * x - 1 ≠ 0) :
    ((4 - x) ^ 2 * (4 * x - 1) / (125 * x ^ 3)) *
      (1 / (x - 4) + 8 / (4 * x - 1)) =
        (132 * (x⁻¹) ^ 3 - 81 * (x⁻¹) ^ 2 + 12 * x⁻¹) / 125 := by
  have hfive : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h125 : (125 : K) ≠ 0 := by
    rw [show (125 : K) = 5 ^ 3 by ring]
    exact pow_ne_zero _ hfive
  field_simp [hx, hx4, h4x1, h125]
  ring

private theorem coeff_comp_neg (P : K[X]) (n : ℕ) :
    (P.comp (-X)).coeff n = P.coeff n * (-1 : K) ^ n := by
  refine Polynomial.induction_on P (fun a => ?_) (fun f g hf hg => ?_) (fun d a _ => ?_)
  · simp only [C_comp, coeff_C]
    by_cases hn : n = 0 <;> simp [hn]
  · rw [add_comp, coeff_add, coeff_add, hf, hg]
    ring
  · have hpow : (-X : K[X]) ^ (d + 1) = C ((-1 : K) ^ (d + 1)) * X ^ (d + 1) := by
      calc
        _ = (C (-1 : K) * X) ^ (d + 1) := by simp
        _ = _ := by rw [mul_pow, ← C_pow]
    rw [mul_comp, C_comp, pow_comp, X_comp, hpow, ← mul_assoc, ← C_mul]
    rw [coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    by_cases hn : d + 1 = n
    · subst n
      simp
    · simp only [if_neg (Ne.symm hn), zero_mul]

private theorem even_contract_expand (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (P : K[X]) (heven : P.comp (-X) = P) :
    (contract 2 P).comp (X ^ 2) = P := by
  rw [← expand_eq_comp_X_pow]
  ext n
  rw [coeff_expand (by omega : 0 < 2)]
  by_cases hn : 2 ∣ n
  · rw [if_pos hn, coeff_contract (by omega : 2 ≠ 0), Nat.div_mul_cancel hn]
  · rw [if_neg hn]
    have hodd : Odd n := (Nat.even_or_odd n).resolve_left (by
      rintro ⟨a, ha⟩
      exact hn ⟨a, by omega⟩)
    have he := congrArg (fun F : K[X] => F.coeff n) heven
    rw [coeff_comp_neg, hodd.neg_pow, one_pow] at he
    have hkill : (2 : K) * P.coeff n = 0 := by linear_combination -he
    have htwo : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
      (Finset.mem_Ico.mpr (by omega))
    exact ((mul_eq_zero.mp hkill).resolve_left htwo).symm

theorem LPsrc_even (p : ℕ) : (LPsrc p : K[X]).comp (-X) = LPsrc p := by
  unfold LPsrc EP
  simp only [add_comp, mul_comp, C_comp, comp_neg_X_comp_neg_X]
  ring

theorem KsrcP_even (p : ℕ) (c : K) : (KsrcP p c : K[X]).comp (-X) = KsrcP p c := by
  have hAP : (AP : K[X]).comp (-X) = BP := by
    simp only [AP, BP, mul_comp, C_comp, add_comp, one_comp, X_comp, sub_eq_add_neg]
  have hBP : (BP : K[X]).comp (-X) = AP := by
    simp only [AP, BP, mul_comp, C_comp, sub_comp, one_comp, X_comp, sub_neg_eq_add]
  have hminus : (1 - X : K[X]).comp (-X) = 1 + X := by simp
  have hplus : (1 + X : K[X]).comp (-X) = 1 - X := by simp [sub_eq_add_neg]
  unfold KsrcP S2P
  simp only [add_comp, sub_comp, mul_comp, C_comp, comp_assoc,
    hAP, hBP, hminus, hplus, LPsrc_even]
  ring

noncomputable def bracketT (p : ℕ) (c : K) : K[X] :=
  C (-2 / 3 : K) * KsrcP p c - C (1 / 3 : K) * (LPsrc p - C c) ^ 2 + C (c ^ 2 / 3)

noncomputable def bracketQ (p : ℕ) (c : K) : K[X] :=
  (contract 2 (bracketT p c)).comp (1 - X)

theorem bracketT_even (p : ℕ) (c : K) : (bracketT p c).comp (-X) = bracketT p c := by
  unfold bracketT
  simp only [add_comp, sub_comp, mul_comp, C_comp, pow_comp, KsrcP_even, LPsrc_even]

theorem bracketQ_transport (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (c : K) :
    (bracketQ p c).comp (1 - X ^ 2) = bracketT p c := by
  unfold bracketQ
  rw [comp_assoc]
  have he : (1 - X : K[X]).comp (1 - X ^ 2) = X ^ 2 := by simp
  rw [he]
  exact even_contract_expand p hp (bracketT p c) (bracketT_even p c)

theorem bracketT_eval (p : ℕ) [Fact p.Prime] [CharP K p] (c t : K) :
    (bracketT p c).eval t = -2 * WPFiniteNC122.Ksrc p c t / 3 -
      (WPFiniteNC122.L p t - c) ^ 2 / 3 + c ^ 2 / 3 := by
  simp only [bracketT, eval_add, eval_sub, eval_mul, eval_C, eval_pow,
    KsrcP_eval, LPsrc_eval, div_eq_mul_inv]
  ring

theorem bracketQ_eval (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (c t : K) :
    (bracketQ p c).eval (1 - t ^ 2) = (bracketT p c).eval t := by
  have he := congrArg (fun F : K[X] => F.eval t) (bracketQ_transport p hp c)
  simpa only [eval_comp, eval_sub, eval_one, eval_pow, eval_X] using he

theorem bracketQ_zero_end (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (c : K) :
    (bracketQ p c).eval 0 = 0 := by
  have htwo : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hlog1 : WPFiniteField.ell p (1 : K) = 0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.ell_one_eq_zero p (by omega))
    simpa only [← WPFiniteField.ell_castHom, map_one, map_zero] using he
  have hL1 : WPFiniteNC122.L p (1 : K) = 0 := by
    have he := ell_affine_half p hp (1 : K)
    rw [show ((1 + 1) / 2 : K) = 1 by field_simp [htwo]; ring, hlog1] at he
    exact he.symm
  have he := bracketQ_eval p hp c (1 : K)
  rw [one_pow, sub_self, bracketT_eval, (WPFiniteNC122.Ksrc_normalized_end p hp c).1,
    hL1] at he
  rw [he]
  ring

theorem actual_NC122_residue (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    (canceledDensity (bracketQ p (WPFiniteNC122.h p))).coeff 1 = WPFiniteNC122.G_KQ p u := by
  have hthree : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have hfive : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h25 : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 ^ 2 by ring]
    exact pow_ne_zero _ hfive
  have h125 : (125 : K) ≠ 0 := by
    rw [show (125 : K) = 5 ^ 3 by ring]
    exact pow_ne_zero _ hfive
  have hq : (1 - (WPFiniteNC122.T0 u) ^ 2 : K) = 4 / 125 := by
    unfold WPFiniteNC122.T0
    rw [div_pow, mul_pow, hu]
    field_simp [hfive, h25, h125]
    ring
  rw [canceled_density_full_coefficient _ (bracketQ_zero_end p hp _)]
  rw [← hq, bracketQ_eval p hp, bracketT_eval]
  unfold WPFiniteNC122.G_KQ WPFiniteNC122.a0
  field_simp [hthree]

theorem actual_NC122_corrected_value (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    (canceledDensity (bracketQ p (WPFiniteNC122.h p))).coeff 1 =
      2 * WPFiniteNC122.Aeven p (WPFiniteNC122.T0 u) - 4 * (WPFiniteNC122.a0 p u) ^ 2 / 3 +
      2 * (WPFiniteNC122.q p - WPFiniteNC122.h p) * WPFiniteNC122.a0 p u -
      2 * (WPFiniteNC122.h p) ^ 2 / 3 + 2 * WPFiniteNC122.q p * WPFiniteNC122.h p -
      (WPFiniteNC122.q p) ^ 2 + 22 * WPFiniteNC122.h0J p u / 15 := by
  rw [actual_NC122_residue p hp u hu]
  exact WPFiniteNC122.original_corrected_endpoint p hp u hu

noncomputable def VP : K[X] := C (125 : K)⁻¹ * (4 - X) * (4 * X - 1) ^ 2

theorem Qrev_original_eval (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (x : K) (hx : x ≠ 0) :
    (Qrev : K[X]).eval x⁻¹ = (4 - x) ^ 2 * (4 * x - 1) / (125 * x ^ 3) := by
  have hfive : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h125 : (125 : K) ≠ 0 := by
    rw [show (125 : K) = 5 ^ 3 by ring]
    exact pow_ne_zero _ hfive
  rw [Qrev_factored]
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_ofNat, eval_X, eval_one]
  field_simp [hx, h125]

theorem VP_logarithmic_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (x : K) (hx4 : x - 4 ≠ 0) (h4x1 : 4 * x - 1 ≠ 0) :
    (VP : K[X]).derivative.eval x / VP.eval x = 1 / (x - 4) + 8 / (4 * x - 1) := by
  have hfive : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h125 : (125 : K) ≠ 0 := by
    rw [show (125 : K) = 5 ^ 3 by ring]
    exact pow_ne_zero _ hfive
  have h4mx : (4 - x : K) ≠ 0 := by
    rw [show (4 - x : K) = -(x - 4) by ring]
    exact neg_ne_zero.mpr hx4
  unfold VP
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_sub,
    derivative_ofNat, derivative_X, zero_sub, mul_one, derivative_one,
    derivative_pow, eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_neg,
    eval_one, eval_ofNat, eval_X, eval_zero]
  field_simp [hx4, h4x1, h4mx, h125]
  ring

theorem original_density_eval (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (P : K[X]) (hz : P.eval 0 = 0) (x : K) (hx : x ≠ 0)
    (hx4 : x - 4 ≠ 0) (h4x1 : 4 * x - 1 ≠ 0) :
    (canceledDensity P).eval x⁻¹ =
      P.eval ((4 - x) ^ 2 * (4 * x - 1) / (125 * x ^ 3)) *
        ((VP : K[X]).derivative.eval x / VP.eval x) := by
  have hcoeff0 : P.coeff 0 = 0 := by simpa only [coeff_zero_eq_eval_zero] using hz
  have hdiv : X * P.divX = P := by
    simpa only [hcoeff0, map_zero, add_zero] using X_mul_divX_add P
  have he := congrArg (fun F : K[X] =>
    F.eval ((4 - x) ^ 2 * (4 * x - 1) / (125 * x ^ 3))) hdiv
  simp only [eval_mul, eval_X] at he
  have hF : (Frev : K[X]).eval x⁻¹ =
      ((4 - x) ^ 2 * (4 * x - 1) / (125 * x ^ 3)) *
        (1 / (x - 4) + 8 / (4 * x - 1)) := by
    rw [original_canceled_Q_density p hp x hx hx4 h4x1]
    simp only [Frev, eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
      div_eq_mul_inv]
    ring
  unfold canceledDensity
  rw [eval_mul, eval_comp, Qrev_original_eval p hp x hx, hF,
    VP_logarithmic_derivative p hp x hx4 h4x1]
  linear_combination (1 / (x - 4) + 8 / (4 * x - 1)) * he

theorem actual_bracket_original_density (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (c x : K) (hx : x ≠ 0) (hx4 : x - 4 ≠ 0) (h4x1 : 4 * x - 1 ≠ 0) :
    (canceledDensity (bracketQ p c)).eval x⁻¹ =
      (bracketQ p c).eval ((4 - x) ^ 2 * (4 * x - 1) / (125 * x ^ 3)) *
        ((VP : K[X]).derivative.eval x / VP.eval x) := by
  exact original_density_eval p hp _ (bracketQ_zero_end p hp c) x hx hx4 h4x1

end WPFiniteNC122Residue
