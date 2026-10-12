import WPFieldAssembly.NativeShiftedChi
import WPFiniteZSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPPIntegralReduction WPLaurentIntegralResidue
  WPFiniteLaurentIntegral WPActualEtaPole WPActualPullbackSource
  WPFieldAssembly.NativeShiftedChi WPFiniteABSourceTail WPFiniteWSource
  WPFinitePSource WPFiniteZSource WPFiniteAffineLog

namespace WPFieldAssembly.ActualChiEndpoints

variable {K : Type*} [Field K]

noncomputable def fourUnit (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : Kˣ :=
  Units.mk0 4 (WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega)))

theorem actual_chi_Q_endpoints (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let N := (p - 1) / 2
    evaluate 4 (by norm_num) (chiX p N N) =
        -(WPFiniteInversion.integerFermatQuotient p 2 : ℚ) ∧
      evaluate (1 / 4) (by norm_num) (chiX p N N) =
        (WPFiniteInversion.integerFermatQuotient p 2 : ℚ) /
          (2 : ℚ) ^ (p - 1) := by
  let N := (p - 1) / 2
  have hV4 : evaluate 4 (by norm_num) Vx = 0 := by
    rw [evaluate_Vx]; norm_num
  have hVq : evaluate (1 / 4) (by norm_num) Vx = 0 := by
    rw [evaluate_Vx]; norm_num
  have hHX (a : ℚ) (ha : a ≠ 0) (hV : evaluate a ha Vx = 0) :
      evaluate a ha (HX N) = 0 := by
    simp only [HX, Hpull, evaluate_substitute, hV, Hpolynomial_zero]
  have hr := actual_AX_endpoints p N N
  simp only [AX, map_add, hHX 4 (by norm_num) hV4,
    hHX (1 / 4) (by norm_num) hVq, add_zero] at hr
  have hN : 2 * N = p - 1 := by
    have := half_exponent p hp
    dsimp only [N]; omega
  have h4N : (4 : ℚ) ^ N = (2 : ℚ) ^ (p - 1) := by
    rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, hN]
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have hQa : (WPFiniteInversion.integerFermatQuotient p 2 : ℚ) * p =
      (2 : ℚ) ^ (p - 1) - 1 := by
    exact_mod_cast
      (WPFiniteInversion.integerFermatQuotient_mul p 2 (by simpa using h2))
  have hpQ : (p : ℚ) ≠ 0 := by positivity
  dsimp only
  constructor
  · rw [hr.2, h4N]
    field_simp [hpQ]
    linear_combination hQa
  · rw [hr.1, div_pow, one_pow, h4N]
    field_simp [hpQ, pow_ne_zero (p - 1) (by norm_num : (2 : ℚ) ≠ 0)]
    linear_combination -hQa

theorem actual_chi_field_endpoints (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    eval₂ (RingHom.id (ZMod p)) (fourUnit p hp)
        (residueLaurent p (halfChiIntegral p hp)) =
        -(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) ∧
      eval₂ (RingHom.id (ZMod p)) (fourUnit p hp)⁻¹
        (residueLaurent p (halfChiIntegral p hp)) =
        (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
  let I := shiftedChiIntegral p hp
  let a : integralRationals p :=
    ⟨1 / 4, WPFiniteConductorPolynomial.small_inverse_integral p 4
      (by norm_num) (by omega)⟩
  have hT (x : ℚ) (hx : x ≠ 0) (m : ℕ) :
      evaluate x hx (T (m : ℤ)) = x ^ m := by
    simpa using evaluate_monomial (m : ℤ) 1 x hx
  have hχ := actual_chi_Q_endpoints p hp
  dsimp only at hχ
  have hQ4 := congrArg (evaluate 4 (by norm_num))
    (shiftedChiQ_toLaurent p hp)
  have hQq := congrArg (evaluate (1 / 4) (by norm_num))
    (shiftedChiQ_toLaurent p hp)
  simp only [map_mul, evaluate_toLaurent, hT, hχ.1, hχ.2] at hQ4 hQq
  have hI4 : I.eval 4 =
      -(4 : integralRationals p) ^ p *
        (WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) := by
    apply Subtype.ext
    change (integralRationals p).subtype (I.eval 4) =
      -(4 : ℚ) ^ p * (WPFiniteInversion.integerFermatQuotient p 2 : ℚ)
    rw [← Polynomial.eval_map_apply, shiftedChiIntegral_rational]
    change (shiftedChiQ p).eval (4 : ℚ) =
      -(4 : ℚ) ^ p * (WPFiniteInversion.integerFermatQuotient p 2 : ℚ)
    linear_combination hQ4
  have hIq : (2 : integralRationals p) ^ (p - 1) * I.eval a =
      a ^ p * (WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) := by
    apply Subtype.ext
    change (2 : ℚ) ^ (p - 1) * (integralRationals p).subtype (I.eval a) =
      (1 / 4 : ℚ) ^ p * (WPFiniteInversion.integerFermatQuotient p 2 : ℚ)
    rw [← Polynomial.eval_map_apply, shiftedChiIntegral_rational]
    change (2 : ℚ) ^ (p - 1) * (shiftedChiQ p).eval (1 / 4) =
      (1 / 4 : ℚ) ^ p * (WPFiniteInversion.integerFermatQuotient p 2 : ℚ)
    rw [hQq]
    field_simp
  have haF : residueHom p a = (1 / 4 : ZMod p) := by
    change ((1 / 4 : ℚ) : ZMod p) = (1 / 4 : ZMod p)
    norm_num [Rat.cast_def]
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have hf4 := congrArg (residueHom p) hI4
  rw [← Polynomial.eval_map_apply] at hf4
  simp only [map_neg, map_mul, map_pow, map_ofNat, map_intCast] at hf4
  change (shiftedChiField p hp).eval 4 =
    -(4 : ZMod p) ^ p *
      (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) at hf4
  rw [ZMod.pow_card] at hf4
  have hfq := congrArg (residueHom p) hIq
  simp only [map_mul, map_pow, map_ofNat, map_intCast] at hfq
  rw [← Polynomial.eval_map_apply, haF,
    ZMod.pow_card_sub_one_eq_one h2, one_mul, ZMod.pow_card] at hfq
  change (shiftedChiField p hp).eval (1 / 4) =
    (1 / 4 : ZMod p) *
      (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) at hfq
  have hv : (fourUnit (K := ZMod p) p hp : ZMod p) = 4 := rfl
  have hs4 := congrArg (eval₂ (RingHom.id (ZMod p)) (fourUnit p hp))
    (shiftedChiField_toLaurent p hp)
  have hsq := congrArg (eval₂ (RingHom.id (ZMod p)) (fourUnit p hp)⁻¹)
    (shiftedChiField_toLaurent p hp)
  simp only [map_mul, eval₂_T_n, eval₂_toLaurent, Polynomial.eval₂_id,
    Units.val_inv_eq_inv_val, hv, inv_pow, ZMod.pow_card] at hs4 hsq
  simp only [one_div] at hfq
  constructor
  · apply mul_left_cancel₀ h4
    linear_combination hf4 - hs4
  · apply mul_left_cancel₀ (div_ne_zero one_ne_zero h4)
    linear_combination hfq - hsq

theorem finite_Pnumerator_endpoints (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (Pnumerator p u).eval 4 =
        -4 * (WPFiniteInversion.integerFermatQuotient p 2 : K) ∧
      (Pnumerator p u).eval (1 / 4) =
        (1 / 4 : K) * (WPFiniteInversion.integerFermatQuotient p 2 : K) := by
  have hu (m : ℕ) (hm : m ∈ Finset.Ico 1 p) : (m : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p m hm
  have h2 := hu 2 (Finset.mem_Ico.mpr (by omega))
  have h4 := hu 4 (Finset.mem_Ico.mpr (by omega))
  have h15 := hu 15 (Finset.mem_Ico.mpr (by omega))
  have h16 : (16 : K) ≠ 0 := by
    rw [show (16 : K) = 4 ^ 2 by ring]
    exact pow_ne_zero 2 h4
  have h60 : (60 : K) ≠ 0 := by
    rw [show (60 : K) = 4 * 15 by ring]
    exact mul_ne_zero h4 h15
  have heps : epsilon p ≠ (0 : K) :=
    pow_ne_zero _ (hu 5 (Finset.mem_Ico.mpr (by omega)))
  have h4p : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have hap : (1 / 4 : K) ^ p = 1 / 4 := by rw [div_pow, one_pow, h4p]
  have h42 : (4 : K) ^ (2 * p) = 16 := by
    rw [show 2 * p = p + p by omega, pow_add, h4p]; norm_num
  have ha2 : (1 / 4 : K) ^ (2 * p) = (1 / 4 : K) ^ 2 := by
    rw [show 2 * p = p + p by omega, pow_add, hap, pow_two]
  have h14 : (1 / 4 : K) * 4 = 1 := one_div_mul_cancel h4
  have h41 : (4 : K) * (1 / 4) = 1 := mul_one_div_cancel h4
  have hLP1 : (WPFiniteAffineLog.LP p : K[X]).eval 1 = 0 := by
    rw [LP_eval_eq]
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.ell_one_eq_zero p (by omega))
    simpa only [← WPFiniteField.ell_castHom, map_one, map_zero] using he
  have h2u := mul_inv_cancel₀ h2
  have h4u := mul_inv_cancel₀ h4
  have h15u := mul_inv_cancel₀ h15
  have h16u := mul_inv_cancel₀ h16
  have h60u := mul_inv_cancel₀ h60
  constructor <;>
    simp only [Pnumerator, A, B0, Bpoly, Cminus, uSlot, logTrace,
      logDifference, eval_add, eval_sub, eval_mul, eval_C, eval_pow,
      eval_X, eval_neg, eval_comp, WPFiniteNC122.q, h4p, hap,
      h42, ha2, h14, h41, hLP1] <;>
    field_simp [h2, h4, h15, h16, heps]
  · rw [show (4 : K) ^ 2 = 16 by ring]
    linear_combination
      (-4 * (WPFiniteInversion.integerFermatQuotient p 2 : K) * epsilon p +
        8 * epsilon p * (WPFiniteAffineLog.LP p : K[X]).eval 16 * (60 : K)⁻¹) * h15u -
      2 * epsilon p * (WPFiniteAffineLog.LP p : K[X]).eval 16 * (15 : K)⁻¹ * h60u +
      34 * (W p : K[X]).eval 4 * h2u
  · simp only [show (4 : K) ^ 2 = 16 by ring, one_div]
    linear_combination
      (4 * (WPFiniteInversion.integerFermatQuotient p 2 : K) * epsilon p * (16 : K)⁻¹ -
        128 * epsilon p * (WPFiniteAffineLog.LP p : K[X]).eval (16 : K)⁻¹ *
          (16 : K)⁻¹ * (60 : K)⁻¹) * h15u +
      ((WPFiniteInversion.integerFermatQuotient p 2 : K) * epsilon p *
          ((4 : K)⁻¹ - 4 * (15 : K)⁻¹) +
        4 * WPFifthEntropy.C p u * epsilon p * (15 : K)⁻¹ +
        2 * epsilon p * (WPFiniteAffineLog.LP p : K[X]).eval (16 : K)⁻¹ * (15 : K)⁻¹ +
        2 * (W p : K[X]).eval (4 : K)⁻¹) * h16u -
      4 * (WPFiniteInversion.integerFermatQuotient p 2 : K) * epsilon p * (16 : K)⁻¹ * h4u +
      32 * epsilon p * (WPFiniteAffineLog.LP p : K[X]).eval (16 : K)⁻¹ *
        (16 : K)⁻¹ * (15 : K)⁻¹ * h60u +
      34 * (W p : K[X]).eval (4 : K)⁻¹ * (16 : K)⁻¹ * h2u

theorem finite_P_endpoints (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    eval₂ (RingHom.id K) (fourUnit p hp) (P p u) =
        -(WPFiniteInversion.integerFermatQuotient p 2 : K) ∧
      eval₂ (RingHom.id K) (fourUnit p hp)⁻¹ (P p u) =
        (WPFiniteInversion.integerFermatQuotient p 2 : K) := by
  have hn := finite_Pnumerator_endpoints p hp u
  have hv : (fourUnit (K := K) p hp : K) = 4 := rfl
  have h4 : (4 : K) ≠ 0 := (fourUnit (K := K) p hp).ne_zero
  have h4p : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have hs4 := congrArg (eval₂ (RingHom.id K) (fourUnit p hp)) (P_numerator p u)
  have hsq := congrArg (eval₂ (RingHom.id K) (fourUnit p hp)⁻¹) (P_numerator p u)
  simp only [map_mul, eval₂_T_n, eval₂_toLaurent, Polynomial.eval₂_id,
    Units.val_inv_eq_inv_val, hv, inv_pow, h4p] at hs4 hsq
  simp only [one_div] at hn
  constructor
  · apply mul_left_cancel₀ h4; linear_combination hn.1 + hs4
  · apply mul_left_cancel₀ (div_ne_zero one_ne_zero h4)
    linear_combination hn.2 + hsq

noncomputable def zeta (p : ℕ) : K[T;T⁻¹] :=
  LaurentPolynomial.C (1 / 3 : K) * T (-(p : ℤ)) * (Abar : K[X]).toLaurent ^ p

theorem zeta_CB_endpoints (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (CB : K[T;T⁻¹]) :
    eval₂ (RingHom.id K) (fourUnit p hp) (zeta p * CB) = 0 ∧
      eval₂ (RingHom.id K) (fourUnit p hp)⁻¹ (zeta p * CB) = 0 := by
  have hv : (fourUnit (K := K) p hp : K) = 4 := rfl
  have h41 : (4 : K) * (1 / 4) = 1 :=
    mul_one_div_cancel (fourUnit (K := K) p hp).ne_zero
  have hA4 : (Abar : K[X]).eval 4 = 0 := by simp [Abar]
  have hAq : (Abar : K[X]).eval (1 / 4) = 0 := by
    simp only [Abar, eval_mul, eval_sub, eval_ofNat, eval_X,
      eval_one, h41, sub_self, mul_zero]
  have hAqi : (Abar : K[X]).eval (4 : K)⁻¹ = 0 := by
    simpa only [one_div] using hAq
  constructor
  · simp only [zeta, map_mul, map_pow, eval₂_toLaurent,
      Polynomial.eval₂_id, hv, hA4,
      zero_pow (by omega : p ≠ 0), mul_zero, zero_mul]
  · simp only [zeta, map_mul, map_pow, eval₂_toLaurent,
      Polynomial.eval₂_id, Units.val_inv_eq_inv_val, hv, hAqi,
      zero_pow (by omega : p ≠ 0), mul_zero, zero_mul]

end WPFieldAssembly.ActualChiEndpoints
