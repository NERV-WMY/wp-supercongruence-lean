import WPFieldAssembly.ResidualProjection
import WPActualNativeRemainderSource

open scoped Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource
  WPActualEtaPole WPActualChiSource WPActualPositiveResidueSource
  WPActualEtaSupport WPActualNativeRemainderSource

namespace WPFieldAssembly.OriginalLaurentDensity

noncomputable def D : ℚ[T;T⁻¹] :=
  (T 1 - C (1 / 4)) * (T 1 - C 4)
noncomputable def K : ℚ[T;T⁻¹] :=
  C 2 * (T 1 - C 4) + (T 1 - C (1 / 4))
noncomputable def Frev_inverse : ℚ[T;T⁻¹] :=
  invert (WPFiniteNC122Residue.Frev : ℚ[X]).toLaurent
noncomputable def reciprocalDensity (G : ℚ[X]) : ℚ[T;T⁻¹] :=
  invert (WPFiniteNC122Residue.canceledDensity G).toLaurent
noncomputable def O (p j : ℕ) (G : ℚ[X]) : ℚ :=
  (weightedDifference (T (((p - 1) / 2 : ℕ) : ℤ) * substitute G Qx)).coeff
    (-(j : ℤ) * (p : ℤ) - 1)

theorem Qrev_eq_Vpolynomial : (WPFiniteNC122Residue.Qrev : ℚ[X]) = Vpolynomial := by
  apply Polynomial.funext
  intro x
  simp only [WPFiniteNC122Residue.Qrev, Vpolynomial,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  ring

theorem Frev_factored : (WPFiniteNC122Residue.Frev : ℚ[X]) =
    Polynomial.C (1 / 125 : ℚ) * 3 * Polynomial.X *
      (4 * Polynomial.X - 1) * (11 * Polynomial.X - 4) := by
  apply Polynomial.funext
  intro x
  simp only [WPFiniteNC122Residue.Frev, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  ring

theorem Qx_inverse_factor :
    Qx = C (1 / 125 : ℚ) * (4 * T (-1) - 1) ^ 2 * (4 - T (-1)) := by
  rw [← actual_Vx_reciprocal]
  simp only [Vx, Vpolynomial, map_mul, map_pow, map_sub, map_ofNat, map_one,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X, invert_C, invert_T]

theorem Frev_inverse_factor : Frev_inverse = C (1 / 125 : ℚ) * 3 * T (-1) *
    (4 * T (-1) - 1) * (11 * T (-1) - 4) := by
  unfold Frev_inverse
  rw [Frev_factored]
  simp only [map_mul, map_sub, map_ofNat, map_one,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X, invert_C, invert_T]

theorem endpoint_clearing (L : ℚ[T;T⁻¹]) :
    D * weightedDifference L = K * L -
      C 2 * (T 1 - C 4) * C (evaluate (1 / 4) (by norm_num) L) -
      (T 1 - C (1 / 4)) * C (evaluate 4 (by norm_num) L) := by
  have ha := dividedDifference_identity (1 / 4) (by norm_num) L
  have hb := dividedDifference_identity 4 (by norm_num) L
  unfold D K
  rw [weightedDifference_apply]
  linear_combination C 2 * (T 1 - C 4) * ha + (T 1 - C (1 / 4)) * hb

theorem endpoint_clearing_zero (L : ℚ[T;T⁻¹])
    (ha : evaluate (1 / 4) (by norm_num) L = 0)
    (hb : evaluate 4 (by norm_num) L = 0) :
    D * weightedDifference L = K * L := by
  rw [endpoint_clearing, ha, hb, map_zero]
  ring

theorem D_ne_zero : D ≠ 0 := by
  have hf (a : ℚ) : (T 1 - C a : ℚ[T;T⁻¹]) ≠ 0 := by
    intro hz
    have hh := congrArg (fun L : ℚ[T;T⁻¹] => L.coeff 1) hz
    norm_num [AddMonoidAlgebra.coeff_sub] at hh
  exact mul_ne_zero (hf (1 / 4)) (hf 4)

/-- Exact cancellation of both original endpoint factors. -/
theorem D_mul_Frev_inverse : D * Frev_inverse = K * Qx := by
  have htu : (T 1 : ℚ[T;T⁻¹]) * T (-1) = 1 := by rw [← T_add]; norm_num
  have hut : (T (-1) : ℚ[T;T⁻¹]) * T 1 = 1 := by simpa only [mul_comm] using htu
  have hquarter : (4 : ℚ[T;T⁻¹]) * C (1 / 4 : ℚ) = 1 := by
    calc
      _ = C ((4 : ℚ) * (1 / 4)) := by simp only [map_mul, map_ofNat]
      _ = 1 := by norm_num
  have ha : (T 1 - C (1 / 4) : ℚ[T;T⁻¹]) =
      C (1 / 4 : ℚ) * (4 - T (-1)) * T 1 := by
    symm
    calc
      _ = (4 * C (1 / 4 : ℚ)) * T 1 - C (1 / 4 : ℚ) * (T (-1) * T 1) := by ring
      _ = _ := by rw [hquarter, hut]; ring
  have hb : (T 1 - C 4 : ℚ[T;T⁻¹]) = -(4 * T (-1) - 1) * T 1 := by
    norm_num only [map_ofNat]
    calc
      _ = T 1 - 4 * (T (-1) * T 1) := by rw [hut, mul_one]
      _ = _ := by ring
  have hK : K = -3 * C (1 / 4 : ℚ) * (11 * T (-1) - 4) * T 1 := by
    unfold K
    norm_num only [map_ofNat]
    linear_combination (-3 * T 1 + 8) * hquarter + 33 * C (1 / 4 : ℚ) * hut
  rw [D, ha, hb, hK, Qx_inverse_factor, Frev_inverse_factor]
  calc
    _ = (-3 * C (1 / 4 : ℚ) * (11 * T (-1) - 4) * T 1) *
        (C (1 / 125 : ℚ) * (4 * T (-1) - 1) ^ 2 * (4 - T (-1))) *
        (T 1 * T (-1)) := by ring
    _ = _ := by rw [htu, mul_one]

theorem reciprocalDensity_factor (G : ℚ[X]) :
    reciprocalDensity G = substitute G.divX Qx * Frev_inverse := by
  have hc : invert (G.divX.comp (WPFiniteNC122Residue.Qrev : ℚ[X])).toLaurent =
      substitute G.divX Qx := by
    calc
      _ = invert (substituteOver G.divX (WPFiniteNC122Residue.Qrev : ℚ[X]).toLaurent) := by
        rw [substituteOver_toLaurent]
      _ = substituteOver G.divX Qx := by
        rw [substituteOver_invert, Qrev_eq_Vpolynomial]
        change substituteOver G.divX (invert Vx) = _
        rw [actual_Vx_reciprocal]
      _ = _ := rfl
  unfold reciprocalDensity WPFiniteNC122Residue.canceledDensity
  rw [map_mul, map_mul, hc]
  rfl

theorem whole_cancellation_zero (M : ℕ) (G : ℚ[X]) (hG : G.coeff 0 = 0) :
    weightedDifference (T (M : ℤ) * substitute G Qx) =
      T (M : ℤ) * reciprocalDensity G := by
  have hd : Polynomial.X * G.divX = G := by
    simpa only [hG, map_zero, add_zero] using Polynomial.X_mul_divX_add G
  have hs : Qx * substitute G.divX Qx = substitute G Qx := by
    have hh := congrArg (Polynomial.eval₂RingHom C Qx) hd
    simpa only [substitute, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using hh
  have he (a : ℚ) (ha : a ≠ 0) (hQ : evaluate a ha Qx = 0) :
      evaluate a ha (T (M : ℤ) * substitute G Qx) = 0 := by
    rw [map_mul, evaluate_substitute, hQ, ← Polynomial.coeff_zero_eq_eval_zero, hG, mul_zero]
  have ha := he (1 / 4) (by norm_num) (by rw [evaluate_Qx]; norm_num)
  have hb := he 4 (by norm_num) (by rw [evaluate_Qx]; norm_num)
  apply mul_left_cancel₀ D_ne_zero
  calc
    D * weightedDifference (T (M : ℤ) * substitute G Qx) =
        K * (T (M : ℤ) * substitute G Qx) := endpoint_clearing_zero _ ha hb
    _ = D * (T (M : ℤ) * reciprocalDensity G) := by
      rw [reciprocalDensity_factor]
      calc
        _ = T (M : ℤ) * ((K * Qx) * substitute G.divX Qx) := by rw [← hs]; ring
        _ = _ := by rw [← D_mul_Frev_inverse]; ring

/-- The omitted constant is retained as an explicit regular Laurent term. -/
theorem whole_cancellation (M : ℕ) (G : ℚ[X]) :
    weightedDifference (T (M : ℤ) * substitute G Qx) =
      T (M : ℤ) * reciprocalDensity G +
        weightedDifference (T (M : ℤ) * C (G.coeff 0)) := by
  let H : ℚ[X] := G - Polynomial.C (G.coeff 0)
  have hH : H.coeff 0 = 0 := by simp [H]
  have hs : substitute G Qx = substitute H Qx + C (G.coeff 0) := by
    simp only [H, substitute, map_sub, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    ring
  have hc : reciprocalDensity H = reciprocalDensity G := by
    unfold reciprocalDensity H
    rw [WPFieldAssembly.ResidualProjection.canceledDensity_sub_constant]
  rw [hs, mul_add, map_add, whole_cancellation_zero M H hH, hc]

theorem constant_negative_coefficient (M k : ℕ) (c : ℚ) :
    (weightedDifference (T (M : ℤ) * C c)).coeff (-(k : ℤ) - 1) = 0 := by
  have hm : bounded (T (M : ℤ) * C c) 0 ((M : ℤ) + 1) :=
    bounded_mono (bounded_mul (bounded_T _) (bounded_C c)) (by omega) (by omega)
  have hw := weightedDifference_bounded (T (M : ℤ) * C c) 0 ((M : ℤ) + 1)
    (by omega) (by omega) hm
  by_contra hh
  have hnonnegative := (hw (-(k : ℤ) - 1) hh).1
  omega

theorem reciprocalDensity_negative_coefficient (M k : ℕ) (G : ℚ[X]) :
    (T (M : ℤ) * reciprocalDensity G).coeff (-(k : ℤ) - 1) =
      (WPFiniteNC122Residue.canceledDensity G).coeff (M + k + 1) := by
  have hs := WPFiniteJCarrier.shifted_coeff (1 : ℚ) (M : ℤ) (-(k : ℤ) - 1) (reciprocalDensity G)
  simp only [map_one, one_mul] at hs
  rw [hs, reciprocalDensity, LaurentPolynomial.invert_apply,
    show -(-(k : ℤ) - 1 - (M : ℤ)) = ((M + k + 1 : ℕ) : ℤ) by omega,
    WPFiniteJCarrier.toLaurent_coeff_nat]

theorem original_negative_projection (M k : ℕ) (G : ℚ[X]) :
    (weightedDifference (T (M : ℤ) * substitute G Qx)).coeff (-(k : ℤ) - 1) =
      (WPFiniteNC122Residue.canceledDensity G).coeff (M + k + 1) := by
  rw [whole_cancellation, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    constant_negative_coefficient, add_zero, reciprocalDensity_negative_coefficient]

theorem O_eq_Ij (p j : ℕ) (G : ℚ[X]) :
    O p j G = WPFieldAssembly.ResidualProjection.Ij p j G := by
  unfold O WPFieldAssembly.ResidualProjection.Ij
  simpa only [Nat.cast_mul, neg_mul] using original_negative_projection ((p - 1) / 2) (j * p) G

end WPFieldAssembly.OriginalLaurentDensity
