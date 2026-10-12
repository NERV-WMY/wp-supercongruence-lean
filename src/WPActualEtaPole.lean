import WPActualLogarithmicEta

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource WPActualLogarithmicEta

namespace WPActualEtaPole

/-- The positive geometric quotient, with its entire coefficient support. -/
noncomputable def forwardQuotient (a : ℚ) : ℕ → ℚ[T;T⁻¹]
  | 0 => 0
  | n + 1 => T (n : ℤ) + C a * forwardQuotient a n

theorem forwardQuotient_identity (a : ℚ) (n : ℕ) :
    (T 1 - C a) * forwardQuotient a n = T (n : ℤ) - C (a ^ n) := by
  induction n with
  | zero => simp [forwardQuotient]
  | succ n ih =>
    rw [forwardQuotient, mul_add]
    calc
      _ = T 1 * T (n : ℤ) - C a * T (n : ℤ) +
          C a * ((T 1 - C a) * forwardQuotient a n) := by ring
      _ = _ := by
        rw [ih, ← T_add, pow_succ, map_mul]
        push_cast
        ring

/-- The unique monomial quotient by x-a, including all negative powers. -/
noncomputable def monomialQuotient (a : ℚ) : ℤ → ℚ[T;T⁻¹]
  | .ofNat n => forwardQuotient a n
  | .negSucc n => -C (a ^ (-(n + 1 : ℤ))) * T (-(n + 1 : ℤ)) *
      forwardQuotient a (n + 1)

theorem monomialQuotient_identity (a : ℚ) (ha : a ≠ 0) (n : ℤ) :
    (T 1 - C a) * monomialQuotient a n = T n - C (a ^ n) := by
  cases n with
  | ofNat n => simpa [monomialQuotient] using forwardQuotient_identity a n
  | negSucc n =>
    rw [monomialQuotient]
    calc
      _ = -C (a ^ (-(n + 1 : ℤ))) * T (-(n + 1 : ℤ)) *
          ((T 1 - C a) * forwardQuotient a (n + 1)) := by ring
      _ = T (Int.negSucc n) - C (a ^ Int.negSucc n) := by
        rw [forwardQuotient_identity]
        have hexp : -(n + 1 : ℤ) + (n + 1 : ℕ) = 0 := by omega
        have hpow : a ^ (-(n + 1 : ℤ)) * a ^ (n + 1) = 1 := by
          rw [← zpow_natCast, ← zpow_add₀ ha, hexp, zpow_zero]
        calc
          _ = -C (a ^ (-(n + 1 : ℤ))) *
              (T (-(n + 1 : ℤ)) * T ((n + 1 : ℕ) : ℤ)) +
              C (a ^ (-(n + 1 : ℤ)) * a ^ (n + 1)) * T (-(n + 1 : ℤ)) := by
                rw [map_mul]; ring
          _ = _ := by
            rw [← T_add, hexp, T_zero, mul_one, hpow, map_one, one_mul,
              show Int.negSucc n = -(n + 1 : ℤ) by omega]
            ring

noncomputable def dividedDifference (a : ℚ) : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ[T;T⁻¹] :=
  (Finsupp.linearCombination ℚ (monomialQuotient a)).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem dividedDifference_monomial (a c : ℚ) (n : ℤ) :
    dividedDifference a (C c * T n) = C c * monomialQuotient a n := by
  rw [← single_eq_C_mul_T]
  change Finsupp.linearCombination ℚ _ (Finsupp.single n c) = _
  rw [Finsupp.linearCombination_single, smul_eq_C_mul]

theorem dividedDifference_identity (a : ℚ) (ha : a ≠ 0) (P : ℚ[T;T⁻¹]) :
    (T 1 - C a) * dividedDifference a P = P - C (evaluate a ha P) := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, mul_add, hP, hQ, map_add, map_add]
    ring
  | C_mul_T n c =>
    rw [dividedDifference_monomial, evaluate_monomial, map_mul]
    calc
      _ = C c * ((T 1 - C a) * monomialQuotient a n) := by ring
      _ = _ := by rw [monomialQuotient_identity a ha n]; ring

theorem dividedDifference_unique (a : ℚ) (ha : a ≠ 0) (P D : ℚ[T;T⁻¹])
    (hD : (T 1 - C a) * D = P - C (evaluate a ha P)) :
    D = dividedDifference a P := by
  have hfactor : (T 1 - C a : ℚ[T;T⁻¹]) ≠ 0 := by
    intro h
    have hh := congrArg (fun L : ℚ[T;T⁻¹] => L.coeff 1) h
    norm_num [AddMonoidAlgebra.coeff_sub] at hh
  exact mul_left_cancel₀ hfactor (hD.trans (dividedDifference_identity a ha P).symm)

noncomputable def Vx : ℚ[T;T⁻¹] := Polynomial.toLaurent Vpolynomial
noncomputable def Qx : ℚ[T;T⁻¹] :=
  C (1 / 125) * (4 * T 1 - 1) * (4 - T 1) ^ 2 * T (-3)
noncomputable def chiX (p N e : ℕ) : ℚ[T;T⁻¹] :=
  C (1 / (p : ℚ)) * (Fpull e Vx - T (N : ℤ) * Fpull e Qx)
noncomputable def HX (e : ℕ) : ℚ[T;T⁻¹] := Hpull e Vx
noncomputable def AX (p N e : ℕ) : ℚ[T;T⁻¹] := chiX p N e + HX e

theorem evaluate_Vx (a : ℚ) (ha : a ≠ 0) :
    evaluate a ha Vx = (4 * a - 1) ^ 2 * (4 - a) / 125 := by
  rw [Vx, evaluate_toLaurent]
  simp [Vpolynomial]
  ring

theorem evaluate_Qx (a : ℚ) (ha : a ≠ 0) :
    evaluate a ha Qx = (4 * a - 1) * (4 - a) ^ 2 / (125 * a ^ 3) := by
  have hT (z : ℤ) : evaluate a ha (T z) = a ^ z := by
    simpa using evaluate_monomial z 1 a ha
  simp only [Qx, map_mul, map_sub, map_pow, map_ofNat, map_one, evaluate_C, hT]
  norm_num [zpow_neg, zpow_natCast]
  ring

theorem evaluate_Fpull_zero (e : ℕ) (L : ℚ[T;T⁻¹]) (a : ℚ) (ha : a ≠ 0)
    (hL : evaluate a ha L = 0) : evaluate a ha (Fpull e L) = 1 := by
  rw [Fpull, evaluate_substitute, hL, ← Polynomial.coeff_zero_eq_eval_zero,
    WPReview.nativePolynomial_coeff]
  simp [WPReview.nativeCoefficient_zero]

theorem actual_AX_endpoints (p N e : ℕ) :
    evaluate (1 / 4) (by norm_num) (AX p N e) = (1 - (1 / 4 : ℚ) ^ N) / p ∧
    evaluate 4 (by norm_num) (AX p N e) = (1 - (4 : ℚ) ^ N) / p := by
  have hVa : evaluate (1 / 4) (by norm_num) Vx = 0 := by rw [evaluate_Vx]; norm_num
  have hVb : evaluate 4 (by norm_num) Vx = 0 := by rw [evaluate_Vx]; norm_num
  have hQa : evaluate (1 / 4) (by norm_num) Qx = 0 := by rw [evaluate_Qx]; norm_num
  have hQb : evaluate 4 (by norm_num) Qx = 0 := by rw [evaluate_Qx]; norm_num
  constructor
  · simp only [AX, chiX, HX, Hpull, map_add, map_mul, map_sub, evaluate_C,
      evaluate_Fpull_zero e Vx _ _ hVa, evaluate_Fpull_zero e Qx _ _ hQa,
      evaluate_substitute, hVa, Hpolynomial_zero]
    have hT : evaluate (1 / 4) (by norm_num) (T (N : ℤ)) = (1 / 4 : ℚ) ^ N := by
      simpa using evaluate_monomial (N : ℤ) 1 (1 / 4) (by norm_num)
    rw [hT]
    ring
  · simp only [AX, chiX, HX, Hpull, map_add, map_mul, map_sub, evaluate_C,
      evaluate_Fpull_zero e Vx _ _ hVb, evaluate_Fpull_zero e Qx _ _ hQb,
      evaluate_substitute, hVb, Hpolynomial_zero]
    have hT : evaluate 4 (by norm_num) (T (N : ℤ)) = (4 : ℚ) ^ N := by
      simpa using evaluate_monomial (N : ℤ) 1 4 (by norm_num)
    rw [hT]
    ring

noncomputable def linearPole (a : ℚ) : RatFunc ℚ := rationalVariable - algebraMap ℚ _ a

theorem ratify_linear (a : ℚ) : ratify (T 1 - C a) = linearPole a := by
  simp [ratify, linearPole, eval₂_T, rationalVariable]

theorem linearPole_ne_zero (a : ℚ) : linearPole a ≠ 0 := by
  rw [← ratify_linear]
  have hn : (T 1 - C a : ℚ[T;T⁻¹]) ≠ 0 := by
    intro h
    have hh := congrArg (fun L : ℚ[T;T⁻¹] => L.coeff 1) h
    norm_num [AddMonoidAlgebra.coeff_sub] at hh
  simpa using ratify_injective.ne hn

theorem derivative_toLaurent (P : ℚ[X]) :
    derivative (Polynomial.toLaurent P) = Polynomial.toLaurent (Polynomial.derivative P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial n a =>
    cases n with
    | zero => simp [derivative_C]
    | succ n => simp [derivative_monomial, Polynomial.derivative_monomial_succ]

theorem actual_dlogVx : dlog Vx = 2 / linearPole (1 / 4) + 1 / linearPole 4 := by
  rw [dlog, Vx, derivative_toLaurent, ratify_toLaurent, ratify_toLaurent,
    Vpolynomial_derivative]
  have hC (a : ℚ) : algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.C a) =
      algebraMap ℚ (RatFunc ℚ) a := (IsScalarTower.algebraMap_apply ℚ ℚ[X] (RatFunc ℚ) a).symm
  simp only [Vpolynomial, map_mul, map_pow, map_sub, map_ofNat, map_one, hC,
    map_div₀]
  change (3 / 125 : RatFunc ℚ) * (4 * rationalVariable - 1) * (11 - 4 * rationalVariable) /
    ((1 / 125 : RatFunc ℚ) * (4 * rationalVariable - 1) ^ 2 * (4 - rationalVariable)) = _
  have h1 := linearPole_ne_zero (1 / 4)
  have h4 := linearPole_ne_zero 4
  simp only [linearPole, map_div₀, map_ofNat, map_one] at h1 h4 ⊢
  have hformula {K : Type} [Field K] [CharZero K] (Y : K)
      (h1 : Y - 1 / 4 ≠ 0) (h4 : Y - 4 ≠ 0) :
      (3 / 125 : K) * (4 * Y - 1) * (11 - 4 * Y) /
        ((1 / 125 : K) * (4 * Y - 1) ^ 2 * (4 - Y)) =
        2 / (Y - 1 / 4) + 1 / (Y - 4) := by
    have h41 : 4 * Y - 1 ≠ 0 := by
      rw [show 4 * Y - 1 = 4 * (Y - 1 / 4) by ring]
      exact mul_ne_zero (by norm_num) h1
    have h4x : 4 - Y ≠ 0 := by
      intro h
      apply h4
      linear_combination -h
    field_simp [h1, h4, h41, h4x]
    ring
  exact hformula rationalVariable h1 h4

/-- The original eta coefficient in x, retaining chi, He and the square-root term. -/
noncomputable def etaX (p N e : ℕ) : RatFunc ℚ :=
  ratify (chiX p N e) * dlog Vx + ratify (HX e) *
    (dlog Vx - 1 / (2 * rationalVariable))

noncomputable def endpointPole (p N : ℕ) : RatFunc ℚ :=
  2 * algebraMap ℚ _ ((1 - (1 / 4 : ℚ) ^ N) / p) / linearPole (1 / 4) +
    algebraMap ℚ _ ((1 - (4 : ℚ) ^ N) / p) / linearPole 4

/-- The actual pole-subtracted Laurent polynomial, with no source coefficient removed. -/
noncomputable def Peta (p N e : ℕ) : ℚ[T;T⁻¹] :=
  C 2 * dividedDifference (1 / 4) (AX p N e) + dividedDifference 4 (AX p N e) -
    C (1 / 2) * HX e * T (-1)

theorem actual_eta_pole_subtraction (p N e : ℕ) :
    etaX p N e - endpointPole p N = ratify (Peta p N e) := by
  have ha := dividedDifference_identity (1 / 4) (by norm_num) (AX p N e)
  have hb := dividedDifference_identity 4 (by norm_num) (AX p N e)
  have he := actual_AX_endpoints p N e
  rw [he.1] at ha
  rw [he.2] at hb
  have hqa := congrArg ratify ha
  have hqb := congrArg ratify hb
  rw [map_mul, ratify_linear, map_sub, ratify_C] at hqa hqb
  have hT : ratify (T (-1)) = rationalVariable⁻¹ := by simp [ratify, eval₂_T]
  have hAX : ratify (AX p N e) = ratify (chiX p N e) + ratify (HX e) := by
    simp only [AX, map_add]
  rw [hAX] at hqa hqb
  have h1 := linearPole_ne_zero (1 / 4)
  have h4 := linearPole_ne_zero 4
  have hda : ratify (dividedDifference (1 / 4) (AX p N e)) =
      (ratify (chiX p N e) + ratify (HX e) -
        algebraMap ℚ _ ((1 - (1 / 4 : ℚ) ^ N) / p)) / linearPole (1 / 4) := by
    apply (eq_div_iff h1).mpr
    linear_combination hqa
  have hdb : ratify (dividedDifference 4 (AX p N e)) =
      (ratify (chiX p N e) + ratify (HX e) -
        algebraMap ℚ _ ((1 - (4 : ℚ) ^ N) / p)) / linearPole 4 := by
    apply (eq_div_iff h4).mpr
    linear_combination hqb
  rw [etaX, endpointPole, actual_dlogVx, Peta]
  simp only [map_sub, map_add, map_mul, ratify_C, hT]
  rw [hda, hdb]
  norm_num
  simp only [div_eq_mul_inv]
  ring

end WPActualEtaPole
