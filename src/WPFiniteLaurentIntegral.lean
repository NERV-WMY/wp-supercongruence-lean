import WPFiniteGammaIntegral
import WPFiniteConductorReflection
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open scoped BigOperators LaurentPolynomial Polynomial

namespace WPFiniteLaurentIntegral

open LaurentPolynomial

noncomputable def derivative : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ[T;T⁻¹] :=
  (Finsupp.linearCombination ℚ (fun n : ℤ => C (n : ℚ) * T (n - 1))).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

noncomputable def endpointIntegral (a b : ℚ) : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ :=
  (Finsupp.linearCombination ℚ
    (fun n : ℤ => WPFiniteConductorReflection.monomialEndpoint (n + 1) a b)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

noncomputable def evaluate (a : ℚ) (ha : a ≠ 0) : ℚ[T;T⁻¹] →+* ℚ :=
  eval₂ (RingHom.id ℚ) (Units.mk0 a ha)

theorem derivative_monomial (n : ℤ) (a : ℚ) :
    derivative (C a * T n) = C (a * (n : ℚ)) * T (n - 1) := by
  rw [← single_eq_C_mul_T]
  change Finsupp.linearCombination ℚ _ (Finsupp.single n a) = _
  rw [Finsupp.linearCombination_single]
  rw [smul_eq_C_mul, ← mul_assoc, ← map_mul]

theorem integral_monomial (n : ℤ) (c a b : ℚ) :
    endpointIntegral a b (C c * T n) =
      c * WPFiniteConductorReflection.monomialEndpoint (n + 1) a b := by
  rw [← single_eq_C_mul_T]
  change Finsupp.linearCombination ℚ _ (Finsupp.single n c) = _
  rw [Finsupp.linearCombination_single]
  rfl

theorem evaluate_monomial (n : ℤ) (c a : ℚ) (ha : a ≠ 0) :
    evaluate a ha (C c * T n) = c * a ^ n := by
  simp [evaluate, eval₂_C_mul_T]

theorem evaluate_C (c a : ℚ) (ha : a ≠ 0) : evaluate a ha (C c) = c := by
  simpa using evaluate_monomial 0 c a ha

theorem evaluate_toLaurent (P : ℚ[X]) (a : ℚ) (ha : a ≠ 0) :
    evaluate a ha (Polynomial.toLaurent P) = P.eval a := by
  rw [evaluate, eval₂_toLaurent]
  rfl

/-- Exact finite antiderivative evaluation; the logarithmic coefficient cancels automatically. -/
theorem integral_derivative (P : ℚ[T;T⁻¹]) (a b : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    endpointIntegral a b (derivative P) = evaluate b hb P - evaluate a ha P := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, map_add, hP, hQ, map_add, map_add]
    ring
  | C_mul_T n c =>
    rw [derivative_monomial, integral_monomial, evaluate_monomial, evaluate_monomial]
    rw [show n - 1 + 1 = n by omega]
    by_cases hn : n = 0
    · simp [hn]
    · have hnq : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
      unfold WPFiniteConductorReflection.monomialEndpoint
      field_simp [hnq]

theorem monomial_mul (n m : ℤ) (a b : ℚ) :
    (C a * T n) * (C b * T m) = C (a * b) * T (n + m) := by
  rw [map_mul, T_add]
  ring

/-- The finite Laurent derivative obeys the actual product rule. -/
theorem derivative_mul (P Q : ℚ[T;T⁻¹]) :
    derivative (P * Q) = derivative P * Q + P * derivative Q := by
  induction P using LaurentPolynomial.induction_on' with
  | add P1 P2 h1 h2 =>
    rw [add_mul, map_add, h1, h2, map_add]
    ring
  | C_mul_T n a =>
    induction Q using LaurentPolynomial.induction_on' with
    | add Q1 Q2 h1 h2 =>
      rw [mul_add, map_add, h1, h2, map_add]
      ring
    | C_mul_T m b =>
      rw [monomial_mul, derivative_monomial, derivative_monomial, derivative_monomial,
        monomial_mul, monomial_mul]
      rw [show n - 1 + m = n + m - 1 by omega,
        show n + (m - 1) = n + m - 1 by omega]
      rw [← add_mul, ← map_add]
      congr 2
      push_cast
      ring

theorem derivative_C (a : ℚ) : derivative (C a) = 0 := by
  simpa using derivative_monomial 0 a

theorem derivative_pow_succ (P : ℚ[T;T⁻¹]) (n : ℕ) :
    derivative (P ^ (n + 1)) = C ((n : ℚ) + 1) * P ^ n * derivative P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ P (n + 1), derivative_mul, ih]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one, pow_succ]
    ring

noncomputable def substitute (P : ℚ[X]) (L : ℚ[T;T⁻¹]) : ℚ[T;T⁻¹] :=
  Polynomial.eval₂RingHom C L P

theorem derivative_substitute (P : ℚ[X]) (L : ℚ[T;T⁻¹]) :
    derivative (substitute P L) = substitute (Polynomial.derivative P) L * derivative L := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [substitute, Polynomial.coe_eval₂RingHom,
      map_add] at *
    rw [hP, hQ]
    ring
  | monomial n a =>
    cases n with
    | zero => simp [substitute, derivative_C]
    | succ n =>
      simp only [substitute, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_monomial, Polynomial.derivative_monomial_succ,
        derivative_mul, derivative_C, zero_mul, zero_add, derivative_pow_succ,
        map_mul]
      ring

theorem evaluate_substitute (P : ℚ[X]) (L : ℚ[T;T⁻¹]) (a : ℚ) (ha : a ≠ 0) :
    evaluate a ha (substitute P L) = P.eval (evaluate a ha L) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [substitute, Polynomial.coe_eval₂RingHom,
      Polynomial.eval_add, map_add] at *
    rw [hP, hQ]
  | monomial n c =>
    simp [substitute, evaluate, eval₂_C, Polynomial.eval₂_monomial]

noncomputable def polynomialPrimitive (P : ℚ[X]) : ℚ[X] :=
  P.sum (fun n a => Polynomial.monomial (n + 1) (a / ((n : ℚ) + 1)))

theorem polynomialPrimitive_add (P Q : ℚ[X]) :
    polynomialPrimitive (P + Q) = polynomialPrimitive P + polynomialPrimitive Q := by
  unfold polynomialPrimitive
  apply Polynomial.sum_add_index
  · intro n; simp
  · intro n a b
    rw [add_div, map_add]

theorem derivative_polynomialPrimitive (P : ℚ[X]) :
    Polynomial.derivative (polynomialPrimitive P) = P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [polynomialPrimitive_add, Polynomial.derivative_add, hP, hQ]
  | monomial n a =>
    have hn : (n : ℚ) + 1 ≠ 0 := by positivity
    simp [polynomialPrimitive, Polynomial.derivative_monomial_succ, hn]

/-- The exact original conic coordinate after s=2r. -/
noncomputable def V : ℚ[T;T⁻¹] := C (2 / 3) * T 1 - C (2 / 3) * T (-1)

theorem evaluate_V (a : ℚ) (ha : a ≠ 0) :
    evaluate a ha V = (2 / 3) * (a - 1 / a) := by
  rw [V, map_sub, evaluate_monomial, evaluate_monomial]
  simp only [zpow_one, zpow_neg_one, one_div]
  ring

theorem evaluate_derivative_V (a : ℚ) (ha : a ≠ 0) :
    evaluate a ha (derivative V) = (2 / 3) * (1 + 1 / a ^ 2) := by
  rw [V, map_sub, derivative_monomial, derivative_monomial]
  norm_num [evaluate_monomial, evaluate_C, zpow_neg, zpow_ofNat]
  ring

/-- Finite Gamma becomes the exact conic Laurent primitive, with U=0 and U=1 retained. -/
theorem Gamma_finite_pullback (P : ℚ[X]) (L : ℕ) (hL : P.natDegree ≤ L) :
    endpointIntegral 1 2
      (substitute (P.comp WPFiniteGammaIntegral.quadraticArgument) V * derivative V) =
      WPReview.Gamma L (fun k => P.coeff k) := by
  let Q := P.comp WPFiniteGammaIntegral.quadraticArgument
  have hD := derivative_substitute (polynomialPrimitive Q) V
  rw [derivative_polynomialPrimitive] at hD
  rw [← hD, integral_derivative _ 1 2 (by norm_num) (by norm_num),
    evaluate_substitute, evaluate_substitute, evaluate_V, evaluate_V]
  norm_num
  rw [WPFiniteGammaIntegral.Gamma_eq_integral P L hL]
  have h := WPFiniteGammaIntegral.integral_derivative (polynomialPrimitive Q)
  rw [derivative_polynomialPrimitive] at h
  exact h.symm

noncomputable def evaluateInteger (n : ℕ) : ℚ[T;T⁻¹] →+* ℚ :=
  evaluate ((n : ℚ) + 3) (by positivity)

/-- Finite Laurent equality is determined by its universal integer evaluations. -/
theorem ext_positive_integers (P Q : ℚ[T;T⁻¹])
    (h : ∀ n : ℕ, evaluateInteger n P = evaluateInteger n Q) : P = Q := by
  let A := P - Q
  obtain ⟨k, F, hF⟩ := LaurentPolynomial.exists_T_pow A
  have hzero : ∀ n : ℕ, evaluateInteger n A = 0 := by
    intro n
    change evaluateInteger n (P - Q) = 0
    rw [map_sub, h n, sub_self]
  have hFeval : ∀ n : ℕ, F.eval ((n : ℚ) + 3) = 0 := by
    intro n
    calc
      F.eval ((n : ℚ) + 3) = evaluateInteger n (Polynomial.toLaurent F) :=
        (evaluate_toLaurent F _ _).symm
      _ = evaluateInteger n (A * T (k : ℤ)) := congrArg (evaluateInteger n) hF
      _ = 0 := by rw [map_mul, hzero n, zero_mul]
  have hi : Function.Injective (fun n : ℕ => (n : ℚ) + 3) := by
    intro i j hij
    have hcast : (i : ℚ) = (j : ℚ) := add_right_cancel hij
    exact_mod_cast hcast
  have hinf := Set.infinite_range_of_injective hi
  have hroots : Set.range (fun n : ℕ => (n : ℚ) + 3) ⊆ {a | Polynomial.IsRoot F a} := by
    rintro a ⟨n, rfl⟩
    exact hFeval n
  have hFzero := Polynomial.eq_zero_of_infinite_isRoot F (hinf.mono hroots)
  rw [hFzero, map_zero] at hF
  have hA : A = 0 := by
    have hmul := congrArg (fun L : ℚ[T;T⁻¹] => L * T (-(k : ℤ))) hF
    simp only [zero_mul, mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one] at hmul
    exact hmul.symm
  exact sub_eq_zero.mp hA

end WPFiniteLaurentIntegral
