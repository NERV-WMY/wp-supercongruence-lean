import WPRationalCartier

open scoped Polynomial LaurentPolynomial
open LaurentPolynomial WPRationalCartier

namespace WPQuadraticRationalCartier

private def doubleIndex : ℤ →+ ℤ where
  toFun j := 2 * j
  map_zero' := by ring
  map_add' := by intros; ring

variable (p : ℕ) [Fact p.Prime]

/-- The entire Laurent substitution x=y², including negative powers. -/
noncomputable def squareSubstitute : (ZMod p)[T;T⁻¹] →+* (ZMod p)[T;T⁻¹] :=
  AddMonoidAlgebra.mapDomainRingHom (ZMod p) doubleIndex

theorem squareSubstitute_monomial (a : ZMod p) (j : ℤ) :
    squareSubstitute p (C a * T j) = C a * T (2 * j) := by
  simp [squareSubstitute, doubleIndex, ← LaurentPolynomial.single_eq_C_mul_T]

@[simp] theorem squareSubstitute_C (a : ZMod p) : squareSubstitute p (C a) = C a := by
  simpa using squareSubstitute_monomial p a 0

@[simp] theorem squareSubstitute_T (j : ℤ) : squareSubstitute p (T j) = T (2 * j) := by
  simpa using squareSubstitute_monomial p 1 j

theorem squareSubstitute_injective : Function.Injective (squareSubstitute p) := by
  change Function.Injective (AddMonoidAlgebra.mapDomain (R := ZMod p) doubleIndex)
  apply AddMonoidAlgebra.mapDomain_injective
  intro j k h
  change 2 * j = 2 * k at h
  omega

theorem quadraticPullback_eq (P : (ZMod p)[T;T⁻¹]) :
    WPFiniteCartier.quadraticPullback P = C 2 * T 1 * squareSubstitute p P := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    rw [WPFiniteCartier.quadraticPullback_add, map_add, mul_add, hP, hQ]
  | C_mul_T j a =>
    rw [WPFiniteCartier.quadraticPullback_monomial, squareSubstitute_monomial]
    rw [map_mul, T_add]
    ring

private theorem substituted_denominator_ne_zero (Q : (ZMod p)[T;T⁻¹])
    (hQ : evaluate p Q ≠ 0) : evaluate p (squareSubstitute p Q) ≠ 0 := by
  intro h
  have hQ0 : Q = 0 := squareSubstitute_injective p
    (evaluate_injective p (by simpa using h))
  exact hQ (by rw [hQ0, map_zero])

/-- Actual rational differential pullback, with its literal reduced numerator and denominator. -/
noncomputable def quadraticRational (f : RatFunc (ZMod p)) : RatFunc (ZMod p) :=
  evaluate p (C 2 * T 1 * squareSubstitute p (Polynomial.toLaurent f.num)) /
    evaluate p (squareSubstitute p (Polynomial.toLaurent f.denom))

/-- Rational differential pullback is independent of the complete Laurent fraction presentation. -/
theorem quadraticRational_fraction (P Q : (ZMod p)[T;T⁻¹])
    (hQ : evaluate p Q ≠ 0) :
    quadraticRational p (evaluate p P / evaluate p Q) =
      evaluate p (C 2 * T 1 * squareSubstitute p P) /
        evaluate p (squareSubstitute p Q) := by
  let f := evaluate p P / evaluate p Q
  let A : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent f.num
  let B : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent f.denom
  have hB : evaluate p B ≠ 0 := by
    rw [show B = Polynomial.toLaurent f.denom by rfl, evaluate_toLaurent]
    exact RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)
  have hrep : evaluate p A / evaluate p B = evaluate p P / evaluate p Q := by
    rw [show A = Polynomial.toLaurent f.num by rfl,
      show B = Polynomial.toLaurent f.denom by rfl, evaluate_toLaurent,
      evaluate_toLaurent, RatFunc.num_div_denom]
  have hcross : A * Q = P * B := by
    apply evaluate_injective p
    simp only [map_mul]
    exact (div_eq_div_iff hB hQ).mp hrep
  have hCe := congrArg (evaluate p) (congrArg (squareSubstitute p) hcross)
  simp only [map_mul] at hCe
  change evaluate p (C 2 * T 1 * squareSubstitute p A) /
      evaluate p (squareSubstitute p B) = _
  apply (div_eq_div_iff (substituted_denominator_ne_zero p B hB)
    (substituted_denominator_ne_zero p Q hQ)).mpr
  simp only [map_mul]
  linear_combination evaluate p (C 2) * evaluate p (T 1) * hCe

theorem quadraticRational_evaluate (P : (ZMod p)[T;T⁻¹]) :
    quadraticRational p (evaluate p P) = evaluate p (WPFiniteCartier.quadraticPullback P) := by
  have h := quadraticRational_fraction p P 1 (by simp)
  simpa only [map_one, div_one, quadraticPullback_eq] using h

/-- Cartier commutes with the complete rational x=y² differential pullback. -/
theorem rationalCartier_quadratic (hpodd : Odd p) (f : RatFunc (ZMod p)) :
    rationalCartier p (quadraticRational p f) =
      quadraticRational p (rationalCartier p f) := by
  let A : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent f.num
  let B : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent f.denom
  have hB : evaluate p B ≠ 0 := by
    rw [show B = Polynomial.toLaurent f.denom by rfl, evaluate_toLaurent]
    exact RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)
  have hf : f = evaluate p A / evaluate p B := by
    rw [show A = Polynomial.toLaurent f.num by rfl,
      show B = Polynomial.toLaurent f.denom by rfl, evaluate_toLaurent,
      evaluate_toLaurent, RatFunc.num_div_denom]
  rw [hf, quadraticRational_fraction p A B hB,
    rationalCartier_fraction p A B hB,
    quadraticRational_fraction p _ B hB,
    rationalCartier_fraction p _ (squareSubstitute p B)
      (substituted_denominator_ne_zero p B hB)]
  have hN : (C 2 * T 1 * squareSubstitute p A) *
      squareSubstitute p B ^ (p - 1) =
      WPFiniteCartier.quadraticPullback (A * B ^ (p - 1)) := by
    rw [quadraticPullback_eq, map_mul, map_pow]
    ring
  rw [hN, WPFiniteCartier.cartier_quadratic_pullback p (Fact.out : p.Prime).pos hpodd,
    quadraticPullback_eq]

end WPQuadraticRationalCartier
