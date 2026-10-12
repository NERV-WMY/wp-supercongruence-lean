import WPFieldAssembly.NativeClosureNormOrigin

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource WPFiniteLaurentDifferential
open WPFieldAssembly.ActualSimplePoleResidue WPFieldAssembly.GreenLaurentOperators
  WPFieldAssembly.NativeScalarRows

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/-- The actual original GKQ bracket, transported as a whole Laurent source. -/
noncomputable def actualBracketQK (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  coefficientMap (ActualThreePhase.φ (K := K) p)
    (substituteOver
      (WPFiniteNC122Residue.bracketQ p (WPFiniteNC122.h (K := ZMod p) p))
      (originalQ : (ZMod p)[T;T⁻¹]))

/-- The bracket value is its original marked residue, with both endpoint cancellations proved. -/
theorem actual_GKQ_bracket_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    ActualThreePhase.φ (K := K) p (actualGKQ (K := ZMod p) p) =
      originPole (actualBracketQK (K := K) p * (33 - 12 * T 1)) := by
  let G := WPFiniteNC122Residue.bracketQ p (WPFiniteNC122.h (K := ZMod p) p)
  let g : ZMod p →+* K := ActualThreePhase.φ p
  have hG : G.coeff 0 = 0 := by
    simpa only [coeff_zero_eq_eval_zero, G] using
      (WPFiniteNC122Residue.bracketQ_zero_end (K := ZMod p) p hp
        (WPFiniteNC122.h p))
  have hs := reciprocalDensity_cleared_general G
  rw [hG] at hs
  simp only [map_zero, sub_zero] at hs
  rw [← actual_original_whole_cancellation p hp G
    (WPFiniteNC122Residue.bracketQ_zero_end p hp (WPFiniteNC122.h p))] at hs
  have hm := congrArg (coefficientMap g) hs
  have ha : coefficientMap g (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent =
      (WPFiniteZSource.Abar : K[X]).toLaurent := by
    simp only [coefficientMap_toLaurent, WPFiniteZSource.Abar, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat]
  simp only [map_mul, map_sub, map_ofNat, coefficientMap_T, ha] at hm
  change _ = originPole (coefficientMap g
    (substituteOver G (originalQ : (ZMod p)[T;T⁻¹])) * (33 - 12 * T 1))
  rw [← hm, originPole_cleared p hp, coefficientMap_coeff]
  rfl

/-- The Euler density is the derivative of this same bracket, with the actual H pullback. -/
theorem actual_EulerBracket_source (p : ℕ) [Fact p.Prime] [CharP K p] :
    coefficientMap (ActualThreePhase.φ (K := K) p) (actualEulerBracketDensity p) =
      (ActualGreenResidue.HpullK (K := K) p).toLaurent *
        D (actualBracketQK (K := K) p) := by
  rw [actualEulerBracketDensity, map_mul, D_coefficientMap, coefficientMap_toLaurent]
  rfl

/-- The native, complete norm and GKQ carriers enter one actual H adjoint. -/
noncomputable def actualUniversalV (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    K[T;T⁻¹] := actualRootUniversalV (K := K) p u + actualBracketQK p

/-- Removing only the bracket term from the retained original non-f source. -/
noncomputable def actualMarkedResidualDensity (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) (h4 : (4 : K) ≠ 0) : K[T;T⁻¹] :=
  actualMarkedNonfDensity (K := K) p u h4 +
    (WPFiniteZSource.Abar : K[X]).toLaurent *
      coefficientMap (ActualThreePhase.φ (K := K) p) (actualEulerBracketDensity p)

noncomputable def actualUniversalDensity (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) (h4 : (4 : K) ≠ 0) : K[T;T⁻¹] :=
  actualUniversalV (K := K) p u * (33 - 12 * T 1) -
    (WPFiniteZSource.Abar : K[X]).toLaurent *
      ((ActualGreenResidue.HpullK (K := K) p).toLaurent * D (actualUniversalV p u)) +
    actualMarkedResidualDensity p u h4

/-- The collected bracket retains its value and its derivative in the same residue. -/
theorem actualUniversalDensity_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) (h4 : (4 : K) ≠ 0) :
    actualUniversalDensity (K := K) p u h4 =
      actualMarkedEulerDensity (K := K) p u h4 +
        actualBracketQK p * (33 - 12 * T 1) := by
  unfold actualUniversalDensity actualUniversalV actualMarkedResidualDensity
    actualMarkedEulerDensity
  rw [map_add, actual_EulerBracket_source p]
  ring

/-- The same actual NC77 scalar now has one universal adjoint and all original residual sources. -/
theorem actualNC77Scalar_universal_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) (h4 : (4 : K) ≠ 0) :
    ActualThreePhase.φ (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) =
      ActualThreePhase.φ (K := K) p (actualRetainedTraceScalar p hp) +
        originPole (actualUniversalDensity (K := K) p u h4) := by
  rw [actualNC77Scalar_marked_Euler_origin p hp u hu h4, map_add,
    actual_GKQ_bracket_origin p hp, actualUniversalDensity_source p u h4, originPole_add]
  ring

/-- The complete Z52 norm carrier has the literal product derivative, with its P-D source intact. -/
theorem actual_Z52_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    D (actualZ52 (K := K) p u) =
      2 * ((actualAK p).toLaurent - invert (actualAK p).toLaurent) *
        (D (actualAK p).toLaurent - D (invert (actualAK p).toLaurent)) +
      6 * (D (invert (actualAK p).toLaurent) *
          (WPFiniteZSource.P p u - (WPFieldAssembly.ActualBpairContraction.Dstar p : K[X]).toLaurent) +
        invert (actualAK p).toLaurent *
          (D (WPFiniteZSource.P p u) - D (WPFieldAssembly.ActualBpairContraction.Dstar p : K[X]).toLaurent)) := by
  have h6 : D (6 : K[T;T⁻¹]) = 0 := by
    simpa only [map_ofNat] using D_C (6 : K)
  simp only [actualZ52, pow_two, map_add, map_sub, D_mul, h6, zero_mul, zero_add]
  ring

/-- Both Frobenius phases remain in the whole R52 derivative. -/
theorem actual_R52_derivative (p : ℕ) [Fact p.Prime] [CharP K p] :
    D (actualR52 (K := K) p) =
      -(4 * T (-(p : ℤ)) - 11) * D (invert (actualAK p).toLaurent) -
        (4 * T (p : ℤ) - 11) * D (actualAK p).toLaurent := by
  have hplus : D (T (p : ℤ) : K[T;T⁻¹]) = 0 := by
    have h := D_monomial (1 : K) (p : ℤ)
    simpa only [map_one, one_mul, Int.cast_natCast, CharP.cast_eq_zero,
      map_zero, zero_mul] using h
  have hminus : D (T (-(p : ℤ)) : K[T;T⁻¹]) = 0 := by
    have h := D_monomial (1 : K) (-(p : ℤ))
    simpa only [map_one, one_mul, Int.cast_neg, Int.cast_natCast,
      CharP.cast_eq_zero, neg_zero, map_zero, zero_mul] using h
  have h4 : D (4 : K[T;T⁻¹]) = 0 := by
    simpa only [map_ofNat] using D_C (4 : K)
  have h11 : D (11 : K[T;T⁻¹]) = 0 := by
    simpa only [map_ofNat] using D_C (11 : K)
  simp only [actualR52, map_sub, map_neg, D_mul, hplus, hminus, h4, h11,
    zero_mul, mul_zero, zero_add, sub_zero]
  ring

end WPFieldAssembly.ActualBpairContraction
