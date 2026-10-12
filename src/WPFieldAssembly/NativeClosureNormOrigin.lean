import WPFieldAssembly.NativeClosureMarkedAdjoint
import WPFieldAssembly.NativeClosureEulerAdjoint

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource
open WPFieldAssembly.ActualSimplePoleResidue WPFieldAssembly.GreenLaurentOperators
  WPFieldAssembly.ResidualProjection WPFieldAssembly.NativeScalarRows
  WPFieldAssembly.ActualNormCrossAttachment

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]

/-- The original reciprocal density retains the true origin coefficient before any projection. -/
theorem reciprocalDensity_cleared_general (G : K[X]) :
    (WPFiniteZSource.Abar : K[X]).toLaurent * reciprocalDensity G =
      (substituteOver G (originalQ : K[T;T⁻¹]) - LaurentPolynomial.C (G.coeff 0)) *
        (33 - 12 * T 1) := by
  have hd : X * G.divX = G - Polynomial.C (G.coeff 0) := by
    linear_combination X_mul_divX_add G
  have hs := congrArg
    (Polynomial.eval₂RingHom LaurentPolynomial.C (originalQ : K[T;T⁻¹])) hd
  have hs' : originalQ * substituteOver G.divX originalQ =
      substituteOver G originalQ - LaurentPolynomial.C (G.coeff 0) := by
    simpa only [substituteOver, Polynomial.coe_eval₂RingHom, map_mul, map_sub,
      Polynomial.eval₂_X, Polynomial.eval₂_C] using hs
  rw [reciprocalDensity_factor]
  calc
    _ = substituteOver G.divX originalQ *
        ((WPFiniteZSource.Abar : K[X]).toLaurent * Fnegative) := by ring
    _ = substituteOver G.divX originalQ * (originalQ * (33 - 12 * T 1)) := by
      rw [original_cubic_density_cleared]
    _ = _ := by rw [← hs']; ring

/-- Complete coefficient transport identifies the original reciprocal actual Xi. -/
theorem actual_Xi_reciprocal_transport (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    coefficientMap (ActualThreePhase.φ (K := K) p)
      (substituteOver (actualNormXi p hp) (originalQ : (ZMod p)[T;T⁻¹])) =
      invert (actualXiK (K := K) p hp).toLaurent := by
  rw [originalQ, ← substituteOver_invert, substituteOver_toLaurent,
    ActualLowEuler.Qrev_eq_fieldV p, coefficientMap_invert, coefficientMap_toLaurent]
  rfl

/-- The mapped I1 source retains the entire N+p carrier and its actual constant. -/
theorem actual_norm_I1_cleared (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent *
        coefficientMap (ActualThreePhase.φ (K := K) p) (actualNormI1Density p hp) =
      T ((((p - 1) / 2 + p : ℕ) : ℤ)) *
        (invert (actualXiK (K := K) p hp).toLaurent -
          LaurentPolynomial.C
            (ActualThreePhase.φ (K := K) p ((actualNormXi p hp).coeff 0))) *
        (33 - 12 * T 1) := by
  let g : ZMod p →+* K := ActualThreePhase.φ p
  have ha : coefficientMap g (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent =
      (WPFiniteZSource.Abar : K[X]).toLaurent := by
    simp only [coefficientMap_toLaurent, WPFiniteZSource.Abar, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat]
  have h := congrArg (coefficientMap g)
    (reciprocalDensity_cleared_general (actualNormXi p hp))
  simp only [map_mul, map_sub, map_ofNat, coefficientMap_T, coefficientMap_C, ha] at h
  dsimp only [g] at h
  rw [actual_Xi_reciprocal_transport p hp] at h
  rw [actualNormI1Density, map_mul, coefficientMap_T]
  linear_combination T ((((p - 1) / 2 + p : ℕ) : ℤ)) * h

/-- Only a proved positive polynomial origin residue is removed; both signed Xi halves remain. -/
theorem actual_I1_Xi_Delta_origin (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    ActualThreePhase.φ (K := K) p (Ij p 1 (actualNormXi p hp)) =
      -originPole (T (p : ℤ) *
        ((actualXiK (K := K) p hp).toLaurent -
          T (((p - 1) / 2 : ℕ) : ℤ) * invert (actualXiK p hp).toLaurent) *
        (33 - 12 * T 1)) := by
  let n := (p - 1) / 2
  let F := (actualXiK (K := K) p hp).toLaurent
  let c := ActualThreePhase.φ (K := K) p ((actualNormXi p hp).coeff 0)
  let L : K[T;T⁻¹] := 33 - 12 * T 1
  have hn : (T (((n + p : ℕ) : ℤ)) : K[T;T⁻¹]) = T (p : ℤ) * T (n : ℤ) := by
    rw [← T_add]
    congr 1
    push_cast
    omega
  have hF : originPole (T (p : ℤ) * F * L) = 0 := by
    have h := originPole_polynomial ((X ^ p : K[X]) * actualXiK p hp * (33 - 12 * X))
    simpa only [map_mul, map_sub, map_ofNat, Polynomial.toLaurent_X,
      Polynomial.toLaurent_X_pow, F, L] using h
  have hc : originPole (T (((n + p : ℕ) : ℤ)) * LaurentPolynomial.C c * L) = 0 := by
    have h := originPole_polynomial ((X ^ (n + p) : K[X]) * Polynomial.C c * (33 - 12 * X))
    simpa only [map_mul, map_sub, map_ofNat, Polynomial.toLaurent_X,
      Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C, L] using h
  rw [actual_I1_Xi_origin p hp, ← coefficientMap_coeff,
    ← originPole_cleared p hp, actual_norm_I1_cleared p hp]
  change originPole (T (((n + p : ℕ) : ℤ)) * (invert F - LaurentPolynomial.C c) * L) = _
  have he : T (((n + p : ℕ) : ℤ)) * (invert F - LaurentPolynomial.C c) * L =
      T (p : ℤ) * F * L - T (p : ℤ) * (F - T (n : ℤ) * invert F) * L -
        T (((n + p : ℕ) : ℤ)) * LaurentPolynomial.C c * L := by
    rw [hn]
    ring
  rw [he, originPole_sub, originPole_sub, hF, hc]
  ring

/-- The same original I1 norm supplies the whole Z52/R52 block in both prime classes. -/
theorem actual_I1_Xi_NC123_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    ActualThreePhase.φ (K := K) p (Ij p 1 (actualNormXi p hp)) =
      -originPole (T (p : ℤ) *
        ((ActualThreePhase.fK (K := K) p hp).toLaurent * actualZ52 p u +
          2 * (ActualThreePhase.CBK (K := K) p).toLaurent * actualR52 p) *
        (33 - 12 * T 1)) := by
  rw [actual_I1_Xi_Delta_origin p hp, actual_DeltaXi p hp u hu]

/-- The same norm source joins the actual f/CB adjoints before the quadratic contraction. -/
noncomputable def actualMarkedNC123Density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) : K[T;T⁻¹] :=
  actualMarkedAdjointCore (K := K) p hp u h4 -
    (WPFiniteZSource.Abar : K[X]).toLaurent *
      coefficientMap (ActualThreePhase.φ (K := K) p) (actualEulerBracketDensity p) -
    LaurentPolynomial.C (1 / 3 : K) *
      ((WPFiniteZSource.Abar : K[X]).toLaurent *
        coefficientMap (ActualThreePhase.φ (K := K) p) (properMetricDensity p)) +
    LaurentPolynomial.C (5 / 24 : K) *
      (T (p : ℤ) *
        ((ActualThreePhase.fK (K := K) p hp).toLaurent * actualZ52 p u +
          2 * (ActualThreePhase.CBK (K := K) p).toLaurent * actualR52 p) *
        (33 - 12 * T 1))

theorem actualMarkedAdjoint_to_NC123_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) (h4 : (4 : K) ≠ 0) :
    originPole (actualMarkedAdjointDensity (K := K) p hp u h4) =
      originPole (actualMarkedNC123Density (K := K) p hp u h4) := by
  have h := actual_I1_Xi_NC123_origin (K := K) p hp u hu
  rw [actual_I1_Xi_origin p hp, ← coefficientMap_coeff, ← originPole_cleared p hp] at h
  simp only [actualMarkedAdjointDensity, actualMarkedNC123Density, originPole_sub,
    originPole_add, originPole_C_mul, h]
  ring

/-- NC123's complete norm contribution still belongs to the same original actual scalar. -/
theorem actualNC77Scalar_marked_NC123_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) (h4 : (4 : K) ≠ 0) :
    ActualThreePhase.φ (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) =
      ActualThreePhase.φ (K := K) p
        (actualRetainedTraceScalar p hp + actualGKQ (K := ZMod p) p) +
      originPole (actualMarkedNC123Density (K := K) p hp u h4) := by
  rw [actualNC77Scalar_marked_Adjoint_origin p hp u hu h4,
    actualMarkedAdjoint_to_NC123_origin p hp u hu h4]

/-- The actual native and norm f terms are combined before the whole Euler adjoint. -/
noncomputable def actualRootUniversalV (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    K[T;T⁻¹] :=
  literalKB (K := K) p *
      (LaurentPolynomial.C (1 / 3 : K) * (actualAK p).toLaurent - WPFiniteZSource.P p u) +
    LaurentPolynomial.C (5 / 24 : K) * T (p : ℤ) * actualZ52 p u

noncomputable def actualMarkedNonfDensity (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) (h4 : (4 : K) ≠ 0) : K[T;T⁻¹] :=
  literalKB (K := K) p *
    ((-2 * (1 - LaurentPolynomial.C (2 / 3 : K) * T (-(p : ℤ))) *
          (ActualThreePhase.CBK (K := K) p).toLaurent -
        (ActualGreenResidue.HpullK (K := K) p).toLaurent) * (33 - 12 * T 1) +
      (WPFiniteZSource.Abar : K[X]).toLaurent *
        ((ActualGreenResidue.HpullK (K := K) p).toLaurent +
          2 * LaurentPolynomial.C (ActualGreenResidue.hK (K := K) p)) *
        (LaurentPolynomial.C (1 / 2 : K) * T (-1))) -
    literalKB (K := K) p * actualMarkedEndpointSource p u h4 -
    (WPFiniteZSource.Abar : K[X]).toLaurent *
      coefficientMap (ActualThreePhase.φ (K := K) p) (actualEulerBracketDensity p) -
    LaurentPolynomial.C (1 / 3 : K) *
      ((WPFiniteZSource.Abar : K[X]).toLaurent *
        coefficientMap (ActualThreePhase.φ (K := K) p) (properMetricDensity p)) +
    LaurentPolynomial.C (5 / 12 : K) * T (p : ℤ) *
      (ActualThreePhase.CBK (K := K) p).toLaurent * actualR52 p * (33 - 12 * T 1)

theorem actualMarkedNC123_f_split (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) :
    actualMarkedNC123Density (K := K) p hp u h4 =
      (ActualThreePhase.fK (K := K) p hp).toLaurent * actualRootUniversalV p u *
        (33 - 12 * T 1) + actualMarkedNonfDensity p u h4 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h12 : (12 : K) ≠ 0 := by
    rw [show (12 : K) = 2 ^ 2 * 3 by ring]
    exact mul_ne_zero (pow_ne_zero 2 h2) h3
  have h24 : (24 : K) ≠ 0 := by
    convert mul_ne_zero h2 h12 using 1
    norm_num
  have hc : (5 / 24 : K) * 2 = 5 / 12 := by
    field_simp [h12, h24]
    ring
  have hL := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc
  simp only [map_mul, map_ofNat] at hL
  unfold actualMarkedNC123Density actualMarkedAdjointCore actualRootUniversalV
    actualMarkedNonfDensity
  linear_combination (T (p : ℤ) * (ActualThreePhase.CBK (K := K) p).toLaurent *
    actualR52 p * (33 - 12 * T 1)) * hL

/-- The complete H adjoint retains both endpoints and the original high proper metric. -/
noncomputable def actualMarkedEulerDensity (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) (h4 : (4 : K) ≠ 0) : K[T;T⁻¹] :=
  actualRootUniversalV (K := K) p u * (33 - 12 * T 1) -
    (WPFiniteZSource.Abar : K[X]).toLaurent *
      ((ActualGreenResidue.HpullK (K := K) p).toLaurent *
        WPFiniteLaurentDifferential.D (actualRootUniversalV p u)) +
    actualMarkedNonfDensity p u h4

theorem actualMarkedNC123_to_Euler_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) :
    originPole (actualMarkedNC123Density (K := K) p hp u h4) =
      originPole (actualMarkedEulerDensity (K := K) p u h4) := by
  rw [actualMarkedNC123_f_split p hp u h4, originPole_add,
    actual_f_green_marked_adjoint p hp, actualMarkedEulerDensity, originPole_add]

theorem actualNC77Scalar_marked_Euler_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) (h4 : (4 : K) ≠ 0) :
    ActualThreePhase.φ (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) =
      ActualThreePhase.φ (K := K) p
        (actualRetainedTraceScalar p hp + actualGKQ (K := ZMod p) p) +
      originPole (actualMarkedEulerDensity (K := K) p u h4) := by
  rw [actualNC77Scalar_marked_NC123_origin p hp u hu h4,
    actualMarkedNC123_to_Euler_origin p hp u h4]

end WPFieldAssembly.ActualBpairContraction
