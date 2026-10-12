import WPFieldAssembly.NativeClosureJetMarked
import WPFieldAssembly.NativeClosureReflectionPhase

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPFieldAssembly.ActualSimplePoleResidue WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/-- Both original endpoint values remain separate after the differential contraction. -/
noncomputable def actualMarkedEndpointSource (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) (h4 : (4 : K) ≠ 0) : K[T;T⁻¹] :=
  8 * (T 1 - 4) * LaurentPolynomial.C
      (ev (1 / 4) (one_div_ne_zero h4) (WPFiniteZSource.P p u)) +
    4 * (T 1 - LaurentPolynomial.C (1 / 4 : K)) * LaurentPolynomial.C
      (ev 4 h4 (WPFiniteZSource.P p u))

/-- The original f, CB and H adjoints, before any low metric or period value. -/
noncomputable def actualMarkedAdjointCore (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) : K[T;T⁻¹] :=
  literalKB (K := K) p *
    (((ActualThreePhase.fK (K := K) p hp).toLaurent *
          (LaurentPolynomial.C (1 / 3 : K) * (actualAK p).toLaurent -
            WPFiniteZSource.P p u) -
        2 * (1 - LaurentPolynomial.C (2 / 3 : K) * T (-(p : ℤ))) *
          (ActualThreePhase.CBK (K := K) p).toLaurent -
        (ActualGreenResidue.HpullK (K := K) p).toLaurent) * (33 - 12 * T 1) +
      (WPFiniteZSource.Abar : K[X]).toLaurent *
        ((ActualGreenResidue.HpullK (K := K) p).toLaurent +
          2 * LaurentPolynomial.C (ActualGreenResidue.hK (K := K) p)) *
        (LaurentPolynomial.C (1 / 2 : K) * T (-1))) -
    literalKB (K := K) p * actualMarkedEndpointSource p u h4

/-- Whole-kernel integration by parts and the actual Sigma source give the original adjoints. -/
theorem actualMarkedSigma_core_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) :
    originPole
      (ActualGreenResidue.greenPrimitive (K := K) p u * kernelDerivativeNumerator p +
        LaurentPolynomial.C (1 / 3 : K) *
          (literalKB p * actualSigmaVK p hp * (33 - 12 * T 1)) -
        literalKB p * actualMarkedEndSource p u h4) =
      originPole (actualMarkedAdjointCore (K := K) p hp u h4) := by
  let q : K[T;T⁻¹] := LaurentPolynomial.C (1 / 3 : K)
  let f := (ActualThreePhase.fK (K := K) p hp).toLaurent
  let A := (actualAK (K := K) p).toLaurent
  let B := (ActualThreePhase.CBK (K := K) p).toLaurent
  let H := (ActualGreenResidue.HpullK (K := K) p).toLaurent
  let L : K[T;T⁻¹] := 33 - 12 * T 1
  let W := (WPFiniteZSource.Abar : K[X]).toLaurent *
    (H + 2 * LaurentPolynomial.C (ActualGreenResidue.hK (K := K) p)) *
      (LaurentPolynomial.C (1 / 2 : K) * T (-1))
  let α : K[T;T⁻¹] := 1 - LaurentPolynomial.C (2 / 3 : K) * T (-(p : ℤ))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have hq : (3 : K[T;T⁻¹]) * q = 1 := by
    change LaurentPolynomial.C (3 : K) * LaurentPolynomial.C (1 / 3 : K) = 1
    rw [← map_mul, mul_one_div_cancel h3, map_one]
  have hphase : ActualChiEndpoints.zeta (K := K) p + q * (4 * T (p : ℤ) - 11) =
      2 * α := by
    rw [native_zeta_phase p hp]
    simp only [WPFiniteZSource.phase]
    have h23 : LaurentPolynomial.C (2 / 3 : K) = 2 * q := by
      dsimp only [q]
      simp only [div_eq_mul_inv, map_mul, map_ofNat, one_mul]
    dsimp only [α]
    rw [h23]
    linear_combination 2 * hq
  have hS : actualSigmaVK (K := K) p hp = f * A - (4 * T (p : ℤ) - 11) * B := by
    change (actualSigmaK (K := K) p hp).toLaurent = _
    rw [actual_SigmaK_source p hp]
    simp only [map_sub, map_mul, map_ofNat, Polynomial.toLaurent_X_pow]
    rfl
  have hχ : ActualGreenResidue.candidateChi (K := K) p hp u =
      f * WPFiniteZSource.P p u + ActualChiEndpoints.zeta p * B := rfl
  have hg := ActualGreenResidue.actual_candidate_green_source (K := K) p hp u
  change (WPFiniteZSource.Abar : K[X]).toLaurent *
      D (ActualGreenResidue.greenPrimitive (K := K) p u) =
    (ActualGreenResidue.candidateChi p hp u + H - WPFiniteZSource.P p u) * L - W at hg
  have hi := literalKB_D_origin (K := K) p hp
    (ActualGreenResidue.greenPrimitive p u)
  have he : (literalKB (K := K) p * D (ActualGreenResidue.greenPrimitive p u)).coeff (-1) =
      originPole (literalKB p *
        ((ActualGreenResidue.candidateChi p hp u + H - WPFiniteZSource.P p u) * L - W)) := by
    have hh : (WPFiniteZSource.Abar : K[X]).toLaurent *
        (literalKB p * D (ActualGreenResidue.greenPrimitive (K := K) p u)) =
        literalKB p *
          ((ActualGreenResidue.candidateChi p hp u + H - WPFiniteZSource.P p u) * L - W) := by
      linear_combination literalKB (K := K) p * hg
    rw [← originPole_cleared p hp, hh]
  rw [he] at hi
  have hcore :
      -(literalKB (K := K) p *
          ((ActualGreenResidue.candidateChi p hp u + H - WPFiniteZSource.P p u) * L - W)) +
        q * (literalKB p * actualSigmaVK p hp * L) -
        literalKB p * actualMarkedEndSource p u h4 = actualMarkedAdjointCore p hp u h4 := by
    rw [hχ, hS, actualMarkedEndSource, actualMarkedAdjointCore, actualMarkedEndpointSource]
    change _ = literalKB (K := K) p * ((f * (q * A - WPFiniteZSource.P p u) -
      2 * α * B - H) * L + W) - literalKB p *
      (8 * (T 1 - 4) * LaurentPolynomial.C
        (ev (1 / 4) (one_div_ne_zero h4) (WPFiniteZSource.P p u)) +
      4 * (T 1 - LaurentPolynomial.C (1 / 4 : K)) * LaurentPolynomial.C
        (ev 4 h4 (WPFiniteZSource.P p u)))
    linear_combination -(literalKB (K := K) p * B * L) * hphase
  rw [originPole_sub, originPole_add]
  have hin : originPole (ActualGreenResidue.greenPrimitive (K := K) p u *
      kernelDerivativeNumerator p) = -originPole (literalKB p *
        ((ActualGreenResidue.candidateChi p hp u + H - WPFiniteZSource.P p u) * L - W)) := by
    linear_combination hi
  have hn : originPole (-(literalKB (K := K) p *
      ((ActualGreenResidue.candidateChi p hp u + H - WPFiniteZSource.P p u) * L - W))) =
      -originPole (literalKB p *
        ((ActualGreenResidue.candidateChi p hp u + H - WPFiniteZSource.P p u) * L - W)) := by
    rw [show ∀ F : K[T;T⁻¹], -F = LaurentPolynomial.C (-1 : K) * F from
      fun F => by rw [map_neg, map_one, neg_one_mul], originPole_C_mul]
    ring
  rw [hin, ← hcore, originPole_sub, originPole_add, hn]

/-- The whole collected source retains the Euler bracket, original metric and second norm phase. -/
noncomputable def actualMarkedAdjointDensity (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) : K[T;T⁻¹] :=
  actualMarkedAdjointCore (K := K) p hp u h4 -
    (WPFiniteZSource.Abar : K[X]).toLaurent *
      WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
        (actualEulerBracketDensity p) -
    LaurentPolynomial.C (1 / 3 : K) *
      ((WPFiniteZSource.Abar : K[X]).toLaurent *
        WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
          (properMetricDensity p)) -
    LaurentPolynomial.C (5 / 24 : K) *
      ((WPFiniteZSource.Abar : K[X]).toLaurent *
        WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
          (actualNormI1Density p hp))

theorem actualMarkedSigma_to_Adjoint_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) :
    originPole (actualMarkedSigmaDensity (K := K) p hp u h4) =
      originPole (actualMarkedAdjointDensity (K := K) p hp u h4) := by
  have h := actualMarkedSigma_core_origin (K := K) p hp u h4
  simp only [originPole_sub] at h
  simp only [actualMarkedSigmaDensity, actualMarkedAdjointDensity, originPole_sub]
  rw [h]

/-- The original scalar reaches the actual f/CB/H adjoints with all high sources retained. -/
theorem actualNC77Scalar_marked_Adjoint_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) (h4 : (4 : K) ≠ 0) :
    ActualThreePhase.φ (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) =
      ActualThreePhase.φ (K := K) p
        (actualRetainedTraceScalar p hp + NativeScalarRows.actualGKQ (K := ZMod p) p) +
      originPole (actualMarkedAdjointDensity (K := K) p hp u h4) := by
  rw [actualNC77Scalar_marked_Sigma_origin p hp u hu h4,
    actualMarkedSigma_to_Adjoint_origin p hp u h4]

end WPFieldAssembly.ActualBpairContraction
