import WPFieldAssembly.ActualBpairSigma
import WPFieldAssembly.ActualBpairOriginSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualNativeCanonicalPart
  WPActualCanonicalFinitePart WPActualChiSource
open WPFieldAssembly.ActualSimplePoleResidue WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/-- The whole actual Sigma pullback, with every Frobenius coefficient retained. -/
noncomputable def actualSigmaVK (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    K[T;T⁻¹] :=
  (((ActualNormCrossAttachment.actualSigmaNative p hp).comp
    (WPHasseIntegralTransport.fieldV p)).map (ActualThreePhase.φ p)).toLaurent

/-- The original cubic chart satisfies its full logarithmic differential identity. -/
theorem native_VK_logarithmic (p : ℕ) [Fact p.Prime] [CharP K p] :
    (WPFiniteZSource.Abar : K[X]) * (ActualGreenResidue.VK (K := K) p).derivative =
      ActualGreenResidue.VK p * (33 - 12 * X) := by
  have hc : (((1 / 125 : ℚ) : ZMod p)) = (1 / 125 : ZMod p) := by
    simpa only [one_div, Nat.cast_ofNat] using (Rat.cast_inv_nat (α := ZMod p) 125)
  have hv : ActualGreenResidue.VK (K := K) p =
      Polynomial.C (1 / 125 : K) * (4 * X - 1) ^ 2 * (4 - X) := by
    simp only [ActualGreenResidue.VK, WPHasseIntegralTransport.fieldV,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_ofNat, Polynomial.map_one, Polynomial.map_X, hc,
      map_div₀, map_one, map_ofNat]
  rw [hv]
  simp only [WPFiniteZSource.Abar, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_pow, Polynomial.derivative_sub, Polynomial.derivative_ofNat,
    Polynomial.derivative_X, Polynomial.derivative_one, zero_mul, zero_add, mul_one]
  norm_num only [Nat.cast_ofNat, map_ofNat]
  ring

/-- The actual H jet is attached by its derivative, without assigning a primitive value. -/
theorem actual_HJet_Sigma_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent * D (HJetPullK (K := K) p) =
      2 * actualSigmaVK (K := K) p hp * (33 - 12 * T 1) := by
  let f : ZMod p →+* K := ActualThreePhase.φ p
  let J := (nativeHJet p).map f
  let S := (ActualNormCrossAttachment.actualSigmaNative p hp).map f
  have hθ := congrArg (fun Q : (ZMod p)[X] => Q.map f)
    (nativeHJet_actual_source p hp)
  rw [actual_jet_twice_Sigma p hp] at hθ
  simp only [Polynomial.map_mul, Polynomial.map_X, Polynomial.map_ofNat,
    ← Polynomial.derivative_map] at hθ
  change X * J.derivative = 2 * S at hθ
  have ht := congrArg (fun Q : K[X] => Q.comp (ActualGreenResidue.VK p)) hθ
  simp only [Polynomial.mul_comp, Polynomial.X_comp, Polynomial.ofNat_comp] at ht
  have hv := native_VK_logarithmic (K := K) p
  have hs : (WPFiniteZSource.Abar : K[X]) *
      (J.comp (ActualGreenResidue.VK p)).derivative =
      2 * S.comp (ActualGreenResidue.VK p) * (33 - 12 * X) := by
    rw [Polynomial.derivative_comp]
    linear_combination (J.derivative.comp (ActualGreenResidue.VK p)) * hv +
      (33 - 12 * X) * ht
  have hj : HJetPullK (K := K) p = (J.comp (ActualGreenResidue.VK p)).toLaurent := by
    simp only [HJetPullK, pullbackPolynomial, coefficientMap_toLaurent,
      Polynomial.map_comp, J, f, ActualGreenResidue.VK]
  have hS : actualSigmaVK (K := K) p hp =
      (S.comp (ActualGreenResidue.VK p)).toLaurent := by
    simp only [actualSigmaVK, Polynomial.map_comp, S, f, ActualGreenResidue.VK]
  have hl := congrArg (fun Q : K[X] => Q.toLaurent) hs
  simp only [map_mul, map_sub, map_ofNat, Polynomial.toLaurent_X,
    ← D_toLaurent] at hl
  simpa only [hj, hS] using hl

/-- The complete original kernel turns the H-jet derivative into the actual Sigma residue. -/
theorem actual_HJet_kernel_coefficient (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (literalKB (K := K) p * D (HJetPullK (K := K) p)).coeff (-1) =
      2 * originPole (literalKB (K := K) p * actualSigmaVK p hp * (33 - 12 * T 1)) := by
  have hs := actual_HJet_Sigma_source (K := K) p hp
  have he : (WPFiniteZSource.Abar : K[X]).toLaurent *
      (literalKB (K := K) p * D (HJetPullK (K := K) p)) =
      LaurentPolynomial.C (2 : K) *
        (literalKB (K := K) p * actualSigmaVK p hp * (33 - 12 * T 1)) := by
    simp only [map_ofNat]
    linear_combination literalKB (K := K) p * hs
  rw [← originPole_cleared p hp, he, originPole_C_mul]

/-- Integration by parts removes the H jet only within the complete original residue. -/
theorem actual_HJet_kernel_origin (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    originPole (HJetPullK (K := K) p * kernelDerivativeNumerator p) =
      -2 * originPole (literalKB (K := K) p * actualSigmaVK p hp * (33 - 12 * T 1)) := by
  have h := literalKB_D_origin (K := K) p hp (HJetPullK p)
  rw [actual_HJet_kernel_coefficient p hp] at h
  linear_combination h

end WPFieldAssembly.ActualBpairContraction
