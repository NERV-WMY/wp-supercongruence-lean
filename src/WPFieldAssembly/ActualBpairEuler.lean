import WPFieldAssembly.ActualBpairGreen
import WPFieldAssembly.ActualNormCrossAttachment

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource
  WPFieldAssembly.GreenLaurentOperators WPFiniteLaurentDifferential
  WPActualNativeCanonicalPart WPActualCanonicalFinitePart WPCartierPoleProjection
namespace WPFieldAssembly.NativeScalarRows
variable {K : Type*} [Field K]
theorem actual_GKQ_raw_endpoint (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    actualGKQ p = -2 * WPFiniteNC122.Ksrc p (WPFiniteNC122.h p)
      (WPFiniteNC122.T0 u) - WPFiniteNC122.a0 p u ^ 2 +
      WPFiniteNC122.h p ^ 2 := by
  rw [actual_GKQ_original_attachment p hp,
    WPFiniteNC122Residue.actual_NC122_residue p hp u hu]
  rfl

theorem actual_GKQ_literal_J_endpoint (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    actualGKQ p = 2 * WPFiniteNC122.Aeven p (WPFiniteNC122.T0 u) -
      4 * WPFiniteNC122.a0 p u ^ 2 / 3 +
      2 * (WPFiniteNC122.q p - WPFiniteNC122.h p) * WPFiniteNC122.a0 p u -
      2 * WPFiniteNC122.h p ^ 2 / 3 +
      2 * WPFiniteNC122.q p * WPFiniteNC122.h p - WPFiniteNC122.q p ^ 2 -
      2 * ((WPFiniteNC122.T0 u) ^ p *
        WPFiniteNC122.J_L p (WPFiniteNC122.T0 u)) / 3 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 6
    (Finset.mem_Ico.mpr (by omega))
  rw [actual_GKQ_raw_endpoint p hp u hu,
    WPFiniteNC122.Ksrc_quadratic p hp]
  have hL : WPFiniteNC122.L p (WPFiniteNC122.T0 u) =
      WPFiniteNC122.a0 p u + WPFiniteNC122.h p := by
    unfold WPFiniteNC122.a0
    ring
  rw [hL]
  field_simp [h2, h3, h6]
  ring
/-- The original T0 Frobenius factor gives NC130a's literal positive J origin term. -/
theorem actual_GKQ_literal_origin_J_endpoint (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    actualGKQ p=2*WPFiniteNC122.Aeven p (WPFiniteNC122.T0 u)-
      4*WPFiniteNC122.a0 p u^2/3+
      2*(WPFiniteNC122.q p-WPFiniteNC122.h p)*WPFiniteNC122.a0 p u-
      2*WPFiniteNC122.h p^2/3+2*WPFiniteNC122.q p*WPFiniteNC122.h p-
      WPFiniteNC122.q p^2+
      (22/15 : K)*u^p*WPFiniteNC122.J_L p (WPFiniteNC122.T0 u) := by
  have h11p : (11 : K)^p=11 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 11
  have h5p : (5 : K)^p=5 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 5
  have hphase : (WPFiniteNC122.T0 u)^p= -11*u^p/5 := by
    rw [WPFiniteNC122.T0,div_pow,mul_pow,
      (Fact.out : p.Prime).odd_of_ne_two (by omega) |>.neg_pow,h11p,h5p]
  rw [actual_GKQ_literal_J_endpoint p hp u hu,hphase]
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  field_simp [h3,h5,h15]
  ring

end WPFieldAssembly.NativeScalarRows

namespace WPFieldAssembly.ActualBpairContraction
open NativeScalarRows ActualLowEuler ResidualProjection

 theorem actual_fK_self (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ActualThreePhase.fK (K := ZMod p) p hp =
      (actualF p).comp (WPFiniteNC122Residue.Qrev : (ZMod p)[X]) := by
  rw [ActualThreePhase.fK, phi_self, Polynomial.map_id,
    NativeChiFieldSource.halfPullbackField_eq,
    WPActualNativeHasse.actual_full_native_field_cutoff p ((p-1)/2)
      (by omega) (by omega) (by omega), ← actualF_eq_native p hp,
    ← Qrev_eq_fieldV p]

 theorem actual_Hpull_euler (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent *
        D (ActualGreenResidue.Hpull p).toLaurent =
      (((actualF p).comp (WPFiniteNC122Residue.Qrev : (ZMod p)[X])).toLaurent - 1) *
        (33 - 12 * T 1) := by
  have h := (ActualGreenResidue.actual_two_Euler_sources (K := ZMod p) p hp).1
  rw [ActualGreenResidue.HpullK, phi_self, Polynomial.map_id,
    actual_fK_self p hp] at h
  exact h

 theorem reciprocalDensity_mul_zero (p : ℕ) [Fact p.Prime]
    (F G : (ZMod p)[X]) (hG : G.eval 0 = 0) :
    reciprocalDensity (F * G) =
      substituteOver F (originalQ : (ZMod p)[T;T⁻¹]) * reciprocalDensity G := by
  rw [reciprocalDensity_factor, mul_divX_right F G hG,
    reciprocalDensity_factor]
  simp only [substituteOver, Polynomial.eval₂_mul]
  ring

 theorem reciprocalDensity_cleared_zero (p : ℕ) [Fact p.Prime]
    (G : (ZMod p)[X]) (hG : G.eval 0 = 0) :
    (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent * reciprocalDensity G =
      substituteOver G (originalQ : (ZMod p)[T;T⁻¹]) * (33 - 12 * T 1) := by
  have hz : G.coeff 0 = 0 := by simpa only [coeff_zero_eq_eval_zero] using hG
  have hd : X * G.divX = G := by
    simpa only [hz, map_zero, add_zero] using X_mul_divX_add G
  have hs := congrArg
    (Polynomial.eval₂RingHom LaurentPolynomial.C
      (originalQ : (ZMod p)[T;T⁻¹])) hd
  have hs' : originalQ * substituteOver G.divX originalQ = substituteOver G originalQ := by
    simpa only [substituteOver, Polynomial.coe_eval₂RingHom, map_mul,
      Polynomial.eval₂_X] using hs
  rw [reciprocalDensity_factor]
  calc
    _ = substituteOver G.divX originalQ *
        ((WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent * Fnegative) := by ring
    _ = substituteOver G.divX originalQ * (originalQ * (33 - 12 * T 1)) := by
      rw [original_cubic_density_cleared]
    _ = _ := by rw [← hs']; ring
end WPFieldAssembly.ActualBpairContraction

namespace WPFieldAssembly.ActualBpairContraction
open NativeScalarRows ActualLowEuler ResidualProjection

theorem actual_I0_Euler_attachment (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (G : (ZMod p)[X]) (hG : G.eval 0 = 0) :
    Ij p 0 (actualF p * G) = (reciprocalDensity G).coeff (-1) -
      ((ActualGreenResidue.Hpull p).toLaurent *
        D (substituteOver G (originalQ : (ZMod p)[T;T⁻¹]))).coeff (-1) := by
  let f : (ZMod p)[T;T⁻¹] :=
    ((actualF p).comp (WPFiniteNC122Residue.Qrev : (ZMod p)[X])).toLaurent
  let H : (ZMod p)[T;T⁻¹] := (ActualGreenResidue.Hpull p).toLaurent
  let GQ : (ZMod p)[T;T⁻¹] := substituteOver G originalQ
  let A : (ZMod p)[T;T⁻¹] := (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent
  have hE : A * D H = (f - 1) * (33 - 12 * T 1) :=
    actual_Hpull_euler p hp
  have hC : A * reciprocalDensity G = GQ * (33 - 12 * T 1) :=
    reciprocalDensity_cleared_zero p G hG
  have hprod : f * reciprocalDensity G = GQ * D H + reciprocalDensity G := by
    apply mul_left_cancel₀ (WPFiniteZSource.Abar_nonzero (K := ZMod p) p hp)
    calc
      A * (f * reciprocalDensity G) = f * (A * reciprocalDensity G) := by ring
      _ = f * (GQ * (33 - 12 * T 1)) := by rw [hC]
      _ = GQ * ((f - 1) * (33 - 12 * T 1)) + GQ * (33 - 12 * T 1) := by ring
      _ = GQ * (A * D H) + A * reciprocalDensity G := by rw [hE, hC]
      _ = A * (GQ * D H + reciprocalDensity G) := by ring
  have hfrob : f = T (((p-1)/2 : ℕ) : ℤ) *
      substituteOver (actualF p) (originalQ : (ZMod p)[T;T⁻¹]) := by
    dsimp only [f]
    rw [← substituteOver_toLaurent]
    exact actualF_whole_reciprocity p hp
  have hprojection : Ij p 0 (actualF p * G) =
      (f * reciprocalDensity G).coeff (-1) := by
    have h : Ij p 0 (actualF p * G) =
        (T (((p-1)/2 : ℕ) : ℤ) * reciprocalDensity (actualF p * G)).coeff (-1) := by
      simpa only [Ij, Nat.zero_mul, Nat.add_zero, reciprocalDensity] using
        (polar_projection ((p-1)/2) (actualF p * G)).symm
    rw [reciprocalDensity_mul_zero p (actualF p) G hG,
      ← mul_assoc, ← hfrob] at h
    exact h
  have hz : (D (H * GQ)).coeff (-1) = 0 := by
    rw [D_coeff]
    norm_num
  rw [D_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hz
  have hibp : (GQ * D H).coeff (-1) = -(H * D GQ).coeff (-1) := by
    have hh : (GQ * D H).coeff (-1) + (H * D GQ).coeff (-1) = 0 := by
      simpa only [mul_comm] using hz
    exact eq_neg_of_add_eq_zero_left hh
  rw [hprojection, hprod, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hibp]
  change -(H * D GQ).coeff (-1) + (reciprocalDensity G).coeff (-1) = _
  ring

theorem actual_bracket_Euler_attachment (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    Ij p 0 (actualF p * WPFiniteNC122Residue.bracketQ p (WPFiniteNC122.h p)) =
      NativeScalarRows.actualGKQ (K := ZMod p) p -
      ((ActualGreenResidue.Hpull p).toLaurent *
        D (substituteOver (WPFiniteNC122Residue.bracketQ p (WPFiniteNC122.h p))
          (originalQ : (ZMod p)[T;T⁻¹]))).coeff (-1) := by
  rw [actual_I0_Euler_attachment p hp _
    (WPFiniteNC122Residue.bracketQ_zero_end p hp _)]
  rw [← actual_original_whole_cancellation p hp _
    (WPFiniteNC122Residue.bracketQ_zero_end p hp _)]
  rfl
end WPFieldAssembly.ActualBpairContraction

namespace WPFieldAssembly.ActualBpairContraction
open NativeQuadraticInverse NativeOriginalResidues ActualNormCrossAttachment
  ActualLowEuler ResidualProjection WPActualGaussBottom

noncomputable def actualKNative (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  quadraticInverse (WPFiniteKSource.KsrcP p (fieldHarmonic p (p/6)))

theorem actual_h_eq_NC122 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    fieldHarmonic p (p/6) = WPFiniteNC122.h (K := ZMod p) p := by
  rw [WPActualPartialHarmonic.actual_harmonic_sixth p (by omega)]
  unfold WPFiniteNC122.h WPFiniteNC122.q
  ring

theorem actual_bracket_native (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPFiniteNC122Residue.bracketQ p (WPFiniteNC122.h (K := ZMod p) p) =
      Polynomial.C (-2 / 3 : ZMod p) * actualKNative p -
      Polynomial.C (1 / 3 : ZMod p) * actualLogMinusH p ^ 2 +
      Polynomial.C (fieldHarmonic p (p/6) ^ 2 / 3) := by
  let A : (ZMod p)[X] := WPFiniteKSource.LPsrc p -
    Polynomial.C (fieldHarmonic p (p/6))
  have hA : A.comp (-X) = A := by
    simp only [A, sub_comp, WPFiniteNC122Residue.LPsrc_even, C_comp]
  have hA2 : quadraticInverse (A ^ 2) = actualLogMinusH p ^ 2 := by
    rw [pow_two, quadraticInverse_mul_even p hp A A hA hA,
      actual_log_minus_h_native p, ← pow_two]
  have hC : quadraticInverse (Polynomial.C (fieldHarmonic p (p/6) ^ 2 / 3)) =
      Polynomial.C (fieldHarmonic p (p/6) ^ 2 / 3) := by
    simp [quadraticInverse]
  rw [← actual_h_eq_NC122 p hp]
  change quadraticInverse (Polynomial.C (-2 / 3 : ZMod p) *
      WPFiniteKSource.KsrcP p (fieldHarmonic p (p/6)) -
      Polynomial.C (1 / 3 : ZMod p) * A ^ 2 +
      Polynomial.C (fieldHarmonic p (p/6) ^ 2 / 3)) = _
  rw [quadraticInverse_add_local, quadraticInverse_sub_local,
    ActualNC77Chart.quadraticInverse_C_mul, ActualNC77Chart.quadraticInverse_C_mul, hA2, hC]
  rfl

theorem actual_K_Xi_bracket_polynomial (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    Polynomial.C (-2 / 3 : ZMod p) * actualF p * actualKNative p -
      Polynomial.C (1 / 3 : ZMod p) * actualNormXi p hp =
    actualF p * WPFiniteNC122Residue.bracketQ p (WPFiniteNC122.h (K := ZMod p) p) +
      Polynomial.C (2 / 3 : ZMod p) *
        (actualF p * actualLogMinusH p ^ 2 -
          actualLogMinusH p * actualSigmaNative p hp) -
      Polynomial.C (fieldHarmonic p (p/6) ^ 2 / 3) * actualF p := by
  rw [actual_Xi_native_source p hp, actual_bracket_native p hp]
  simp only [div_eq_mul_inv, map_mul, map_neg, map_ofNat, map_one]
  ring

theorem actual_K_Xi_bracket_I0 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (-2 / 3 : ZMod p) * Ij p 0 (actualF p * actualKNative p) -
      Ij p 0 (actualNormXi p hp) / 3 =
      Ij p 0 (actualF p * WPFiniteNC122Residue.bracketQ p (WPFiniteNC122.h (K := ZMod p) p)) +
      (2 / 3 : ZMod p) * Ij p 0
        (actualF p * actualLogMinusH p ^ 2 -
          actualLogMinusH p * actualSigmaNative p hp) := by
  have h := congrArg (Ij p 0) (actual_K_Xi_bracket_polynomial p hp)
  have hz : Ij p 0 (actualF p) = 0 :=
    low_correction_both_projections_zero p hp _ (actualF_degree p hp) 0
  have hm : Polynomial.C (-2 / 3 : ZMod p) * actualF p * actualKNative p =
      Polynomial.C (-2 / 3 : ZMod p) * (actualF p * actualKNative p) := by ring
  rw [hm] at h
  simp only [Ij_sub_local, Ij_add, Ij_C_mul, hz, mul_zero, sub_zero] at h
  simp only [div_eq_mul_inv, Ij_sub_local] at h ⊢
  linear_combination h
end WPFieldAssembly.ActualBpairContraction

namespace WPFieldAssembly.ActualBpairContraction
open ActualResidualAssembly ActualNormCrossAttachment ActualLowEuler
  NativeScalarRows NativeOriginalResidues NativeQuadraticInverse ResidualProjection
  WPPIntegralReduction WPActualRankTwoLegendreField WPActualRankTwoProper
  WPActualRankTwoComparison WPActualGaussBottom ActualDeltaUNextSource
  ActualBalancedNodeAttachment NativeFullGreen ActualR0Node ActualNextHermite WPFiniteCarry

theorem actual_coupled_residual_Xi (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    2 * residueHom p (integralDeltaUDigit p hp) -
      (originalNorm p : ZMod p) - nativeBpair p hp =
    2 * residueHom p (balancedGreenDigitIntegral p hp) +
      (2 / 3 : ZMod p) * Ij p 0 (actualF p * actualSecondLogField p) -
      (2 * actualLowConstant p / 3) *
        QO p (X ^ p * actualLegendreJacobi p * properLegendreJacobi p) -
      (2 / 3 : ZMod p) * QO p (actualLegendreJacobi p ^ 2 *
        WPFiniteKSource.KsrcP p (fieldHarmonic p (p/6))) +
      (2 / 3 : ZMod p) * QO p (actualLegendreJacobi p *
        properLegendreJacobi p * WPFiniteKSource.OP p) -
      Ij p 0 (actualNormXi p hp) / 3 -
      (5 / 24 : ZMod p) * Ij p 1 (actualNormXi p hp) -
      103 * fieldHarmonic p (p/6) ^ 2 / 1000 - nativeBpair p hp := by
  have hr := actual_residual_balanced_source p hp
  have hs := actual_residual_polynomial_QO p hp
  have he := actual_low_euler_NC87 p hp
  change Ij p 0 (actualF p * actualSecondLogField p) =
    actualLowPair p + 3 * (actualSecondLogField p).eval (4/125) at he
  have hn := actual_original_norm_full p hp
  have hx := actual_original_norm_Xi p hp
  have h2 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h5 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  norm_num only [Nat.cast_ofNat] at h2 h3 h5
  have h24 : (24 : ZMod p) ≠ 0 := by
    rw [show (24 : ZMod p) = 2 ^ 3 * 3 by ring]
    exact mul_ne_zero (pow_ne_zero 3 h2) h3
  have h1000 : (1000 : ZMod p) ≠ 0 := by
    rw [show (1000 : ZMod p) = 2 ^ 3 * 5 ^ 3 by ring]
    exact mul_ne_zero (pow_ne_zero 3 h2) (pow_ne_zero 3 h5)
  linear_combination (norm := (field_simp [h3, h24, h1000]; ring))
    hr + (1 / 3 : ZMod p) * hs - (2 / 3 : ZMod p) * he + hn - hx

theorem actual_Ksrc_product_attachment (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    QO p (actualLegendreJacobi p ^ 2 *
      WPFiniteKSource.KsrcP p (fieldHarmonic p (p/6))) =
      Ij p 0 (actualF p * actualKNative p) := by
  unfold QO
  rw [quadraticInverse_mul_even p hp _ _ (actual_Y_square_even p hp)
    (WPFiniteNC122Residue.KsrcP_even p (fieldHarmonic p (p/6)))]
  rfl
end WPFieldAssembly.ActualBpairContraction

namespace WPFieldAssembly.ActualBpairContraction
open ActualResidualAssembly ActualNormCrossAttachment ActualLowEuler
  NativeScalarRows NativeOriginalResidues ResidualProjection
  WPPIntegralReduction WPActualRankTwoLegendreField WPActualRankTwoProper
  WPActualGaussBottom ActualDeltaUNextSource ActualBalancedNodeAttachment NativeFullGreen
  ActualR0Node ActualNextHermite WPFiniteCarry

theorem actual_coupled_GKQ_extraction (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    2 * residueHom p (integralDeltaUDigit p hp) -
      (originalNorm p : ZMod p) - nativeBpair p hp =
    2 * residueHom p (balancedGreenDigitIntegral p hp) +
      (2 / 3 : ZMod p) * Ij p 0 (actualF p * actualSecondLogField p) -
      (2 * actualLowConstant p / 3) *
        QO p (X ^ p * actualLegendreJacobi p * properLegendreJacobi p) +
      (2 / 3 : ZMod p) * QO p (actualLegendreJacobi p *
        properLegendreJacobi p * WPFiniteKSource.OP p) + actualGKQ (K := ZMod p) p -
      ((ActualGreenResidue.Hpull p).toLaurent *
        D (substituteOver (WPFiniteNC122Residue.bracketQ p (WPFiniteNC122.h (K := ZMod p) p))
          (originalQ : (ZMod p)[T;T⁻¹]))).coeff (-1) +
      (2 / 3 : ZMod p) * Ij p 0
        (actualF p * actualLogMinusH p ^ 2 -
          actualLogMinusH p * actualSigmaNative p hp) -
      (5 / 24 : ZMod p) * Ij p 1 (actualNormXi p hp) -
      103 * fieldHarmonic p (p/6) ^ 2 / 1000 - nativeBpair p hp := by
  rw [actual_coupled_residual_Xi p hp, actual_Ksrc_product_attachment p hp]
  have h := actual_K_Xi_bracket_I0 p hp
  rw [actual_bracket_Euler_attachment p hp] at h
  linear_combination h
end WPFieldAssembly.ActualBpairContraction
