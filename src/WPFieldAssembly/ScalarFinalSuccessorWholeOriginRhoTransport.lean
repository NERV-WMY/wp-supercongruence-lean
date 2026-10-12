import WPFieldAssembly.NativeClosureUniversalSource
import WPFieldAssembly.NativeOriginalResidues

open scoped BigOperators Polynomial
open Polynomial

namespace WPFieldAssembly.NativeJointSuccessorRhoReduction

open ActualThreePhase

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

private theorem finite_q_map {L : Type*} [Field L] (f : K →+* L) (p : ℕ) :
    f (WPFiniteNC122.q (K := K) p) = WPFiniteNC122.q (K := L) p := by
  simp only [WPFiniteNC122.q, map_intCast]

/-- The original harmonic dictionary commutes with the complete field map. -/
theorem actual_original_h_transport (p : ℕ) [Fact p.Prime] [CharP K p] :
    φ (K := K) p (WPFiniteNC122.h (K := ZMod p) p) = WPFiniteNC122.h p := by
  simp only [WPFiniteNC122.h, finite_q_map, map_sub, map_mul, map_neg,
    map_div₀, map_ofNat, map_intCast]

private theorem finite_LP_map {L : Type*} [Field L] (f : K →+* L) (p : ℕ) :
    (WPFiniteAffineLog.LP (K := K) p).map f = WPFiniteAffineLog.LP (K := L) p := by
  simp only [WPFiniteAffineLog.LP, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, map_inv₀, map_natCast]

private theorem finite_RP_map {L : Type*} [Field L] (f : K →+* L) (p : ℕ) :
    (WPFiniteKSource.RP (K := K) p).map f = WPFiniteKSource.RP (K := L) p := by
  simp only [WPFiniteKSource.RP, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, map_inv₀, map_pow, map_natCast]

private theorem finite_KsrcP_map {L : Type*} [Field L]
    (f : K →+* L) (p : ℕ) (c : K) :
    (WPFiniteKSource.KsrcP p c).map f = WPFiniteKSource.KsrcP p (f c) := by
  simp only [WPFiniteKSource.KsrcP, WPFiniteKSource.S2P, WPFiniteKSource.LPsrc,
    WPFiniteKSource.EP, WPFiniteKSource.AP, WPFiniteKSource.BP,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_one, Polynomial.map_X,
    finite_LP_map, finite_RP_map, finite_q_map, map_inv₀, map_ofNat,
    map_div₀, map_mul, map_sub, _root_.map_pow]
  rw [Polynomial.map_pow, Polynomial.map_C, finite_q_map]

/-- Every coefficient of the original bracket, before its reciprocal cubic substitution, maps. -/
theorem actual_original_bracketQ_transport (p : ℕ) [Fact p.Prime] [CharP K p] :
    (WPFiniteNC122Residue.bracketQ p (WPFiniteNC122.h (K := ZMod p) p)).map
        (φ (K := K) p) =
      WPFiniteNC122Residue.bracketQ p (WPFiniteNC122.h (K := K) p) := by
  simp only [WPFiniteNC122Residue.bracketQ, Polynomial.map_comp,
    Polynomial.map_contract (by norm_num : (2 : ℕ) ≠ 0),
    WPFiniteNC122Residue.bracketT, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_one,
    Polynomial.map_X, finite_KsrcP_map, WPFiniteKSource.LPsrc, WPFiniteKSource.EP,
    Polynomial.map_comp, Polynomial.map_neg, finite_LP_map, finite_q_map,
    map_inv₀, map_neg, map_ofNat, map_one, map_div₀, map_pow, actual_original_h_transport]

private theorem canceled_density_map {L : Type*} [Field L]
    (f : K →+* L) (G : K[X]) :
    (WPFiniteNC122Residue.canceledDensity G).map f =
      WPFiniteNC122Residue.canceledDensity (G.map f) := by
  simp only [WPFiniteNC122Residue.canceledDensity, Polynomial.map_mul,
    Polynomial.map_comp, NativeOriginalResidues.divX_map_local,
    WPFiniteNC122Residue.Qrev, WPFiniteNC122Residue.Frev,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, map_div₀, map_ofNat]

/-- The mapped actual ZMod GKQ is the SAME generic-field whole reciprocal source value. -/
theorem actual_GKQ_coefficient_transport (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    φ (K := K) p (NativeScalarRows.actualGKQ (K := ZMod p) p) =
      NativeScalarRows.actualGKQ (K := K) p := by
  rw [NativeScalarRows.actual_GKQ_original_attachment p hp,
    NativeScalarRows.actual_GKQ_original_attachment p hp,
    ← Polynomial.coeff_map, canceled_density_map, actual_original_bracketQ_transport]

end WPFieldAssembly.NativeJointSuccessorRhoReduction
