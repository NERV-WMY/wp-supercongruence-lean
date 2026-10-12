import WPFieldAssembly.SourceClosureSigmaGclosed
import WPFieldAssembly.SourceClosureActualUVAttachment
import WPFieldAssembly.SourceClosureUVPhaseTrace

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource
  WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.SourceClosureUniversalLog
  WPFieldAssembly.SourceClosureUVDescent
  WPFieldAssembly.SourceClosureSigmaProperEndpoint
  WPFieldAssembly.SourceClosureSigmaCanonicalTransport
  WPFieldAssembly.SourceClosureSigmaProductCarry
  WPFieldAssembly.SourceClosureSigmaGclosed
  WPFieldAssembly.SourceClosureSigmaActualVS
  WPFieldAssembly.SourceClosureActualUVAttachment
  WPFieldAssembly.ActualKwFieldTrace
  WPFieldAssembly.SourceClosureUVPhaseTrace

namespace WPFieldAssembly.SourceClosureUVJointSource

/- The UW17e collection is made on the original whole U and the same
   integral VS. The canonical Tprod holes and the full u0 are retained. -/

theorem joint_log_coefficient (p : ℕ) [Fact p.Prime] :
    (LaurentPolynomial.C
        (WPFiniteABSourceTail.epsilon p *
          (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) / 15) -
      LaurentPolynomial.C (descendedZE p) +
      LaurentPolynomial.C
        ((WPFiniteWSource.W p).eval (1/4) + (WPFiniteWSource.W p).eval 4) :
        (ZMod p)[T;T⁻¹]) =
      LaurentPolynomial.C
        (WPFiniteABSourceTail.epsilon p *
          ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) -
            4 * descendedC p) / 15) := by
  rw [← _root_.map_sub, ← _root_.map_add]
  congr 1
  unfold descendedZE
  ring

/-- The whole actual carrier has the original UW17e source, with no free derivative premise. -/
theorem actualUV_joint_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualUV p hp =
      -endSym (fourUnitField p hp) (canSlots p (Tprod p)) -
      LaurentPolynomial.C (1/2 : ZMod p) * originalK0 p *
        ((originalHm p).toLaurent + invert (originalHm p).toLaurent) +
      LaurentPolynomial.C
        (WPFiniteABSourceTail.epsilon p *
          ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) -
            4 * descendedC p) / 15) * (originalJa p + originalJb p) -
      LaurentPolynomial.C (1/2 : ZMod p) * originalJ2log p -
      LaurentPolynomial.C (descendedU0 p) := by
  rw [actualUV, actualVSField, originalWholeVSI_Gclosed p hp,
    endSym_sub, endSym_sub, endSym_C_mul, originalJa_endSym p hp,
    Gclosed_endSym_joint p hp]
  unfold descendedU descendedUcan originalHsym
  linear_combination (originalJa p + originalJb p) * joint_log_coefficient p

theorem originalPhi_branch (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ)
      (originalPhi p) = -(25/4 : ZMod p) := by
  have h4 : (4 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 4
    (by omega) (by omega)
  simp only [originalPhi, _root_.map_sub, _root_.map_add,
    LaurentPolynomial.eval₂_C, RingHom.id_apply, LaurentPolynomial.eval₂_T_n,
    LaurentPolynomial.eval₂_T_neg_n, Units.val_neg, Units.val_one,
    ZMod.pow_card, inv_neg, inv_one]
  field_simp [h4]
  ring

/-- The original whole formula before canonical p-hole subtraction, without changing u0. -/
noncomputable def jointUncanonicalUV (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ZMod p)[T;T⁻¹] :=
  -endSym (fourUnitField p hp) (Tprod p) -
    LaurentPolynomial.C (1/2 : ZMod p) * originalK0 p *
      ((originalHm p).toLaurent + invert (originalHm p).toLaurent) +
    LaurentPolynomial.C
      (WPFiniteABSourceTail.epsilon p *
        ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) -
          4 * descendedC p) / 15) * (originalJa p + originalJb p) -
    LaurentPolynomial.C (1/2 : ZMod p) * originalJ2log p -
    LaurentPolynomial.C (descendedU0 p)

theorem actualUV_joint_p_hole (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualUV p hp = jointUncanonicalUV p hp +
      LaurentPolynomial.C ((Tprod p).coeff (p : ℤ)) * originalPhi p := by
  rw [actualUV_joint_source p hp, canSlots_endSym_original p hp]
  change _ = jointUncanonicalUV p hp +
    LaurentPolynomial.C ((Tprod p).coeff (p : ℤ)) *
      (T (p : ℤ)+T (-(p : ℤ))-LaurentPolynomial.C (17/4 : ZMod p))
  unfold jointUncanonicalUV
  ring

theorem originalWeightedFieldTrace_C_mul (p : ℕ) [Fact p.Prime]
    (c : ZMod p) (F : (ZMod p)[T;T⁻¹]) :
    originalWeightedFieldTrace p (LaurentPolynomial.C c * F) =
      c * originalWeightedFieldTrace p F := by
  unfold originalWeightedFieldTrace
  rw [show (3*(R : (ZMod p)[T;T⁻¹])^p*(3*T (-1)*(4-11*T 1)))*
      (LaurentPolynomial.C c*F) = LaurentPolynomial.C c*
        ((3*R^p*(3*T (-1)*(4-11*T 1)))*F) by ring]
  simpa only [LaurentPolynomial.smul_eq_C_mul, smul_eq_mul] using
    (LaurentPoleField.fieldTrace p (p+1)).map_smul c _

theorem actualUV_joint_weight_p_hole (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originalWeightedFieldTrace p (actualUV p hp) =
      originalWeightedFieldTrace p (jointUncanonicalUV p hp) +
        (99/4 : ZMod p) * (Tprod p).coeff (p : ℤ) := by
  rw [actualUV_joint_p_hole p hp]
  simp only [originalWeightedFieldTrace, mul_add, _root_.map_add]
  change _ + originalWeightedFieldTrace p
    (LaurentPolynomial.C ((Tprod p).coeff (p : ℤ))*originalPhi p) = _
  rw [originalWeightedFieldTrace_C_mul, originalPhi_weight p hp]
  ring

/-- UW18's uncanonical branch is evaluated on this same full carrier. -/
noncomputable def jointUncanonicalMu (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : ZMod p :=
  -(descendedU0 p : ZMod p) -
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ)
      (jointUncanonicalUV p hp) -
    (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2/2

theorem actualMu_joint_p_hole (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualMu p hp = jointUncanonicalMu p hp +
      (25/4 : ZMod p) * (Tprod p).coeff (p : ℤ) := by
  rw [actualMu, (actualUV_endpoints p hp).2, actualUV_joint_p_hole p hp]
  simp only [_root_.map_add, _root_.map_mul, LaurentPolynomial.eval₂_C,
    RingHom.id_apply, originalPhi_branch p hp, jointUncanonicalMu]
  ring

/-- The two actual p-hole contributions cancel only in the original coupled collection. -/
theorem actual_joint_p_hole_cancel (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (2/3 : ZMod p)*originalWeightedFieldTrace p (actualUV p hp) -
      (66/25 : ZMod p)*actualMu p hp =
    (2/3 : ZMod p)*originalWeightedFieldTrace p (jointUncanonicalUV p hp) -
      (66/25 : ZMod p)*jointUncanonicalMu p hp := by
  have h3 : (3 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have h4 : (4 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 4
    (by omega) (by omega)
  have h5 : (5 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have h25 : (25 : ZMod p) ≠ 0 := by
    rw [show (25 : ZMod p)=5*5 by ring]
    exact mul_ne_zero h5 h5
  rw [actualUV_joint_weight_p_hole p hp, actualMu_joint_p_hole p hp]
  field_simp [h3, h4, h25]
  ring

end WPFieldAssembly.SourceClosureUVJointSource
