import WPFieldAssembly.SourceClosureUVJointSource
import WPFieldAssembly.SourceClosureUVEndpoint
import WPFieldAssembly.SourceClosureUVUnitEndpoints
import WPFiniteFieldLog

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.SourceClosureUniversalLog WPFieldAssembly.SourceClosureUVDescent
  WPFieldAssembly.SourceClosureUVEndpoint WPFieldAssembly.SourceClosureUVUnitEndpoints
  WPFieldAssembly.SourceClosureSigmaProperEndpoint WPFieldAssembly.SourceClosureSigmaGclosed
  WPFieldAssembly.SourceClosureSigmaKCarry WPFieldAssembly.ActualSigmaNormCarrySource
  WPFieldAssembly.ActualUW16PrimitiveSource WPFieldAssembly.SourceClosureUVJointSource

namespace WPFieldAssembly.SourceClosureUVJointEndpoint

/- These evaluations use the original K1, W1 and entire uncanonical UV.
   The full u0 cancels in its defining branch difference, after evaluation. -/

theorem originalK0_branch (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ)
      (originalK0 p)=25/(2*WPFiniteABSourceTail.epsilon p) := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p)≠0 := pow_ne_zero _
    (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega))
  simp only [originalK0, map_sub, map_add, map_mul,
    LaurentPolynomial.eval₂_C, RingHom.id_apply, LaurentPolynomial.eval₂_T_n,
    LaurentPolynomial.eval₂_T_neg_n, Units.val_neg, Units.val_one,
    ZMod.pow_card, inv_neg, inv_one]
  field_simp [h2,heps]; ring

theorem normEntropyField_endpoints (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)⁻¹
      (normEntropyField p)=0 ∧
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)
      (normEntropyField p)=0 := by
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4
    (by omega) (by omega)
  have hv : (fourUnitField p hp : ZMod p)=4 := rfl
  have h4p : (4 : ZMod p)^p=4 := ZMod.pow_card _
  have hell : WPFiniteField.ell p (1 : ZMod p)=0 :=
    WPFiniteInversion.ell_one_eq_zero p (by omega)
  have hmul : (4 : ZMod p)⁻¹*4=1 := inv_mul_cancel₀ h4
  have hmul' : (4 : ZMod p)*4⁻¹=1 := mul_inv_cancel₀ h4
  constructor <;>
    simp only [normEntropyField, map_add, map_mul, map_sub, _root_.map_ofNat,
      LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T_neg_n,
      RingHom.id_apply, LaurentPolynomial.eval₂_toLaurent, eval₂_id,
      eval_comp, eval_mul, eval_C, eval_X, Polynomial.eval_ofNat,
      WPFiniteAffineLog.LP_eval_eq,
      Units.val_inv_eq_inv_val, hv, inv_inv, inv_pow, h4p,
      one_div, hmul, hmul', hell, sub_self, mul_zero, zero_mul,
      add_zero]

theorem normEntropyField_branch (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ)
      (normEntropyField p)=-(5/2 : ZMod p)*WPFiniteField.ell p (-4) := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4
    (by omega) (by omega)
  have hinv := WPFiniteField.ell_inversion p (-4 : ZMod p) (neg_ne_zero.mpr h4)
  rw [ZMod.pow_card, show (-4 : ZMod p)⁻¹=-(1/4 : ZMod p) by
    simp only [inv_neg,one_div]] at hinv
  simp only [normEntropyField, map_add, map_mul, map_sub, _root_.map_ofNat,
    LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T_neg_n,
    RingHom.id_apply, LaurentPolynomial.eval₂_toLaurent, eval₂_id,
    eval_comp, eval_mul, eval_C, eval_X, Polynomial.eval_ofNat,
    WPFiniteAffineLog.LP_eval_eq,
    Units.val_neg, Units.val_one, ZMod.pow_card, inv_neg, inv_one,
    mul_neg, mul_one]
  rw [hinv]
  field_simp [h2,h4]
  ring

theorem originalK1_endpoints (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)⁻¹
      (originalK1Field p)=15*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)/
        WPFiniteABSourceTail.epsilon p ∧
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)
      (originalK1Field p)=15*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)/
        WPFiniteABSourceTail.epsilon p := by
  obtain ⟨hKa,hKb⟩ := originalK0_endpoints p hp
  obtain ⟨hQa,hQb⟩ := normEntropyField_endpoints p hp
  constructor <;>
    simp only [originalK1Field, map_add, map_mul, LaurentPolynomial.eval₂_C,
      RingHom.id_apply, originalK0Field_identification p hp, hKa, hKb,
      hQa, hQb, mul_zero, zero_add, add_zero, WPFiniteABSourceTail.epsilon]

theorem originalK1_branch (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ)
      (originalK1Field p)=0 := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p)≠0 := pow_ne_zero _
    (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega))
  have hepsPow : (5 : ZMod p)^((p-1)/2)=WPFiniteABSourceTail.epsilon p := rfl
  simp only [originalK1Field, map_add, map_mul, LaurentPolynomial.eval₂_C,
    RingHom.id_apply, originalK0Field_identification p hp, originalK0_branch p hp,
    normEntropyField_branch p hp, WPFiniteField.ell_neg_four_eq_fermat p hp]
  rw [hepsPow]
  field_simp [h2,heps]; ring

theorem originalE4Centered_branch (p : ℕ) [Fact p.Prime] :
    (originalE4CenteredField p).eval (-1)=
      -(WPFiniteLVSource.evenSquared p).eval (4/5 : ZMod p) := by
  have hzero : (WPFiniteLVSource.evenSquared p).eval (0 : ZMod p)=0 := by
    simp only [WPFiniteLVSource.evenSquared, eval_finsetSum, eval_mul,
      eval_C, eval_pow, eval_X]
    apply Finset.sum_eq_zero
    intro j hj
    have hj0 : j≠0 := by have := (Finset.mem_Ico.mp hj).1; omega
    simp only [zero_pow hj0,mul_zero]
  simp only [originalE4CenteredField, eval_sub, eval_comp, eval_mul,
    eval_ofNat, eval_C, WPFiniteWSource.squaredCoordinate, eval_add, eval_X,
    eval_one, neg_add_cancel, mul_zero, hzero, zero_sub]

theorem originalTprod_branch (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ)
      (Tprod p)=(5/3 : ZMod p)*
        (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        (WPFiniteLVSource.evenSquared p).eval (4/5) := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have h15 : (15 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 15
    (by omega) (by omega)
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p)≠0 := pow_ne_zero _
    (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega))
  have hepsPow : (5 : ZMod p)^((p-1)/2)=WPFiniteABSourceTail.epsilon p := rfl
  simp only [Tprod, map_add, map_mul, originalK1_branch p hp,
    originalK0Field_identification p hp, originalK0_branch p hp, zero_mul,
    zero_add, LaurentPolynomial.eval₂_toLaurent, eval₂_id, eval_C,
    Units.val_neg, Units.val_one, originalE4Centered_branch]
  rw [hepsPow]
  field_simp [h2,h3,h15,heps]; ring

theorem originalTprod_endpoint_sum (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)⁻¹ (Tprod p)+
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp) (Tprod p)=
        (15 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)/
          WPFiniteABSourceTail.epsilon p*
          ((WPFiniteWSource.W p).eval (1/4)+(WPFiniteWSource.W p).eval 4) := by
  obtain ⟨hKa,hKb⟩ := originalK0_endpoints p hp
  obtain ⟨hK1a,hK1b⟩ := originalK1_endpoints p hp
  have hv : (fourUnitField p hp : ZMod p)=4 := rfl
  simp only [Tprod, map_add, map_mul, originalK0Field_identification p hp,
    hKa, hKb, hK1a, hK1b, zero_mul, add_zero,
    LaurentPolynomial.eval₂_toLaurent, eval₂_id, Units.val_inv_eq_inv_val,
    hv, one_div]
  ring

theorem originalHm_branch_squared (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (originalHm p : (ZMod p)[X]).eval (-1)=
      -(WPFiniteABSourceTail.epsilon p/15 : ZMod p)*
        (WPFiniteLoop.D ((p-1)/2) (4/5) 0-WPFiniteLoop.D ((p-1)/2) (1/5) 0) := by
  simpa only [originalHm, add_neg_cancel, mul_zero, zero_div] using
    (unitPrimitive_branch (K:=ZMod p) p hp (-1))

/-- The original uncanonical branch is reduced to the same product endpoints,
    before the full finite alphabet is collected. -/
theorem jointUncanonicalMu_original_branch (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    jointUncanonicalMu p hp=
      (10/3 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        (WPFiniteLVSource.evenSquared p).eval (4/5)-
      15*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)/
        WPFiniteABSourceTail.epsilon p*
        ((WPFiniteWSource.W p).eval (1/4)+(WPFiniteWSource.W p).eval 4)+
      25/(2*WPFiniteABSourceTail.epsilon p)*(originalHm p).eval (-1)+
      ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-4*descendedC p)*
        WPFiniteField.ell p (-4)/3-WPFiniteField.R p (-4)/6-
      (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2/2 := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have h6 : (6 : ZMod p)≠0 := by
    rw [show (6 : ZMod p)=2*3 by ring]
    exact mul_ne_zero h2 h3
  have h15 : (15 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 15
    (by omega) (by omega)
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p)≠0 := pow_ne_zero _
    (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega))
  have hEnd : LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ)
      (endSym (fourUnitField p hp) (Tprod p))=
      2*((5/3 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        (WPFiniteLVSource.evenSquared p).eval (4/5))-
      15*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)/
        WPFiniteABSourceTail.epsilon p*
        ((WPFiniteWSource.W p).eval (1/4)+(WPFiniteWSource.W p).eval 4) := by
    simp only [endSym, map_sub, map_add, LaurentPolynomial.eval₂_C,
      RingHom.id_apply, WPFiniteJWeightedResidue.inversion_eval, inv_neg,
      inv_one, originalTprod_branch p hp]
    linear_combination -originalTprod_endpoint_sum p hp
  simp only [jointUncanonicalMu, jointUncanonicalUV, map_sub, map_add,
    map_neg, map_mul, LaurentPolynomial.eval₂_C, RingHom.id_apply,
    hEnd, originalK0_branch p hp, originalJab_branch p hp,
    originalJ2log_branch p hp, WPFiniteJWeightedResidue.inversion_eval,
    inv_neg, inv_one, LaurentPolynomial.eval₂_toLaurent, eval₂_id,
    Units.val_neg, Units.val_one]
  field_simp [h2,h3,h6,h15,heps]
  ring

/-- UW18e for the actual branch constant, in the prime-field squared alphabet. -/
theorem jointUncanonicalMu_finite_alphabet (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    jointUncanonicalMu p hp=
      (10/3 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        (WPFiniteLVSource.evenSquared p).eval (4/5)+
      (3/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2+
      (3/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)+
      4*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*descendedC p+
      ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-4*descendedC p)*
        WPFiniteField.ell p (-4)/3-
      (5/6 : ZMod p)*(WPFiniteLoop.D ((p-1)/2) (4/5) 0-
        WPFiniteLoop.D ((p-1)/2) (1/5) 0)-WPFiniteField.R p (-4)/6 := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have h6 : (6 : ZMod p)≠0 := by
    rw [show (6 : ZMod p)=2*3 by ring]
    exact mul_ne_zero h2 h3
  have h15 : (15 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 15
    (by omega) (by omega)
  have h30 : (30 : ZMod p)≠0 := by
    rw [show (30 : ZMod p)=2*15 by ring]
    exact mul_ne_zero h2 h15
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p)≠0 := pow_ne_zero _ h5
  have hW := WPFieldAssembly.SourceClosureWEndpoint.actual_W_endpoint_balance
    (K:=ZMod p) p hp
  rw [WPFieldAssembly.SourceClosureWEndpoint.squaredEntropyC_deltaE] at hW
  change (WPFiniteWSource.W p).eval (1/4)+(WPFiniteWSource.W p).eval 4+
    4*WPFiniteABSourceTail.epsilon p*descendedC p/15=
      -(WPFiniteABSourceTail.epsilon p : ZMod p)*
        (4*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)+
          3*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p))/30 at hW
  have hWs : (WPFiniteWSource.W p).eval (1/4)+(WPFiniteWSource.W p).eval 4=
      -(WPFiniteABSourceTail.epsilon p : ZMod p)*
        (4*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)+
          3*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p))/30-
      4*WPFiniteABSourceTail.epsilon p*descendedC p/15 := by
    linear_combination hW
  rw [jointUncanonicalMu_original_branch p hp, originalHm_branch_squared p hp, hWs]
  field_simp [h2,h3,h5,h6,h15,h30,heps]
  ring

end WPFieldAssembly.SourceClosureUVJointEndpoint
