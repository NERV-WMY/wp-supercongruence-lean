import WPFieldAssembly.SourceClosureUVDescent

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.SourceClosureUniversalLog
  WPFieldAssembly.SourceClosureUVDescent

namespace WPFieldAssembly.SourceClosureUVUnitEndpoints

/- UW18 uses both original unit endpoints before combining the p-hole
   with the same branch normalization. No endpoint is reset here. -/

variable {K : Type*} [Field K]

theorem scaledLog_eval_unit (p : ℕ) [Fact p.Prime] [CharP K p] (c : K) (v : Kˣ) :
    LaurentPolynomial.eval₂ (RingHom.id K) v (scaledLog p c)=
      WPFiniteField.ell p (c*(v : K)) := by
  simp only [scaledLog,LaurentPolynomial.eval₂_toLaurent,Polynomial.eval₂_id,
    eval_comp,eval_mul,eval_C,eval_X,WPFiniteAffineLog.LP_eval_eq]

theorem scaledDilog_eval_unit (p : ℕ) [Fact p.Prime] [CharP K p] (c : K) (v : Kˣ) :
    LaurentPolynomial.eval₂ (RingHom.id K) v (scaledDilog p c)=
      WPFiniteField.R p (c*(v : K)) := by
  simp only [scaledDilog,LaurentPolynomial.eval₂_toLaurent,Polynomial.eval₂_id,
    eval_comp,eval_mul,eval_C,eval_X,WPFiniteKSource.RP_eval]

/-- All three original prefactors vanish at both reciprocal unit points. -/
theorem original_unit_prefactors (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (v : Kˣ) (hv : (v : K)=4) :
    (LaurentPolynomial.eval₂ (RingHom.id K) v (originalK0 p)=0 ∧
      LaurentPolynomial.eval₂ (RingHom.id K) v⁻¹ (originalK0 p)=0) ∧
    (LaurentPolynomial.eval₂ (RingHom.id K) v (originalJa p+originalJb p)=0 ∧
      LaurentPolynomial.eval₂ (RingHom.id K) v⁻¹ (originalJa p+originalJb p)=0) ∧
    (LaurentPolynomial.eval₂ (RingHom.id K) v (originalJ2log p)=0 ∧
      LaurentPolynomial.eval₂ (RingHom.id K) v⁻¹ (originalJ2log p)=0) := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have heps : (WPFiniteABSourceTail.epsilon p : K)≠0 := pow_ne_zero _ h5
  have h4p : (4 : K)^p=4 := WPFiniteField.natCast_pow_char p 4
  have hmul : (4 : K)⁻¹*4=1 := inv_mul_cancel₀ h4
  have hmul' : (4 : K)*4⁻¹=1 := mul_inv_cancel₀ h4
  have hell : WPFiniteField.ell p (1 : K)=0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.ell_one_eq_zero p (by omega))
    simpa only [←WPFiniteField.ell_castHom,map_one,map_zero] using he
  have hR : WPFiniteField.R p (1 : K)=0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.R_one_eq_zero p (by omega))
    simpa only [←WPFiniteField.R_castHom,map_one,map_zero] using he
  constructor
  · constructor <;>
      simp only [originalK0,map_sub,map_mul,map_add,LaurentPolynomial.eval₂_C,
        RingHom.id_apply,LaurentPolynomial.eval₂_T_n,LaurentPolynomial.eval₂_T_neg_n,
        Units.val_inv_eq_inv_val,hv,inv_pow,h4p]
    · field_simp [h2,h4,heps]
      ring
    · field_simp [h2,h4,heps]
      ring
  · constructor
    · constructor <;>
        simp only [originalJa,originalJb,map_add,map_mul,map_sub,
          LaurentPolynomial.eval₂_C,RingHom.id_apply,LaurentPolynomial.eval₂_T_neg_n,
          Units.val_inv_eq_inv_val,hv,inv_inv,inv_pow,h4p,scaledLog_eval_unit,
          one_div,hmul,hmul',hell]
      · ring
      · ring
    · constructor <;>
        simp only [originalJ2log,map_mul,map_sub,LaurentPolynomial.eval₂_C,
          RingHom.id_apply,LaurentPolynomial.eval₂_T_neg_n,
          Units.val_inv_eq_inv_val,hv,inv_inv,inv_pow,h4p,scaledDilog_eval_unit,
          one_div,hmul,hmul',hR]
      · ring
      · ring

/-- The specified original Ucan has both original unit endpoint values. -/
theorem originalUcan_endpoints (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (v : Kˣ) (hv : (v : K)=4) :
    LaurentPolynomial.eval₂ (RingHom.id K) v (originalUcan p u)=0 ∧
      LaurentPolynomial.eval₂ (RingHom.id K) v⁻¹ (originalUcan p u)=0 := by
  obtain ⟨hK,hJ,hR⟩ := original_unit_prefactors p hp v hv
  constructor
  · simp only [originalUcan,map_sub,map_mul,LaurentPolynomial.eval₂_C,
      RingHom.id_apply,hK.1,hJ.1,hR.1,mul_zero,zero_mul,sub_self]
  · simp only [originalUcan,map_sub,map_mul,LaurentPolynomial.eval₂_C,
      RingHom.id_apply,hK.2,hJ.2,hR.2,mul_zero,zero_mul,sub_self]

/-- Descent preserves these same endpoint values without a square-root premise. -/
theorem descendedUcan_endpoints (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (v : Kˣ) (hv : (v : K)=4) :
    LaurentPolynomial.eval₂ (RingHom.id K) v (descendedUcan p)=0 ∧
      LaurentPolynomial.eval₂ (RingHom.id K) v⁻¹ (descendedUcan p)=0 := by
  obtain ⟨hK,hJ,hR⟩ := original_unit_prefactors p hp v hv
  constructor
  · simp only [descendedUcan,map_sub,map_mul,LaurentPolynomial.eval₂_C,
      RingHom.id_apply,hK.1,hJ.1,hR.1,mul_zero,zero_mul,sub_self]
  · simp only [descendedUcan,map_sub,map_mul,LaurentPolynomial.eval₂_C,
      RingHom.id_apply,hK.2,hJ.2,hR.2,mul_zero,zero_mul,sub_self]

end WPFieldAssembly.SourceClosureUVUnitEndpoints
