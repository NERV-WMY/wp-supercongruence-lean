import WPFieldAssembly.SourceClosureWEndpoint
import WPFieldAssembly.SourceClosureUVDescent

open scoped Polynomial
open Polynomial WPFieldAssembly.SourceClosureHalfPrimitive
  WPFieldAssembly.SourceClosureHalfPrimitiveTransport
  WPFieldAssembly.SourceClosureWEndpoint WPFieldAssembly.SourceClosureUVDescent

namespace WPFieldAssembly.BalancedVbalSuccessorPSquareEnds

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

/- STATEMENT_FIDELITY: the original W is evaluated through its complete
   half-log polynomial and the original squared fifth entropy. This is
   the W-end component of SourceClosureUVFiniteEnds, isolated from the
   unrelated whole UV and sigma collectors so the actual P-square proof
   can consume its genuine source before those collectors are checked.
   Both prime classes and both fifth roots retain the same descendedC. -/

theorem actual_Psquare_W_ends (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (WPFiniteWSource.W p : K[X]).eval (1/4)=
      (WPFiniteABSourceTail.epsilon p/15 : K)*
        (-4*(WPFiniteInversion.integerFermatQuotient p 2 : K)+
          (3/2 : K)*(WPFiniteInversion.integerFermatQuotient p 3 : K)-2*descendedC p) ∧
    (WPFiniteWSource.W p : K[X]).eval 4=
      (WPFiniteABSourceTail.epsilon p/15 : K)*
        (2*(WPFiniteInversion.integerFermatQuotient p 2 : K)-
          3*(WPFiniteInversion.integerFermatQuotient p 3 : K)-2*descendedC p) := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hC : WPFiniteLoop.L ((p-1)/2) (4/5 : K)-
      WPFiniteLoop.L ((p-1)/2) (1/5 : K)=2*descendedC p := by
    rw [descendedC,←squaredEntropyC_deltaE,squaredEntropyC_halfLog]
    field_simp [h2]
  have ha : (5 : K)⁻¹*((1/4)+1)=1/4 := by field_simp [h4,h5]; ring
  have hb : (5 : K)⁻¹*(4+1)=1 := by field_simp [h5]; ring
  have h4a : (4 : K)*(1/4)=1 := by field_simp [h4]
  obtain ⟨hL1,hL4,hLa⟩ := WPFiniteLoop.L_rational_ends (K:=K) p hp
  simp only [originalW_halfLog p hp,eval_mul,eval_C,eval_sub,eval_comp,eval_ofNat,
    WPFiniteWSource.squaredCoordinate,eval_add,eval_X,eval_one,halfLogP_eval,
    ha,hb,h4a,mul_one,hL1,hL4,hLa]
  constructor <;>
    linear_combination (norm := (field_simp [h2]; ring))
      -(WPFiniteABSourceTail.epsilon p/15)*hC

end WPFieldAssembly.BalancedVbalSuccessorPSquareEnds
