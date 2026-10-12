import WPFieldAssembly.SourceClosureHalfPrimitiveTransport
import WPFiniteLVSource

open scoped BigOperators Polynomial
open Polynomial WPFieldAssembly.SourceClosureHalfPrimitive
  WPFieldAssembly.SourceClosureHalfPrimitiveTransport

namespace WPFieldAssembly.SourceClosureWEndpoint

variable {K : Type*} [Field K]

/-- The actual fifth entropy in the squared alphabet, retaining degree N. -/
noncomputable def squaredEntropyC (p : ℕ) : K :=
  (WPFiniteLVSource.evenSquared p).eval (4/5)-
    (WPFiniteLVSource.evenSquared p).eval (1/5)

theorem squaredEntropyC_deltaE (p : ℕ) :
    squaredEntropyC p=(WPFiniteWSource.deltaE p : K[X]).eval (1/5) := by
  simp only [squaredEntropyC,WPFiniteLVSource.evenSquared,WPFiniteWSource.deltaE,
    eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (4/5 : K)=4*(1/5) by ring,mul_pow]
  simp only [div_eq_mul_inv]
  ring

theorem squaredEntropyC_halfLog (p : ℕ) :
    squaredEntropyC p=(WPFiniteLoop.L ((p-1)/2) (4/5 : K)-
      WPFiniteLoop.L ((p-1)/2) (1/5 : K))/2 := by
  rw [squaredEntropyC_deltaE,deltaE_halfLog]
  simp only [eval_mul,eval_C,eval_sub,eval_comp,eval_ofNat,eval_X,halfLogP_eval]
  ring

/-- The same complete W endpoints determine the resonant scalar in either prime class. -/
theorem actual_W_endpoint_balance (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (WPFiniteWSource.W p : K[X]).eval (1/4)+(WPFiniteWSource.W p).eval 4+
      4*WPFiniteABSourceTail.epsilon p*squaredEntropyC p/15=
        -(WPFiniteABSourceTail.epsilon p : K)*
          (4*WPFiniteNC122.q p+3*(WPFiniteInversion.integerFermatQuotient p 3 : K))/30 := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h30 : (30 : K)≠0 := by
    rw [show (30 : K)=2*15 by ring]
    exact mul_ne_zero h2 h15
  rw [originalW_halfLog p hp,squaredEntropyC_halfLog]
  simp only [eval_mul,eval_C,eval_sub,eval_comp,eval_ofNat,eval_X,
    WPFiniteWSource.squaredCoordinate,eval_add,eval_one,halfLogP_eval]
  have ha : (5 : K)⁻¹*((1/4)+1)=1/4 := by field_simp [h4,h5]; ring
  have hb : (5 : K)⁻¹*(4+1)=1 := by field_simp [h5]; ring
  rw [ha,hb,mul_one,show (4 : K)*(1/4)=1 by field_simp [h4]]
  have hends := WPFiniteLoop.L_rational_ends (K:=K) p hp
  rw [hends.1,hends.2.1,hends.2.2]
  unfold WPFiniteNC122.q
  field_simp [h2,h4,h5,h15,h30]
  ring

end WPFieldAssembly.SourceClosureWEndpoint
