import WPFieldAssembly.SourceClosureHalfPrimitiveTransport
import WPFieldAssembly.ActualUVSourceIdentification
import WPFieldAssembly.ActualKwRationalRowAttachment

open scoped Polynomial
open Polynomial WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.SourceClosureHalfPrimitiveTransport
  WPFieldAssembly.ActualKwFiniteHBridge WPFieldAssembly.ActualKwOrderedEndpoints
  WPFieldAssembly.ActualKwRationalRowAttachment

namespace WPFieldAssembly.SourceClosureUVOrderedH

variable {K : Type*} [Field K]

/- The ordered UW18 H combination is reused from the existing whole
   moving-H proof. Its c=11/4 term cancels between those two exact rows. -/

theorem original_unitPrimitive_movingH (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (c y : K) :
    (WPFiniteProductTail.unitPrimitiveP p (WPFiniteWSource.W p) c).eval y =
      (2*WPFiniteABSourceTail.epsilon p/15 : K)*movingH p c y := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  rw [original_unitPrimitive_eval_full p hp]
  unfold movingH
  have h1 (v : K) : (1+v)/5=(1/5 : K)*(1+v) := by ring
  simp only [h1]
  field_simp [h2]
  ring

theorem whole_movingH_ordered (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    -6*movingH p (0 : K) (1/4)+3*movingH p 0 4-
      (22/5 : K)*movingH p (1/4) (1/4)-(7/5 : K)*movingH p (1/4) 4+
      (4/5 : K)*movingH p 4 (1/4)-(11/5 : K)*movingH p 4 4 =
      (3/2 : K)*originalT5 p u+(7/10 : K)*originalG p (1/5)-rationalOrderedRows p := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K)≠0 := by
    rw [show (10 : K)=2*5 by ring]
    exact mul_ne_zero h2 h5
  have hraw := movingTw_ordered (K:=K) p hp
  have hfifth := movingTw_fifth_ordered p hp u hu
  have he : (4*movingH p (4 : K) (1/4)-22*movingH p (1/4) (1/4)-
      11*movingH p 4 4-7*movingH p (1/4) 4)/5-
      6*movingH p 0 (1/4)+3*movingH p 0 4 =
      3*originalT5 p u/2-2*originalG p (1/5)/5+
        (11/10 : K)*originalG p (1/5)-rationalOrderedRows p := by
    linear_combination -hraw-hfifth
  calc
    _ = _ := by
      field_simp [h5]
      ring
    _ = _ := he
    _ = _ := by
      field_simp [h2,h5,h10]
      ring

/-- The exact actual H term, with both root branches and every finite diagonal. -/
theorem original_ordered_H_weight (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    (-90*(originalHx p).eval (1/4)+45*(originalHx p).eval 4-
      66*(originalHa p).eval (1/4)-21*(originalHa p).eval 4+
      12*(originalHb p).eval (1/4)-33*(originalHb p).eval 4)/
      (2*WPFiniteABSourceTail.epsilon p) =
      (3/2 : K)*originalT5 p u+(7/10 : K)*originalG p (1/5)-
      (17/5 : K)*WPFiniteField.R p (-2)+
      (18/5 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)^2-
      (63/5 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)*
        (WPFiniteInversion.integerFermatQuotient p 3 : K)+
      (18/5 : K)*(WPFiniteInversion.integerFermatQuotient p 3 : K)^2 := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have heps : (WPFiniteABSourceTail.epsilon p : K)≠0 := pow_ne_zero _ h5
  calc
    _ = -6*movingH p (0 : K) (1/4)+3*movingH p 0 4-
        (22/5 : K)*movingH p (1/4) (1/4)-(7/5 : K)*movingH p (1/4) 4+
        (4/5 : K)*movingH p 4 (1/4)-(11/5 : K)*movingH p 4 4 := by
      unfold originalHx originalHa originalHb
      rw [original_unitPrimitive_movingH p hp,original_unitPrimitive_movingH p hp,
        original_unitPrimitive_movingH p hp,original_unitPrimitive_movingH p hp,
        original_unitPrimitive_movingH p hp,original_unitPrimitive_movingH p hp]
      field_simp [h2,h5,h15,heps]
      ring
    _ = _ := by
      rw [whole_movingH_ordered p hp u hu,actual_SB103_rational_combination p hp]
      unfold WPFieldAssembly.ActualRationalSignRows.q2 WPFieldAssembly.ActualRationalSignRows.q3
      ring

end WPFieldAssembly.SourceClosureUVOrderedH
