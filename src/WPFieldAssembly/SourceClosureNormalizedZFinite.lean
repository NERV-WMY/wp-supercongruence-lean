import WPFieldAssembly.SourceClosurePSquareWeightEvaluation
import WPFieldAssembly.SourceClosureVbalJWeightedTrace

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteProductTail WPFiniteABSourceTail
  WPFiniteWSource WPFiniteJNormalization WPFiniteJHighCoefficient WPFiniteJCarrier
  WPFieldAssembly.ActualUVSourceIdentification WPFieldAssembly.SourceClosureUVDescent
  WPFieldAssembly.SourceClosureUVFieldTransport WPFieldAssembly.SourceClosureUVPhaseTrace
  WPFieldAssembly.SourceClosureBalancedNativeBetaTransport
  WPFieldAssembly.SourceClosureBalancedNativeBetaIdentification
  WPFieldAssembly.SourceClosurePSquareTrace WPFieldAssembly.SourceClosurePSquareTail
  WPFieldAssembly.SourceClosurePSquareWeightEvaluation
  WPFieldAssembly.SourceClosureVbalJHighElimination WPFieldAssembly.SourceClosureVbalJWeightedTrace

namespace WPFieldAssembly.SourceClosureNormalizedZFinite

set_option maxHeartbeats 1800000

variable {K L : Type*} [Field K] [Field L]

/- STATEMENT_FIDELITY: the original Z=-P^2/2+GJ and original beta are
   combined under the SAME weights 2/3 and -207/4. Both finite pieces
   are attached to their original carriers before their entropy squares
   are collected. Proper primitives and the full fifth alphabet remain
   actual finite definitions. No free trace, endpoint, scalar assignment,
   or low-density vanishing premise is introduced. -/

theorem originalPSquareHRow_transport (f : K →+* L) (p : ℕ) :
    f (originalPSquareHRow p : K)=(originalPSquareHRow p : L) := by
  unfold originalPSquareHRow
  simp only [map_add,map_sub,map_mul,map_neg,map_div₀,map_one,map_ofNat,
    polynomial_eval_transport,originalHa,originalHb,originalHx,
    unitPrimitive_transport,W_transport,map_zero]

theorem originalPSquareFiniteValue_transport (f : K →+* L) (p : ℕ)
    [Fact p.Prime] [CharP K p] [CharP L p] :
    f (originalPSquareFiniteValue p : K)=(originalPSquareFiniteValue p : L) := by
  unfold originalPSquareFiniteValue
  simp only [map_add,map_sub,map_mul,map_div₀,map_pow,map_ofNat,
    originalPSquareHRow_transport,epsilon_transport,finiteDilog_transport,
    finiteLog_transport,descendedC_transport,WPFiniteNC122.q,WPFiniteJNormalization.r,
    map_intCast]

noncomputable def normalizedZFiniteValue (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) : K :=
  -22*originalPSquareHRow p/(15*epsilon p)-WPFiniteField.R p (16 : K)/30-
    159*(WPFiniteNC122.q p)^2/25+
    129*WPFiniteNC122.q p*WPFiniteJNormalization.r p/25-
    9*(WPFiniteJNormalization.r p)^2/10-
    2*WPFiniteNC122.q p*WPFiniteField.ell p (16 : K)/25-
    11*WPFiniteJNormalization.r p*WPFiniteField.ell p (16 : K)/100+
    119*(descendedC p)^2/25+92*WPFiniteNC122.q p*descendedC p/25+
    11*U_J p u/15-22*V_J p u/15+
    8*(2*(JdifferenceP p (W p)).eval (1/4)+(JdifferenceP p (W p)).eval 4)/(15*epsilon p)-
    69*(originPrimitive p (W p) (1/4)-originPrimitive p (W p) 4)/(5*epsilon p)

/-- Both quadratic branches give the actual normalized original Z finite value. -/
theorem actual_original_normalized_Z_finite (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (f : ZMod p →+* K) (u : K) (hu : u^2=1/5) :
    f ((2/3 : ZMod p)*originalWeightedFieldTrace p (originalDescendedZ p)-
      (207/4 : ZMod p)*actualOriginalBeta p)=normalizedZFiniteValue p u := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h8 : (8 : K)≠0 := WPFiniteField.denominator_ne_zero p 8
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K)≠0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h25 : (25 : K)≠0 := by
    rw [show (25 : K)=5^2 by ring]
    exact pow_ne_zero _ h5
  have h30 : (30 : K)≠0 := by
    rw [show (30 : K)=2*15 by ring]
    exact mul_ne_zero h2 h15
  have h50 : (50 : K)≠0 := by
    rw [show (50 : K)=2*25 by ring]
    exact mul_ne_zero h2 h25
  have h100 : (100 : K)≠0 := by
    rw [show (100 : K)=2^2*5^2 by ring]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h5)
  have heps : (epsilon p : K)≠0 := pow_ne_zero _ h5
  have hj := actual_original_normalized_GJ_fifth (K:=K) p hp f u hu
  change f ((2/3 : ZMod p)*originalWeightedFieldTrace p (GJ p)-
    (207/4 : ZMod p)*actualOriginalBetaJ p)=_ at hj
  rw [actual_normalized_Z_split p hp,map_add,
    actual_original_normalized_Psquare_finite p hp f u hu,hj,
    originalPSquareFiniteValue_transport f p]
  unfold normalizedZFiniteValue originalPSquareFiniteValue uSlot
  rw [originalC_descended p hp u hu]
  field_simp [heps,h2,h3,h5,h8,h10,h15,h25,h30,h50,h100]
  ring

end WPFieldAssembly.SourceClosureNormalizedZFinite
