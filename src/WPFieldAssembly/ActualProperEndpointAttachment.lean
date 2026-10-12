import WPFieldAssembly.ActualTC1Family
import WPFieldAssembly.ActualProperEndpointCarry

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPActualRankTwoLowTaylor WPActualRankTwoHatLift
  WPFieldAssembly.ActualTC1Family WPFieldAssembly.ActualBalancedCarry
  WPFieldAssembly.ActualProperProductTaylor WPFieldAssembly.ActualProperEndpointCarry

namespace WPFieldAssembly.ActualProperEndpointAttachment

set_option maxHeartbeats 1200000

section Generic
variable {K : Type*} [CommRing K]

theorem endLift_eval_endpoint (P : EtaPoly K) (a : K) :
    ((endLift P).eval (C a)).eval 1=(P.eval (C a)).eval 1 := by
  change (((P.map (Polynomial.evalRingHom (1 : K))).map
    (Polynomial.C : K →+* K[X])).eval (C a)).eval 1=_
  rw [eval_map_apply, eval_C]
  have h := eval_map_apply (p := P) (Polynomial.evalRingHom (1 : K)) (C a)
  change ((P.map (Polynomial.evalRingHom (1 : K))).eval ((C a).eval 1))=
    (P.eval (C a)).eval 1 at h
  simpa only [eval_C] using h

theorem metricFactor_eval_endpoint (u : ℕ → K) (m : ℕ) (a : K) :
    ((metricFactor u m).eval (C a)).eval 1=metricProduct u a m := by
  simp only [metricFactor_product, metricProduct, eval_prod,
    eval_sub, eval_one, eval_mul, cc, ActualTC1Family.eta, eval_C, eval_X, mul_comm]

/-- The endpoint is attached to the original Jacobi family through its exact product. -/
theorem properEta_eval_product (u : ℕ → K) (m : ℕ) (a : K)
    (hu : UnitsTo u m) :
    a*((properEta u m).eval (C a)).eval 1=metricProduct u a m-1 := by
  have h := congrArg (fun P : EtaPoly K => (P.eval (C a)).eval 1)
    (properEta_endpoint u m hu)
  simpa only [eval_mul, ActualTC1Family.eta, eval_X, eval_C, eval_sub, eval_one,
    endLift_eval_endpoint, metricFactor_eval_endpoint] using h
end Generic

theorem balanced_eta_eq_literal (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (p : integralRationals p)*(2*integralSixth p (by omega))=
      ActualProperProductTaylor.properEtaIntegral p := by
  apply Subtype.ext
  change (integralRationals p).subtype
    ((p : integralRationals p)*(2*integralSixth p (by omega)))=_
  rw [map_mul, map_mul, map_natCast, map_ofNat]
  change (p : ℚ)*(2*(1/6 : ℚ))=
    (ActualProperProductTaylor.properEtaIntegral p).val
  rw [properEtaIntegral_value p hp]
  ring

/-- No new endpoint lift replaces the balanced proper polynomial. -/
theorem balancedProper_endpoint_actual (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (balancedProperIntegral p hp).eval 1=properEndpointIntegral p (p/6) := by
  have h := properEta_eval_product (fun j => smallIntegralInverse p j) (p/6)
    (ActualProperProductTaylor.properEtaIntegral p) (integral_units p (p/6) (by omega))
  have hsource := dividedProduct_source (fun j => smallIntegralInverse p j)
    (ActualProperProductTaylor.properEtaIntegral p) (p/6)
  have hη : ActualProperProductTaylor.properEtaIntegral p ≠ 0 := by
    intro hz
    have hval := congrArg (integralRationals p).subtype hz
    change (ActualProperProductTaylor.properEtaIntegral p).val=0 at hval
    rw [properEtaIntegral_value p hp] at hval
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact (div_ne_zero hp0 (by norm_num)) hval
  rw [balancedProperIntegral, properEtaIntegral_generic, balanced_eta_eq_literal p hp]
  apply mul_left_cancel₀ hη
  change ActualProperProductTaylor.properEtaIntegral p*
      ((properEta (fun j => smallIntegralInverse p j) (p/6)).eval
        (C (ActualProperProductTaylor.properEtaIntegral p))).eval 1=
    ActualProperProductTaylor.properEtaIntegral p*
      dividedProduct (fun j => smallIntegralInverse p j) (ActualProperProductTaylor.properEtaIntegral p) (p/6)
  linear_combination h-hsource

/-- The actual NC95 h_* first difference, with its source-selected sign. -/
theorem balancedProper_hstar_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    -(balancedProperIntegral p hp).eval 1=endpointOriginIntegral p+
      (p : integralRationals p)*endpointCarryIntegral p hp := by
  rw [balancedProper_endpoint_actual p hp]
  exact actual_literal_hstar_firstTaylor p hp

end WPFieldAssembly.ActualProperEndpointAttachment
