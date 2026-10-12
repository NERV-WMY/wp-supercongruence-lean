import WPFieldAssembly.ActualFiniteEntropyCarry

open scoped BigOperators
open WPPIntegralReduction WPActualRankTwoHatLift
  WPFieldAssembly.ActualFiniteEntropyCarry

namespace WPFieldAssembly.ActualProperProductTaylor

set_option maxHeartbeats 1000000

section Generic
variable {R : Type*} [CommRing R]

noncomputable def firstSum (u : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range n, u (j+1)

noncomputable def squareSum (u : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range n, (u (j+1))^2

noncomputable def pairSum (u : ℕ → R) : ℕ → R
  | 0 => 0
  | n+1 => pairSum u n+firstSum u n*u (n+1)

noncomputable def thirdRemainder (u : ℕ → R) (η : R) : ℕ → R
  | 0 => 0
  | n+1 => thirdRemainder u η n*(1-η*u (n+1))+pairSum u n*u (n+1)

noncomputable def metricProduct (u : ℕ → R) (η : R) (n : ℕ) : R :=
  ∏ j ∈ Finset.range n, (1-η*u (j+1))

/-- The entire product retains its third-order remainder before division. -/
theorem metricProduct_secondTaylor (u : ℕ → R) (η : R) (n : ℕ) :
    metricProduct u η n=1-η*firstSum u n+η^2*pairSum u n-
      η^3*thirdRemainder u η n := by
  induction n with
  | zero => simp [metricProduct, firstSum, pairSum, thirdRemainder]
  | succ n ih =>
    simp only [metricProduct, Finset.prod_range_succ] at ih ⊢
    rw [ih]
    simp only [firstSum, Finset.sum_range_succ, pairSum, thirdRemainder]
    ring

theorem pairSum_square_identity (u : ℕ → R) (n : ℕ) :
    2*pairSum u n=(firstSum u n)^2-squareSum u n := by
  induction n with
  | zero => simp [pairSum, firstSum, squareSum]
  | succ n ih =>
    simp only [pairSum, firstSum, squareSum, Finset.sum_range_succ] at ih ⊢
    linear_combination ih

noncomputable def dividedProduct (u : ℕ → R) (η : R) (n : ℕ) : R :=
  -firstSum u n+η*pairSum u n-η^2*thirdRemainder u η n

theorem dividedProduct_source (u : ℕ → R) (η : R) (n : ℕ) :
    η*dividedProduct u η n=metricProduct u η n-1 := by
  rw [metricProduct_secondTaylor, dividedProduct]
  ring
end Generic

noncomputable def properEtaIntegral (p : ℕ) [Fact p.Prime] : integralRationals p :=
  (p : integralRationals p)*smallIntegralInverse p 3

noncomputable def properProductIntegral (p n : ℕ) [Fact p.Prime] : integralRationals p :=
  metricProduct (fun j => smallIntegralInverse p j) (properEtaIntegral p) n

noncomputable def properPairIntegral (p n : ℕ) [Fact p.Prime] : integralRationals p :=
  pairSum (fun j => smallIntegralInverse p j) n

noncomputable def properThirdIntegral (p n : ℕ) [Fact p.Prime] : integralRationals p :=
  thirdRemainder (fun j => smallIntegralInverse p j) (properEtaIntegral p) n

noncomputable def properEndpointIntegral (p n : ℕ) [Fact p.Prime] : integralRationals p :=
  dividedProduct (fun j => smallIntegralInverse p j) (properEtaIntegral p) n

/-- The rational Jacobi endpoint is specified by its literal product quotient. -/
noncomputable def properEndpointQ (p n : ℕ) : ℚ :=
  ((∏ j ∈ Finset.range n, (1-((p : ℚ)/3)/((j+1 : ℕ) : ℚ)))-1)/((p : ℚ)/3)

theorem properEtaIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (properEtaIntegral p).val=(p : ℚ)/3 := by
  change (integralRationals p).subtype (properEtaIntegral p)=_
  rw [properEtaIntegral, map_mul, map_natCast]
  change (p : ℚ)*(smallIntegralInverse p 3).val=_
  rw [smallIntegralInverse_value p 3 (by omega) (by omega)]
  ring

theorem properProductIntegral_value (p n : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hn : n < p) :
    (properProductIntegral p n).val=
      ∏ j ∈ Finset.range n, (1-((p : ℚ)/3)/((j+1 : ℕ) : ℚ)) := by
  change (integralRationals p).subtype (properProductIntegral p n)=_
  rw [properProductIntegral, metricProduct, map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [map_sub, map_one, map_mul]
  change 1-(properEtaIntegral p).val*(smallIntegralInverse p (j+1)).val=_
  rw [properEtaIntegral_value p hp, smallIntegralInverse_value p (j+1) (by omega) (by omega)]
  ring

theorem properEndpointIntegral_value (p n : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hn : n < p) :
    (properEndpointIntegral p n).val=properEndpointQ p n := by
  have h := congrArg (integralRationals p).subtype
    (dividedProduct_source (fun j => smallIntegralInverse p j) (properEtaIntegral p) n)
  change (integralRationals p).subtype
    (properEtaIntegral p*properEndpointIntegral p n)=
      (integralRationals p).subtype (properProductIntegral p n-1) at h
  rw [map_mul, map_sub, map_one] at h
  change (properEtaIntegral p).val*(properEndpointIntegral p n).val=
    (properProductIntegral p n).val-1 at h
  rw [properEtaIntegral_value p hp, properProductIntegral_value p n hp hn] at h
  unfold properEndpointQ
  apply (eq_div_iff (by
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact div_ne_zero hp0 (by norm_num))).2
  linear_combination h

/-- The endpoint sign and its p² remainder agree with the original divided product. -/
theorem properEndpointIntegral_firstTaylor (p n : ℕ) [Fact p.Prime] :
    -properEndpointIntegral p n=fullHarmonicIntegral p n-
      (p : integralRationals p)*smallIntegralInverse p 3*properPairIntegral p n+
      (p : integralRationals p)^2*(smallIntegralInverse p 3)^2*properThirdIntegral p n := by
  unfold properEndpointIntegral dividedProduct firstSum fullHarmonicIntegral
    properPairIntegral properThirdIntegral properEtaIntegral
  ring

theorem properPairIntegral_field (p n : ℕ) [Fact p.Prime] (hn : n < p) :
    2*residueHom p (properPairIntegral p n)=
      (residueHom p (fullHarmonicIntegral p n))^2-
        ∑ j ∈ Finset.range n, (((j+1 : ℕ) : ZMod p)⁻¹)^2 := by
  have h := congrArg (residueHom p)
    (pairSum_square_identity (fun j => smallIntegralInverse p j) n)
  simp only [map_mul, map_ofNat, map_sub, map_pow, squareSum, map_sum] at h
  change 2*residueHom p (properPairIntegral p n)=
      (residueHom p (fullHarmonicIntegral p n))^2-
        ∑ j ∈ Finset.range n, (residueHom p (smallIntegralInverse p (j+1)))^2 at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [smallIntegralInverse_field p (j+1) (by omega) (by omega)]

end WPFieldAssembly.ActualProperProductTaylor
