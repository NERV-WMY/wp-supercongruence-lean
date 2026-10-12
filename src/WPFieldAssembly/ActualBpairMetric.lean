import WPFieldAssembly.ActualSimplePoleResidue
import WPFieldAssembly.ActualBpairBranchSquare

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

private theorem invert_twice (F : K[T;T⁻¹]) : invert (invert F)=F := by
  ext j
  rw [invert_apply,invert_apply,neg_neg]

private theorem whole_lowBand (n : ℕ) (P : K[X]) (hP : P.natDegree≤n) :
    WPFiniteJHighCoefficient.lowBand (n+1) P=P := by
  ext j
  rw [WPFiniteJHighCoefficient.lowBand_coeff]
  by_cases hj : j<n+1
  · rw [if_pos hj]
  · rw [if_neg hj,coeff_eq_zero_of_natDegree_lt (by omega)]

/-- This is the full reciprocal polynomial coefficient, with no omitted lower band. -/
theorem originPole_shifted_polynomial (p n : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (P : K[X]) (hP : P.natDegree≤n) :
    originPole (T (-(n : ℤ))*P.toLaurent)=
      ((1/4 : K)^n*P.eval 4-(4 : K)^n*P.eval (1/4))/15 := by
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have ha : (1/4 : K)≠0 := div_ne_zero one_ne_zero h4
  rw [originPole_trunc_inverse,map_mul,invert_T,neg_neg]
  have h₁ := WPFiniteJWeightedResidue.trunc_shift_invert_eval P n (1/4 : K) ha
  have h₂ := WPFiniteJWeightedResidue.trunc_shift_invert_eval P n (4 : K) h4
  rw [whole_lowBand n P hP] at h₁ h₂
  simp only [one_div,inv_inv] at h₁
  simp only [one_div] at h₂ ⊢
  rw [h₁,h₂]

private theorem four_endpoint_powers (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (4 : K)^((p-1)/2-1)=1/4 ∧ (1/4 : K)^((p-1)/2-1)=4 ∧
      (1/4 : K)^((p-1)/2)=1 := by
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hN := WPFiniteWSource.half_exponent p hp
  have hpow := WPFiniteWSource.four_half_power (K:=K) p hp
  have hsucc : (p-1)/2-1+1=(p-1)/2 := by omega
  have h₁ : (4 : K)^((p-1)/2-1)=1/4 := by
    apply (eq_div_iff h4).mpr
    rw [←pow_succ,hsucc,hpow]
  refine ⟨h₁,?_,?_⟩
  · rw [one_div,inv_pow,h₁]
    simp
  · rw [one_div,inv_pow,hpow,inv_one]

/-- The original whole branch quotient has its two literal endpoint values. -/
theorem branchPolynomial_metric_endpoints (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (branchPolynomial p : K[X]).eval (1/4)=
      16*((Dstar p : K[X]).eval (1/4)+(Dstar p).eval 4) ∧
    (branchPolynomial p : K[X]).eval 4=
      ((Dstar p : K[X]).eval (1/4)+(Dstar p).eval 4)/4 := by
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  obtain ⟨h4m,ham,haN⟩ := four_endpoint_powers (K:=K) p hp
  have hsa : (WPFiniteWSource.squaredCoordinate : K[X]).eval (1/4)=1/4 := by
    simp only [WPFiniteWSource.squaredCoordinate,eval_mul,eval_C,eval_add,eval_X,eval_one]
    field_simp [h4,h5]
    ring
  have hsb : (WPFiniteWSource.squaredCoordinate : K[X]).eval 4=1 := by
    simp only [WPFiniteWSource.squaredCoordinate,eval_mul,eval_C,eval_add,eval_X,eval_one]
    field_simp [h5]
    ring
  let v : Kˣ := Units.mk0 4 h4
  have hv : (v : K)=4 := rfl
  have hfactor : T (((p-1)/2-1 : ℕ) : ℤ)*Dsym p=
      WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2+1)*
        (branchPolynomial p : K[X]).toLaurent := by
    rw [←branchNumerator_toLaurent p hp,←map_pow,←map_mul,
      ←branchPolynomial_factor p hp]
  have ha := congrArg (LaurentPolynomial.eval₂ (RingHom.id K) v⁻¹) hfactor
  have hb := congrArg (LaurentPolynomial.eval₂ (RingHom.id K) v) hfactor
  simp only [Dsym,map_mul,map_add,map_pow,
    WPFiniteJWeightedResidue.inversion_eval,LaurentPolynomial.eval₂_T_n,
    LaurentPolynomial.eval₂_toLaurent,eval₂_id,Units.val_inv_eq_inv_val,hv,inv_inv] at ha hb
  simp only [←one_div (4 : K),h4m,ham,hsa,hsb,pow_succ,haN,one_mul,one_pow] at ha hb
  constructor
  · field_simp [h4] at ha
    linear_combination -ha
  · rw [←hb]
    ring

/-- The full branch factor determines the entire rational-denominator metric residue. -/
theorem Dsym_metric_pole (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    originPole (WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*Dsym p)=
      -((Dstar p : K[X]).eval (1/4)+(Dstar p).eval 4)/25 := by
  let n := (p-1)/2-1
  let P : K[X] := branchPolynomial p
  have hN := WPFiniteWSource.half_exponent p hp
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hfactor : T (n : ℤ)*Dsym p=
      WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2+1)*P.toLaurent := by
    dsimp only [n,P]
    rw [←branchNumerator_toLaurent p hp,←map_pow,←map_mul,
      ←branchPolynomial_factor p hp]
  have hsp : (WPFiniteWSource.squaredCoordinate : K[X])^p=
      Polynomial.C (1/5 : K)*(X^p+1) := by
    have h5p : (5 : K)^p=5 := by
      simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K:=K) p 5
    rw [WPFiniteWSource.squaredCoordinate,mul_pow,←map_pow,inv_pow,h5p,
      add_pow_char (p:=p),one_pow]
    rw [one_div]
  have hphase : WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*Dsym p=
      LaurentPolynomial.C (1/5 : K)*
        (((X^(p-n)*P : K[X]).toLaurent)+T (-(n : ℤ))*P.toLaurent) := by
    have hcancel : (T (-(n : ℤ)) : K[T;T⁻¹])*T (n : ℤ)=1 := by
      rw [←T_add,neg_add_cancel,T_zero]
    have hshift : (T (-(n : ℤ)) : K[T;T⁻¹])*T (p : ℤ)=T ((p-n : ℕ) : ℤ) := by
      rw [←T_add]
      congr 1
      dsimp only [n]
      omega
    calc
      _ = (T (-(n : ℤ))*T (n : ℤ))*
          (WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*Dsym p) := by
        rw [hcancel,one_mul]
      _ = T (-(n : ℤ))*(WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*
          (T (n : ℤ)*Dsym p)) := by ring
      _ = T (-(n : ℤ))*(WPFiniteWSource.squaredCoordinate.toLaurent^p*P.toLaurent) := by
        rw [hfactor,←mul_assoc
          (WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2))
          (WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2+1)) P.toLaurent,
          ←pow_add,show (p-1)/2+((p-1)/2+1)=p by omega]
      _ = _ := by
        rw [←map_pow,hsp]
        simp only [map_mul,map_add,Polynomial.toLaurent_C,Polynomial.toLaurent_X_pow,
          map_one]
        calc
          _ = LaurentPolynomial.C (1/5 : K)*
              ((T (-(n : ℤ))*T (p : ℤ))*P.toLaurent+T (-(n : ℤ))*P.toLaurent) := by ring
          _ = _ := by rw [hshift]
  have hdeg : P.natDegree≤n := by
    have hd := branchPolynomial_degree (K:=K) p hp
    dsimp only [P,n]
    omega
  rw [hphase,originPole_C_mul,originPole_add,originPole_polynomial,zero_add,
    originPole_shifted_polynomial p n hp P hdeg]
  obtain ⟨h4m,ham,_⟩ := four_endpoint_powers (K:=K) p hp
  obtain ⟨ha,hb⟩ := branchPolynomial_metric_endpoints (K:=K) p hp
  dsimp only [P,n]
  rw [h4m,ham,ha,hb]
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := by
    rw [show (15 : K)=3*5 by ring]
    exact mul_ne_zero h3 h5
  have h25 : (25 : K)≠0 := by
    rw [show (25 : K)=5^2 by ring]
    exact pow_ne_zero 2 h5
  field_simp [h3,h4,h5,h15,h25]
  ring

noncomputable def actualDMetric (p : ℕ) : K :=
  (invert (Dstar p : K[X]).toLaurent*D (Dstar p : K[X]).toLaurent).coeff (-1)

/-- The diagonal pairing is fixed by the whole branch source, in both prime classes. -/
theorem actualDMetric_endpoints (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    actualDMetric (K:=K) p=
      (4*(Dstar p : K[X]).eval (1/4)-(Dstar p).eval 4)/15 := by
  have he := congrArg (fun P : K[X] => P.toLaurent)
    (Dstar_cleared_source (K:=K) p hp)
  simp only [map_mul,map_sub,map_one,map_pow,Polynomial.toLaurent_C,←D_toLaurent] at he
  have hc : (WPFiniteZSource.Abar : K[X]).toLaurent*
      (Dsym p*D (Dstar p : K[X]).toLaurent)=
      LaurentPolynomial.C (5/2 : K)*(Dsym p-
        WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*Dsym p) := by
    linear_combination Dsym p*he
  have hh := congrArg originPole hc
  rw [originPole_cleared p hp,originPole_C_mul,originPole_sub,Dsym_metric_pole p hp] at hh
  have hpoly : ((Dstar p : K[X]).toLaurent*D (Dstar p : K[X]).toLaurent).coeff (-1)=0 := by
    rw [D_toLaurent,←map_mul]
    exact WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))
  have hleft : (Dsym p*D (Dstar p : K[X]).toLaurent).coeff (-1)=actualDMetric (K:=K) p := by
    rw [Dsym,add_mul,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hpoly,zero_add]
    rfl
  have hpole : originPole (Dsym p)=
      ((Dstar p : K[X]).eval (1/4)-(Dstar p).eval 4)/15 := by
    rw [Dsym,originPole_add,originPole_polynomial,zero_add,originPole_trunc_inverse,
      invert_twice,trunc_toLaurent]
  rw [hleft,hpole] at hh
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := by
    rw [show (15 : K)=3*5 by ring]
    exact mul_ne_zero h3 h5
  have h25 : (25 : K)≠0 := by
    rw [show (25 : K)=5^2 by ring]
    exact pow_ne_zero 2 h5
  linear_combination (norm := (field_simp [h2,h3,h5,h15,h25]; ring)) hh

theorem actualDMetric_fermat (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    actualDMetric (K:=K) p=WPFiniteNC122.q p/5-
      (WPFiniteInversion.integerFermatQuotient p 3 : K)/10 := by
  obtain ⟨ha,hb⟩ := Dstar_endpoints (K:=K) p hp
  rw [actualDMetric_endpoints p hp,ha,hb]
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : K)≠0 := by
    rw [show (6 : K)=2*3 by ring]
    exact mul_ne_zero h2 h3
  have h10 : (10 : K)≠0 := by
    rw [show (10 : K)=2*5 by ring]
    exact mul_ne_zero h2 h5
  have h15 : (15 : K)≠0 := by
    rw [show (15 : K)=3*5 by ring]
    exact mul_ne_zero h3 h5
  unfold WPFiniteNC122.h WPFiniteNC122.q
  field_simp [h2,h3,h5,h6,h10,h15]
  ring

end WPFieldAssembly.ActualBpairContraction
