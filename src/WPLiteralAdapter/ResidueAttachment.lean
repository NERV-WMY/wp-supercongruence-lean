import WPLiteralAdapter.ResidueNumerator

open scoped BigOperators
open Polynomial WPForcedSourceStokes WPFiniteConductorPolynomial

namespace WPLiteralAdapter

noncomputable section

set_option maxHeartbeats 2000000

local notation "ι" => algebraMap ℚ[X] (RatFunc ℚ)

theorem residue_native_theta_degree (p : ℕ) (hp : 2≤p) (k : ℕ) :
    (thetaPower k (WPReview.nativePolynomial p)).natDegree≤p-1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hnp : ¬n<p := by omega
  simp only [thetaPower_coeff, WPReview.nativePolynomial_coeff, if_neg hnp, mul_zero]

theorem residue_native_ordinary_degree (p : ℕ) (hp : 2≤p) (i : Fin 3) :
    (nativeOrdinaryPolynomial p i).natDegree≤p+2 := by
  have hθ (k : ℕ) : (thetaPower k (WPReview.nativePolynomial p)).natDegree≤p-1 :=
    residue_native_theta_degree p hp k
  have hF : (WPReview.nativePolynomial p).natDegree≤p-1 := by simpa [thetaPower] using hθ 0
  have htprod (P : ℚ[X]) (k : ℕ) (hP : P.natDegree≤3) :
      (P*thetaPower k (WPReview.nativePolynomial p)).natDegree≤p+2 := by
    have hm := Polynomial.natDegree_mul_le (p:=P) (q:=thetaPower k (WPReview.nativePolynomial p))
    have hk := hθ k
    omega
  have hfprod (P : ℚ[X]) (hP : P.natDegree≤3) :
      (P*WPReview.nativePolynomial p).natDegree≤p+2 := by
    have hm := Polynomial.natDegree_mul_le (p:=P) (q:=WPReview.nativePolynomial p)
    omega
  have hL : (1-X : ℚ[X]).natDegree≤1 :=
    (Polynomial.natDegree_sub_le _ _).trans (by norm_num)
  have hhalf : (C (1/2)*X : ℚ[X]).natDegree≤3 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (by norm_num)
  have hfive : (C (5/72)*X : ℚ[X]).natDegree≤3 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (by norm_num)
  have hXX : (X*(X-1) : ℚ[X]).natDegree≤3 := by
    have hm := Polynomial.natDegree_mul_le (p:=(X : ℚ[X])) (q:=X-1)
    have hX : (X : ℚ[X]).natDegree=1 := by simp
    have hL' : (X-1 : ℚ[X]).natDegree≤1 :=
      (Polynomial.natDegree_sub_le _ _).trans (by norm_num)
    omega
  have hCXX : (C 2*X^2 : ℚ[X]).natDegree≤2 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (by norm_num)
  have hCXXL : (C 2*X^2*(1-X) : ℚ[X]).natDegree≤3 := by
    have hm := Polynomial.natDegree_mul_le (p:=(C 2*X^2 : ℚ[X])) (q:=1-X)
    omega
  have hv0 : ((1-X)*thetaPower 2 (WPReview.nativePolynomial p)-
      C (1/2)*X*thetaPower 1 (WPReview.nativePolynomial p)-
      C (5/72)*X*WPReview.nativePolynomial p).natDegree≤p+2 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_sub_le _ _).trans
      exact max_le (htprod (1-X) 2 (by omega)) (htprod (C (1/2)*X) 1 hhalf)
    · exact hfprod (C (5/72)*X) hfive
  have hv1 : (X*(X-1)*thetaPower 1 (WPReview.nativePolynomial p)).natDegree≤p+2 :=
    htprod (X*(X-1)) 1 hXX
  have hv2 : (C 2*X^2*(1-X)*WPReview.nativePolynomial p).natDegree≤p+2 :=
    hfprod (C 2*X^2*(1-X)) hCXXL
  fin_cases i
  · simpa [nativeOrdinaryPolynomial] using hv0
  · simpa [nativeOrdinaryPolynomial] using hv1
  · simpa [nativeOrdinaryPolynomial] using hv2

theorem residue_native_ordinary_sum (p : ℕ) (hp : 2≤p)
    (q : RatFunc (RatFunc ℚ)) (i : Fin 3) :
    Polynomial.aeval q (nativeOrdinaryPolynomial p i)=∑ a∈Finset.range (p+3),
      RatFunc.C (RatFunc.C ((nativeOrdinaryPolynomial p i).coeff a))*q^a := by
  have hd : (nativeOrdinaryPolynomial p i).natDegree<p+3 := by
    have h := residue_native_ordinary_degree p hp i
    omega
  simpa only [Polynomial.aeval_def, outer_native_scalar] using
    Polynomial.eval₂_eq_sum_range' (algebraMap ℚ (RatFunc (RatFunc ℚ))) hd q

private theorem residue_escape_map_nonzero : ι escape≠0 := by
  apply RatFunc.algebraMap_ne_zero
  intro hz
  have hc := congrArg (fun P : ℚ[X] => P.coeff 0) hz
  norm_num [escape] at hc

private theorem residue_source_denominator_map_nonzero : ι (X^4*escape^2)≠0 := by
  rw [map_mul, map_pow, map_pow]
  exact mul_ne_zero (pow_ne_zero 4 (RatFunc.algebraMap_ne_zero X_ne_zero))
    (pow_ne_zero 2 residue_escape_map_nonzero)

theorem residue_lambda_power_denominator_cancel (a e : ℕ) (ha : 2≤a) :
    lambda^(a+e)/ι (X^4*escape^2)=RatFunc.C ((729/15625 : ℚ)^(a+e))*
      symbol^(3*(a+e)-4)/ι (escape^2) := by
  have hx : symbol≠0 := RatFunc.algebraMap_ne_zero X_ne_zero
  have he := residue_escape_map_nonzero
  have ht : (729/15625 : RatFunc ℚ)=RatFunc.C (729/15625 : ℚ) := by
    norm_num [map_div₀, _root_.map_ofNat]
  have hl : lambda^(a+e)=RatFunc.C ((729/15625 : ℚ)^(a+e))*symbol^(3*(a+e)) := by
    simp only [lambda, mul_pow, ← pow_mul, map_pow, ht]
  have hxp : symbol^(3*(a+e))=symbol^4*symbol^(3*(a+e)-4) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hl, hxp]
  simp only [map_mul, map_pow]
  dsimp only [symbol] at hx ⊢
  field_simp [hx, he]

/-- The selected and unselected chambers of one actual ordinary monomial. -/
theorem residue_monomial_closed (A : ℚ[X]) (u v : ℚ) (a b e : ℕ) (ha : 2≤a) :
    rationalResidue (RatFunc.C (2/ι (X^4*escape^2))*RatFunc.C (ι A)*bivS^e/bivConductor*
      (RatFunc.C (RatFunc.C u)*bivS^a)*(RatFunc.C (RatFunc.C v)*bivB^b)) =
      if a+e<b then ι (C (2*u*v*(729/15625 : ℚ)^(a+e))*X^(3*(a+e)-4)*A*
        residueInverseNumerator (b-a-e-1))/ι (escape^2) else 0 := by
  have hxC : (RatFunc.C (ι X) : RatFunc (RatFunc ℚ))≠0 :=
    (map_ne_zero (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ))).mpr
      (RatFunc.algebraMap_ne_zero X_ne_zero)
  have heC : (RatFunc.C (ι escape) : RatFunc (RatFunc ℚ))≠0 :=
    (map_ne_zero (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ))).mpr residue_escape_map_nonzero
  have hn : RatFunc.C (2/ι (X^4*escape^2))*RatFunc.C (ι A)*bivS^e/bivConductor*
      (RatFunc.C (RatFunc.C u)*bivS^a)*(RatFunc.C (RatFunc.C v)*bivB^b) =
    RatFunc.C (2*RatFunc.C u*RatFunc.C v*ι A*lambda^b/ι (X^4*escape^2))*
      (bivS^(a+e)/(bivS^b*bivConductor)) := by
    simp only [bivB, bivLambda, div_pow, pow_add, map_div₀, map_mul, map_pow, _root_.map_ofNat]
    field_simp [bivS_ne_zero, bivConductor_ne_zero, hxC, heC]
  rw [hn, rationalResidue_coefficient_mul, residue_conductor_polynomial,
    finite_quadratic_power_residue (a+e) b (ι m) lambda residue_lambda_ne_zero]
  by_cases hab : a+e<b
  · simp only [if_pos hab]
    rw [show b-(a+e)-1=b-a-e-1 by omega, residue_inverse_coefficient]
    have hpw : lambda^b=lambda^(a+e)*lambda^(b-a-e-1+1) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      _=2*RatFunc.C u*RatFunc.C v*ι A*ι (residueInverseNumerator (b-a-e-1))*
          (lambda^(a+e)/ι (X^4*escape^2)) := by
        rw [hpw]
        field_simp [residue_source_denominator_map_nonzero, residue_lambda_ne_zero]
      _=_ := by
        rw [residue_lambda_power_denominator_cancel a e ha]
        simp only [map_mul, map_pow, RatFunc.algebraMap_C, _root_.map_ofNat, div_eq_mul_inv]
        dsimp only [symbol]
        ring
  · simp only [if_neg hab, mul_zero]

theorem residue_actual_monomial_residue (p : ℕ) (hp : 2≤p) (i j : Fin 3) (a b : ℕ) :
    rationalResidue (bivBsDivU i j*
      (RatFunc.C (RatFunc.C ((nativeOrdinaryPolynomial p i).coeff a))*bivS^a)*
      (RatFunc.C (RatFunc.C ((nativeOrdinaryPolynomial p j).coeff b))*bivB^b)) =
      ι (residueNumeratorTerm p i j a b 0+residueNumeratorTerm p i j a b 1)/ι (escape^2) := by
  by_cases ha : 2≤a
  · have hterm (e : ℕ) : rationalResidue
        (RatFunc.C (2/ι (X^4*escape^2))*RatFunc.C (ι (residueMatrix e i j))*bivS^e/bivConductor*
          (RatFunc.C (RatFunc.C ((nativeOrdinaryPolynomial p i).coeff a))*bivS^a)*
          (RatFunc.C (RatFunc.C ((nativeOrdinaryPolynomial p j).coeff b))*bivB^b)) =
        ι (residueNumeratorTerm p i j a b e)/ι (escape^2) := by
      rw [residue_monomial_closed (residueMatrix e i j) ((nativeOrdinaryPolynomial p i).coeff a)
        ((nativeOrdinaryPolynomial p j).coeff b) a b e ha]
      by_cases hab : a+e<b
      · rw [if_pos hab, residueNumeratorTerm, if_pos (show 2≤a ∧ a+e+1≤b from ⟨ha, by omega⟩)]
      · rw [if_neg hab, residueNumeratorTerm,
          if_neg (show ¬(2≤a ∧ a+e+1≤b) by omega), map_zero, zero_div]
    have hM0 : residueMatrix 0 i j=residueAbar i j := by simp [residueMatrix]
    have hM1 : residueMatrix 1 i j=residueLPbar i j := by simp [residueMatrix]
    have hsplit : bivBsDivU i j*
        (RatFunc.C (RatFunc.C ((nativeOrdinaryPolynomial p i).coeff a))*bivS^a)*
        (RatFunc.C (RatFunc.C ((nativeOrdinaryPolynomial p j).coeff b))*bivB^b) =
      (RatFunc.C (2/ι (X^4*escape^2))*RatFunc.C (ι (residueMatrix 0 i j))*bivS^0/bivConductor*
        (RatFunc.C (RatFunc.C ((nativeOrdinaryPolynomial p i).coeff a))*bivS^a)*
        (RatFunc.C (RatFunc.C ((nativeOrdinaryPolynomial p j).coeff b))*bivB^b))+
      (RatFunc.C (2/ι (X^4*escape^2))*RatFunc.C (ι (residueMatrix 1 i j))*bivS^1/bivConductor*
        (RatFunc.C (RatFunc.C ((nativeOrdinaryPolynomial p i).coeff a))*bivS^a)*
        (RatFunc.C (RatFunc.C ((nativeOrdinaryPolynomial p j).coeff b))*bivB^b)) := by
      rw [residue_bs_actual, hM0, hM1]
      simp only [pow_zero, pow_one, mul_one, div_eq_mul_inv]
      ring
    rw [hsplit, rationalResidue_add, hterm 0, hterm 1, ← add_div, ← map_add]
  · have hz := native_ordinary_first_two_zero p hp i
    have hu : (nativeOrdinaryPolynomial p i).coeff a=0 := by
      have ha' : a=0 ∨ a=1 := by omega
      rcases ha' with rfl | rfl
      · exact hz.1
      · exact hz.2
    have hN (e : ℕ) : residueNumeratorTerm p i j a b e=0 := by
      rw [residueNumeratorTerm, if_neg (show ¬(2≤a ∧ a+e+1≤b) by omega)]
    simp [hu, hN 0, hN 1, rationalResidue, laurentResidue]

/-- The actual full residue has its finite numerator; no origin value or degree cap is assumed. -/
theorem actual_conductor_residue_numerator (p : ℕ) (hp : 2≤p) :
    actualConductorResidue p=ι (actualResidueNumerator p)/ι (escape^2) := by
  classical
  have hpair (i j : Fin 3) : bivBsDivU i j*
      Polynomial.aeval bivS (nativeOrdinaryPolynomial p i)*Polynomial.aeval bivB (nativeOrdinaryPolynomial p j) =
      ∑ b∈Finset.range (p+3), ∑ a∈Finset.range (p+3), bivBsDivU i j*
        (RatFunc.C (RatFunc.C ((nativeOrdinaryPolynomial p i).coeff a))*bivS^a)*
        (RatFunc.C (RatFunc.C ((nativeOrdinaryPolynomial p j).coeff b))*bivB^b) := by
    rw [residue_native_ordinary_sum p hp bivS i, residue_native_ordinary_sum p hp bivB j,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [actualConductorResidue, actual_conductor_ordinary_pairing]
  simp_rw [hpair, rationalResidue_sum, residue_actual_monomial_residue p hp]
  simp only [actualResidueNumerator, map_sum, Finset.sum_div]

end

end WPLiteralAdapter
