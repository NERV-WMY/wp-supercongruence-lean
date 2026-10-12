import WPFieldAssembly.ActualEntropyCubic
import WPFieldAssembly.ActualEntropyOdd
import WPFieldAssembly.ActualEntropyLogAttachment
import WPFifthEntropy
import Mathlib.Analysis.Real.Sqrt

open Polynomial WPPIntegralReduction WPActualRankTwoHatLift
  WPFieldAssembly.ActualEntropyPolynomial WPFieldAssembly.ActualEntropyCubic
  WPFieldAssembly.ActualEntropyOdd WPFieldAssembly.ActualEntropyLogAttachment

namespace WPFieldAssembly.ActualEntropyFifth

set_option maxHeartbeats 1600000

section CharacteristicZero

variable {K : Type*} [Field K] [CharZero K]

theorem entropyIntegral_charZero_eval (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (z : K) :
    ((entropyIntegral p).map
      ((algebraMap ℚ K).comp (integralRationals p).subtype)).eval (z^2)=evenPower p z := by
  rw [←Polynomial.map_map, entropyIntegral_value, actual_evenPower p hp]

theorem oddEntropyIntegral_charZero_eval (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (z : K) :
    ((oddEntropyIntegral p).map
      ((algebraMap ℚ K).comp (integralRationals p).subtype)).eval z=oddPower p z := by
  rw [←Polynomial.map_map, oddEntropyIntegral_value p hp]
  simp only [oddEntropyQ, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, Polynomial.map_X,
    Polynomial.map_ofNat, eval_mul, eval_C, eval_sub, eval_pow, eval_add, eval_one,
    eval_X, eval_ofNat, map_div₀, map_one, map_mul, map_ofNat, map_natCast, oddPower]
  ring

/-- Characteristic-zero transport of the original whole polynomial p-division. -/
theorem entropy_charZero_evaluation_carry (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (z : K) :
    ((movingEvenQ p).map (algebraMap ℚ K)).eval (z^2)-evenPower p z=
      (p : K)*((entropyCarryIntegral p).map
        ((algebraMap ℚ K).comp (integralRationals p).subtype)).eval (z^2) := by
  have h := congrArg (fun P : ℚ[X] => (P.map (algebraMap ℚ K)).eval (z^2))
    (actual_entropy_polynomial_lift p)
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_natCast,
    eval_sub, eval_mul, eval_natCast, map_natCast] at h
  rw [actual_evenPower p hp, Polynomial.map_map] at h
  exact h

/-- The complete first difference still contains the quadratic and cubic sources. -/
noncomputable def fifthCarryValue (p : ℕ) [Fact p.Prime] (u : K) : K :=
  let q₂ : K := WPFiniteInversion.integerFermatQuotient p 2
  let q₅ : K := WPFiniteInversion.integerFermatQuotient p 5
  let U : K := (2 : K)^(p-1)
  let W : K := (5 : K)^(p-1)
  let E₁ := evenPower p u
  let E₂ := evenPower p (2*u)
  let O₁ := oddPower p u
  let O₂ := oddPower p (2*u)
  let r := u^p
  (q₂/U-(4/5 : K)*(q₂-q₅)/W)*E₂+
    ((4/5 : K)*(2*q₂-q₅+(p : K)*q₂^2)/W-4*q₂)*E₁+
    3*((fifthNormFirstIntegral p).val : K)+(4*q₂-q₂/U)*(fifthNormQ p : K)-
    (4/5 : K)*q₂*(q₂-q₅)/W+
    quadraticCorrection r (2*U*r) E₁ E₂ O₁ O₂+
    (1/(2*U)-1)*(E₂^2-O₂^2)+2*U*(E₁^2-O₁^2)+
    (p : K)*cubicCorrection E₁ E₂ O₁ O₂

/-- Exact fifth-point Taylor attachment; all quotients retain their integer normalization. -/
theorem actual_fifth_entropy_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (u : K) (hu : u^2=(1/5 : K)) :
    evenPower p (-(11/5 : K)*u)=
      (11/5 : K)*(evenPower p (2*u)-evenPower p u)-
      (16/5 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)+
      (3/2 : K)*(WPFiniteInversion.integerFermatQuotient p 5 : K)+
      (p : K)*fifthCarryValue p u := by
  let q₂ : K := WPFiniteInversion.integerFermatQuotient p 2
  let q₅ : K := WPFiniteInversion.integerFermatQuotient p 5
  let U : K := (2 : K)^(p-1)
  let W : K := (5 : K)^(p-1)
  have h2unit : (2 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h5unit : (5 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have hq₂ : q₂*(p : K)=U-1 := by
    dsimp only [q₂, U]
    exact_mod_cast WPFiniteInversion.integerFermatQuotient_mul p 2 (by simpa using h2unit)
  have hq₅ : q₅*(p : K)=W-1 := by
    dsimp only [q₅, W]
    exact_mod_cast WPFiniteInversion.integerFermatQuotient_mul p 5 (by simpa using h5unit)
  have hU : U=1+(p : K)*q₂ := by linear_combination -hq₂
  have hW : W=1+(p : K)*q₅ := by linear_combination -hq₅
  have hU0 : U ≠ 0 := pow_ne_zero _ (by norm_num)
  have hW0 : W ≠ 0 := pow_ne_zero _ (by norm_num)
  obtain ⟨hc₂,hc₁,_,hcJ,hcs⟩ := fifth_unit_coefficients (p : K) q₂ q₅
    (by rw [←hU]; exact hU0) (by rw [←hW]; exact hW0)
  rw [←hU, ←hW] at hc₂ hc₁ hcs
  rw [←hU] at hcJ
  have hJ : (fifthNormQ p : K)=q₅/2-(4/5 : K)*q₂+
      (p : K)*((fifthNormFirstIntegral p).val : K) := by
    have h := congrArg ((algebraMap ℚ K).comp (integralRationals p).subtype)
      (fifthNormIntegral_firstTaylor p hp)
    simp only [map_add, map_mul, map_natCast, RingHom.comp_apply,
      Subring.subtype_apply, fifthNormIntegral_value p hp,
      fifthNormLeadingIntegral, map_sub, map_mul, map_intCast, map_ofNat,
      smallIntegralInverse_value p 2 (by omega) (by omega),
      smallIntegralInverse_value p 5 (by omega) (by omega),
      map_div₀, map_one, map_ofNat] at h
    simp only [eq_ratCast] at h
    dsimp only [q₂, q₅]
    linear_combination h
  have he := actual_fifth_norm_eliminated p hp u hu
  dsimp only at he
  rw [actual_fifth_frobenius_norm p hp u hu, ←hW] at he
  change evenPower p (-(11/5 : K)*u)=
    -4*U*(1/(5*W))*q₂+(4-4*U*(1/(5*W))-1/U)*evenPower p (2*u)+
    (1+4*U^2*(1/(5*W))-4*U)*evenPower p u+(1/U-2+4*U)*(fifthNormQ p : K)+
    (p : K)*(quadraticCorrection (u^p) (2*U*u^p) (evenPower p u)
      (evenPower p (2*u)) (oddPower p u) (oddPower p (2*u))+
      (1/(2*U)-1)*((evenPower p (2*u))^2-(oddPower p (2*u))^2)+
      2*U*((evenPower p u)^2-(oddPower p u)^2))+
    (p : K)^2*cubicCorrection (evenPower p u) (evenPower p (2*u))
      (oddPower p u) (oddPower p (2*u)) at he
  have hscalar := hcs
  have hE₂ := hc₂
  have hE₁ := hc₁
  have hJF := hcJ
  have hS : -4*U*(1/(5*W))*q₂=-4*U*q₂/(5*W) := by ring
  have hC₂ : 4-4*U*(1/(5*W))-1/U=4-4*U/(5*W)-1/U := by ring
  have hC₁ : 1+4*U^2*(1/(5*W))-4*U=1+4*U^2/(5*W)-4*U := by ring
  rw [hS,hC₂,hC₁,hscalar,hE₂,hE₁,hJF] at he
  unfold fifthCarryValue
  dsimp only
  linear_combination he+3*hJ

end CharacteristicZero

/-- The actual cubic carry, with integral coefficients and its complete p² contribution. -/
noncomputable def fifthCarryPolynomial (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[X] :=
  let q₂ : integralRationals p := WPFiniteInversion.integerFermatQuotient p 2
  let q₅ : integralRationals p := WPFiniteInversion.integerFermatQuotient p 5
  let U : integralRationals p := (2 : integralRationals p)^(p-1)
  let iU : integralRationals p := (smallIntegralInverse p 2)^(p-1)
  let iW : integralRationals p := (smallIntegralInverse p 5)^(p-1)
  let a₂ := q₂*iU-4*smallIntegralInverse p 5*(q₂-q₅)*iW
  let a₁ := 4*smallIntegralInverse p 5*(2*q₂-q₅+(p : integralRationals p)*q₂^2)*iW-4*q₂
  let E₁ := (entropyIntegral p).comp (X^2)
  let E₂ := (entropyIntegral p).comp (C 4*X^2)
  let O₁ := oddEntropyIntegral p
  let O₂ := (oddEntropyIntegral p).comp (C 2*X)
  let r : (integralRationals p)[X] := X^p
  let s := C (2*U)*r
  let Q := -E₂^2-O₂^2-2*E₁*E₂+2*s*E₁*O₂+2*O₁*O₂-2*r*E₂*O₂-2*s*E₂*O₁
  let R := E₁*(E₂^2+O₂^2)-2*E₂*O₁*O₂
  C a₂*E₂+C a₁*E₁+
    C (3*fifthNormFirstIntegral p+(4*q₂-q₂*iU)*fifthNormIntegral p-
      4*smallIntegralInverse p 5*q₂*(q₂-q₅)*iW)+Q+
    C (smallIntegralInverse p 2*iU-1)*(E₂^2-O₂^2)+
    C (2*U)*(E₁^2-O₁^2)+C (p : integralRationals p)*R

section CharacteristicZeroCarry

variable {K : Type*} [Field K] [CharZero K]

private theorem smallInverse_charZero (p j : ℕ) [Fact p.Prime]
    (hj : 0 < j) (hjp : j < p) :
    ((algebraMap ℚ K).comp (integralRationals p).subtype) (smallIntegralInverse p j)=
      1/(j : K) := by
  rw [RingHom.comp_apply, Subring.subtype_apply, smallIntegralInverse_value p j hj hjp]
  simp only [map_div₀, map_one, map_natCast]

/-- The polynomial is the complete literal carry, rather than a selected field digit. -/
theorem fifthCarryPolynomial_charZero_eval (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (u : K) :
    ((fifthCarryPolynomial p).map
      ((algebraMap ℚ K).comp (integralRationals p).subtype)).eval u=fifthCarryValue p u := by
  let φ : integralRationals p →+* K :=
    (algebraMap ℚ K).comp (integralRationals p).subtype
  have h₂ : φ (smallIntegralInverse p 2)=(1/2 : K) :=
    smallInverse_charZero p 2 (by omega) (by omega)
  have h₅ : φ (smallIntegralInverse p 5)=(1/5 : K) :=
    smallInverse_charZero p 5 (by omega) (by omega)
  have hJ : φ (fifthNormIntegral p)=(fifthNormQ p : K) := by
    change (algebraMap ℚ K) ((fifthNormIntegral p).val)=_
    rw [fifthNormIntegral_value p hp]
    rfl
  have hJ₁ : φ (fifthNormFirstIntegral p)=((fifthNormFirstIntegral p).val : K) := rfl
  have hE₁ := entropyIntegral_charZero_eval (K := K) p hp u
  have hE₂ : ((entropyIntegral p).map φ).eval (4*u^2)=evenPower p (2*u) := by
    rw [show 4*u^2=(2*u)^2 by ring]
    exact entropyIntegral_charZero_eval p hp (2*u)
  have hO₁ := oddEntropyIntegral_charZero_eval (K := K) p hp u
  have hO₂ := oddEntropyIntegral_charZero_eval (K := K) p hp (2*u)
  change ((entropyIntegral p).map φ).eval (u^2)=evenPower p u at hE₁
  change ((oddEntropyIntegral p).map φ).eval u=oddPower p u at hO₁
  change ((oddEntropyIntegral p).map φ).eval (2*u)=oddPower p (2*u) at hO₂
  change ((fifthCarryPolynomial p).map φ).eval u=_
  simp only [fifthCarryPolynomial, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_comp, Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat,
    Polynomial.map_natCast, Polynomial.map_intCast, eval_add, eval_sub,
    eval_neg, eval_mul, eval_C, eval_pow, eval_comp, eval_X, eval_ofNat,
    eval_natCast, eval_intCast, eval_one,
    map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, map_natCast, map_intCast,
    h₂, h₅, hJ, hJ₁, hE₁, hE₂, hO₁, hO₂]
  unfold fifthCarryValue quadraticCorrection cubicCorrection
  dsimp only
  rw [one_div_pow, one_div_pow]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

end CharacteristicZeroCarry

private theorem even_composition (p : ℕ) [Fact p.Prime]
    (P : (integralRationals p)[X]) (a : integralRationals p) :
    (P.comp (C a*X^2)).comp (-X)=P.comp (C a*X^2) := by
  rw [comp_assoc]
  congr 1
  simp only [mul_comp, C_comp, pow_comp, X_comp]
  ring

/-- The whole cubic carry is even; no odd Frobenius term is removed separately. -/
theorem fifthCarryPolynomial_even (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fifthCarryPolynomial p).comp (-X)=fifthCarryPolynomial p := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hx : (-(X : (integralRationals p)[X]))^p=-(X^p) := by
    exact hodd.neg_pow (X : (integralRationals p)[X])
  have hE₁ : ((entropyIntegral p).comp (X^2)).comp (-X)=
      (entropyIntegral p).comp (X^2) := by
    simpa only [C_1, one_mul] using even_composition p (entropyIntegral p) 1
  have hE₂ := even_composition p (entropyIntegral p) 4
  have hO₁ := oddEntropyIntegral_comp_neg p
  have hO₂ : ((oddEntropyIntegral p).comp (C 2*X)).comp (-X)=
      -((oddEntropyIntegral p).comp (C 2*X)) := by
    calc
      _ = ((oddEntropyIntegral p).comp (-X)).comp (C 2*X) := by
        rw [comp_assoc, comp_assoc]
        congr 1
        simp only [mul_comp, C_comp, X_comp, neg_comp]
        ring
      _ = _ := by rw [hO₁, neg_comp]
  simp only [fifthCarryPolynomial, add_comp, sub_comp, neg_comp,
    mul_comp, C_comp, pow_comp, ofNat_comp, X_comp, hE₁, hE₂,
    hO₁, hO₂, hx]
  ring

/-- Integral square contraction retains every even coefficient of the original carry. -/
theorem integral_even_square_pullback (p : ℕ) [Fact p.Prime]
    (P : (integralRationals p)[X]) (hP : P.comp (-X)=P) :
    (contract 2 P).comp (X^2)=P := by
  rw [←expand_eq_comp_X_pow]
  ext j
  rw [coeff_expand (by norm_num : 0 < (2 : ℕ))]
  by_cases hj : 2 ∣ j
  · rw [if_pos hj, coeff_contract (by norm_num : (2 : ℕ) ≠ 0),
      Nat.div_mul_cancel hj]
  · rw [if_neg hj]
    have hm : j % 2=1 := by
      have ht := Nat.mod_lt j (by norm_num : 0 < (2 : ℕ))
      have hz : j % 2 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hj
      omega
    have ho : Odd j := ⟨j/2, by have hh := Nat.mod_add_div j 2; omega⟩
    have hc := congrArg (fun Q : (integralRationals p)[X] => Q.coeff j) hP
    rw [WPActualEvenLogCarry.coeff_comp_neg, ho.neg_one_pow, mul_neg_one] at hc
    have hcv := congrArg (fun a : integralRationals p => a.val) hc
    change -(P.coeff j).val=(P.coeff j).val at hcv
    change (0 : ℚ)=(P.coeff j).val
    linarith

/-- The canonical rational lift for the fifth-point entropy first difference. -/
noncomputable def actualFifthCarryIntegral (p : ℕ) [Fact p.Prime] : integralRationals p :=
  (contract 2 (fifthCarryPolynomial p)).eval (smallIntegralInverse p 5)+
    (entropyCarryIntegral p).eval (121*(smallIntegralInverse p 5)^3)-
    11*smallIntegralInverse p 5*
      ((entropyCarryIntegral p).eval (4*smallIntegralInverse p 5)-
        (entropyCarryIntegral p).eval (smallIntegralInverse p 5))

section ActualCharacteristicZeroEndpoint

variable {K : Type*} [Field K] [CharZero K]

/-- Return the exact entropy identity to the original moving log with its literal C. -/
theorem actual_fifth_moving_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (u : K) (hu : u^2=(1/5 : K)) :
    ((movingEvenQ p).map (algebraMap ℚ K)).eval ((-(11/5 : K)*u)^2)=
      (11/5 : K)*(((movingEvenQ p).map (algebraMap ℚ K)).eval ((2*u)^2)-
        ((movingEvenQ p).map (algebraMap ℚ K)).eval (u^2))-
      (16/5 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)+
      (3/2 : K)*(WPFiniteInversion.integerFermatQuotient p 5 : K)+
      (p : K)*((actualFifthCarryIntegral p).val : K) := by
  let φ : integralRationals p →+* K :=
    (algebraMap ℚ K).comp (integralRationals p).subtype
  have h5 : φ (smallIntegralInverse p 5)=(1/5 : K) :=
    smallInverse_charZero p 5 (by omega) (by omega)
  have hcore : φ ((contract 2 (fifthCarryPolynomial p)).eval (smallIntegralInverse p 5))=
      fifthCarryValue p u := by
    have h := congrArg (fun P : (integralRationals p)[X] => (P.map φ).eval u)
      (integral_even_square_pullback p (fifthCarryPolynomial p)
        (fifthCarryPolynomial_even p hp))
    simp only [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X,
      eval_comp, eval_pow, eval_X] at h
    rw [hu, fifthCarryPolynomial_charZero_eval p hp u] at h
    rw [←eval_map_apply, h5, h]
  have hpoint₀ : (-(11/5 : K)*u)^2=121*(1/5 : K)^3 := by
    rw [mul_pow, hu]
    ring
  have hpoint₂ : (2*u)^2=4*(1/5 : K) := by rw [mul_pow, hu]; ring
  have hI : φ (actualFifthCarryIntegral p)=fifthCarryValue p u+
      ((entropyCarryIntegral p).map φ).eval ((-(11/5 : K)*u)^2)-
      (11/5 : K)*(((entropyCarryIntegral p).map φ).eval ((2*u)^2)-
        ((entropyCarryIntegral p).map φ).eval (u^2)) := by
    rw [actualFifthCarryIntegral, map_sub, map_add, map_mul, map_mul,
      map_ofNat, h5, hcore, map_sub, ←eval_map_apply, ←eval_map_apply, ←eval_map_apply]
    simp only [map_mul, map_ofNat, map_pow, h5]
    rw [hpoint₀, hpoint₂, hu]
    ring
  have h₀ := entropy_charZero_evaluation_carry p hp (-(11/5 : K)*u)
  have h₁ := entropy_charZero_evaluation_carry p hp u
  have h₂ := entropy_charZero_evaluation_carry p hp (2*u)
  have hF := actual_fifth_entropy_firstTaylor p hp u hu
  change φ (actualFifthCarryIntegral p)=_ at hI
  change ((movingEvenQ p).map (algebraMap ℚ K)).eval ((-(11/5 : K)*u)^2)=
    (11/5 : K)*(((movingEvenQ p).map (algebraMap ℚ K)).eval ((2*u)^2)-
      ((movingEvenQ p).map (algebraMap ℚ K)).eval (u^2))-
    (16/5 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)+
    (3/2 : K)*(WPFiniteInversion.integerFermatQuotient p 5 : K)+
    (p : K)*φ (actualFifthCarryIntegral p)
  linear_combination h₀+hF-(11/5 : K)*h₂+(11/5 : K)*h₁-(p : K)*hI

end ActualCharacteristicZeroEndpoint

/-- The unchanged literal fifth-point constant in SB101--102. -/
noncomputable def literalFifthConstantQ (p : ℕ) : ℚ :=
  (movingEvenQ p).eval (4/5)-(movingEvenQ p).eval (1/5)

/-- The original rational first difference, formed before the residue map. -/
noncomputable def actualFifthFirstDifferenceQ (p : ℕ) : ℚ :=
  ((movingEvenQ p).eval (121/125)-(11/5 : ℚ)*literalFifthConstantQ p+
    (16/5 : ℚ)*(WPFiniteInversion.integerFermatQuotient p 2 : ℚ)-
    (3/2 : ℚ)*(WPFiniteInversion.integerFermatQuotient p 5 : ℚ))/(p : ℚ)

/-- The canonical integral carry has the actual rational p-divided value. -/
theorem actualFifthCarryIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualFifthCarryIntegral p).val=actualFifthFirstDifferenceQ p := by
  let u : ℝ := Real.sqrt (1/5 : ℝ)
  have hu : u^2=(1/5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hpoint₀ : (-(11/5 : ℝ)*u)^2=(121/125 : ℝ) := by rw [mul_pow, hu]; ring
  have hpoint₂ : (2*u)^2=(4/5 : ℝ) := by rw [mul_pow, hu]; ring
  have h₀ := eval_map_apply (p := movingEvenQ p) (algebraMap ℚ ℝ) (121/125 : ℚ)
  have h₁ := eval_map_apply (p := movingEvenQ p) (algebraMap ℚ ℝ) (1/5 : ℚ)
  have h₂ := eval_map_apply (p := movingEvenQ p) (algebraMap ℚ ℝ) (4/5 : ℚ)
  norm_num only [map_div₀, map_ofNat, map_one] at h₀ h₁ h₂
  have he := actual_fifth_moving_firstTaylor p hp u hu
  rw [hpoint₀, hpoint₂, hu, h₀, h₂, h₁] at he
  have hQ : (movingEvenQ p).eval (121/125)=
      (11/5 : ℚ)*literalFifthConstantQ p-
      (16/5 : ℚ)*(WPFiniteInversion.integerFermatQuotient p 2 : ℚ)+
      (3/2 : ℚ)*(WPFiniteInversion.integerFermatQuotient p 5 : ℚ)+
      (p : ℚ)*(actualFifthCarryIntegral p).val := by
    unfold literalFifthConstantQ
    apply (algebraMap ℚ ℝ).injective
    simpa only [map_add, map_sub, map_mul, map_div₀, map_ofNat, map_intCast,
      map_natCast, eq_ratCast] using he
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold actualFifthFirstDifferenceQ
  apply (eq_div_iff hp0).2
  linear_combination -hQ

section CharacteristicP

variable {K : Type*} [Field K]

theorem entropyIntegral_base_change_eval (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (((entropyIntegral p).map (residueHom p)).map
      (ZMod.castHom (dvd_refl p) K)).eval (u^2)=WPFiniteField.E p u := by
  have hm : (entropyIntegral p).map (residueHom p)=
      (WPFiniteLVSource.evenSquared p : (ZMod p)[X]) := by
    rw [entropyIntegral, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
      map_natCast, ZMod.natCast_self, C_0, zero_mul, sub_zero,
      movingEvenIntegral_actual_field p hp]
  rw [hm]
  have hs : (WPFiniteLVSource.evenSquared p : (ZMod p)[X]).map
      (ZMod.castHom (dvd_refl p) K)=(WPFiniteLVSource.evenSquared p : K[X]) := by
    simp only [WPFiniteLVSource.evenSquared, Polynomial.map_sum, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      map_div₀, map_one, map_mul, map_ofNat, map_natCast]
  rw [hs]
  have he := congrArg (fun P : K[X] => P.eval u)
    (WPFiniteLVSource.evenSquared_square p hp)
  simp only [eval_comp, eval_pow, eval_X] at he
  rw [he]
  simp only [WPFiniteKSource.EP, eval_mul, eval_C, eval_add, eval_comp, eval_neg,
    eval_X, WPFiniteAffineLog.LP_eval_eq, WPFiniteField.E, div_eq_mul_inv]
  ring

private theorem smallInverse_power_field (p a : ℕ) [Fact p.Prime]
    (ha : 0 < a) (hap : a < p) :
    residueHom p ((smallIntegralInverse p a)^(p-1))=1 := by
  rw [map_pow, smallIntegralInverse_field p a ha hap]
  apply ZMod.pow_card_sub_one_eq_one
  exact inv_ne_zero (WPActualGaussProper.small_cast_ne_zero p a ha hap)

/-- The field expression of the actual SB102f carry; its sources are literal finite functions. -/
noncomputable def actualFifthCarryField (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K :=
  let q₂ : K := WPFiniteInversion.integerFermatQuotient p 2
  let q₅ : K := WPFiniteInversion.integerFermatQuotient p 5
  let E := WPFiniteField.E p u
  let C := WPFiniteField.E p (2*u)-E
  let H := q₅/2-(4/5 : K)*q₂;
  -(22/5 : K)*q₂^2+(47/10 : K)*q₂*q₅-(3/2 : K)*q₅^2+
    (q₂+4*q₅)*C/5-(11/5 : K)*q₂*E-
    (33/8 : K)*E^2+(33/4 : K)*E*H+(11/4 : K)*E*C-
    (45/8 : K)*H^2-(35/4 : K)*H*C-(9/8 : K)*C^2+
    WPFiniteNC122.Aeven p (-(11/5 : K)*u)-
    (11/5 : K)*(WPFiniteNC122.Aeven p (2*u)-WPFiniteNC122.Aeven p u)

/-- The cubic's whole contracted carry has the finite linear and quadratic digits. -/
theorem fifth_core_carry_field (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u^2=(1/5 : K)) :
    (ZMod.castHom (dvd_refl p) K) (residueHom p
      ((contract 2 (fifthCarryPolynomial p)).eval (smallIntegralInverse p 5)))=
    let q₂ : K := WPFiniteInversion.integerFermatQuotient p 2
    let q₅ : K := WPFiniteInversion.integerFermatQuotient p 5
    let E := WPFiniteField.E p u
    let C := WPFiniteField.E p (2*u)-E
    let H := q₅/2-(4/5 : K)*q₂;
    -(22/5 : K)*q₂^2+(47/10 : K)*q₂*q₅-(3/2 : K)*q₅^2+
      (q₂+4*q₅)*C/5-(11/5 : K)*q₂*E-
      (33/8 : K)*E^2+(33/4 : K)*E*H+(11/4 : K)*E*C-
      (45/8 : K)*H^2-(35/4 : K)*H*C-(9/8 : K)*C^2 := by
  let φ : integralRationals p →+* K :=
    (ZMod.castHom (dvd_refl p) K).comp (residueHom p)
  let q₂ : K := WPFiniteInversion.integerFermatQuotient p 2
  let q₅ : K := WPFiniteInversion.integerFermatQuotient p 5
  let E := WPFiniteField.E p u
  let C := WPFiniteField.E p (2*u)-E
  let H := q₅/2-(4/5 : K)*q₂
  let r := u^p
  have h2 : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h5p : (5 : K)^p=5 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 5
  have hr : r^2=(1/5 : K) := by
    change (u^p)^2=_
    rw [←pow_mul, Nat.mul_comm p 2, pow_mul, hu, one_div_pow, h5p]
  have hr0 : r ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hr
    exact (one_div_ne_zero h5) hr.symm
  have hn₁ := WPFifthEntropy.fifth_norm_equation p hp u hu
  have hn₂ := WPFifthEntropy.double_fifth_norm_equation p hp u hu
  have hO₁ : WPFiniteField.O p u=(H-E)/r := by
    apply (eq_div_iff hr0).2
    linear_combination hn₁
  have hO₂ : WPFiniteField.O p (2*u)=(H-E-C)/(2*r) := by
    apply (eq_div_iff (mul_ne_zero h2 hr0)).2
    linear_combination hn₂
  have hs₂ : φ (smallIntegralInverse p 2)=(1/2 : K) := by
    rw [RingHom.comp_apply, smallIntegralInverse_field p 2 (by omega) (by omega)]
    simp only [map_inv₀, Nat.cast_ofNat, map_ofNat, one_div]
  have hs₅ : φ (smallIntegralInverse p 5)=(1/5 : K) := by
    rw [RingHom.comp_apply, smallIntegralInverse_field p 5 (by omega) (by omega)]
    simp only [map_inv₀, Nat.cast_ofNat, map_ofNat, one_div]
  have hiU : φ ((smallIntegralInverse p 2)^(p-1))=1 := by
    rw [RingHom.comp_apply, smallInverse_power_field p 2 (by omega) (by omega), map_one]
  have hiW : φ ((smallIntegralInverse p 5)^(p-1))=1 := by
    rw [RingHom.comp_apply, smallInverse_power_field p 5 (by omega) (by omega), map_one]
  have hU : φ ((2 : integralRationals p)^(p-1))=1 := by
    have hz : residueHom p ((2 : integralRationals p)^(p-1))=1 := by
      rw [map_pow, map_ofNat]
      apply ZMod.pow_card_sub_one_eq_one
      exact WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
    rw [RingHom.comp_apply, hz, map_one]
  have hp0 : φ (p : integralRationals p)=0 := by
    rw [RingHom.comp_apply, map_natCast, ZMod.natCast_self, map_zero]
  rw [map_pow, hs₂] at hiU
  rw [map_pow, hs₅] at hiW
  rw [map_pow, map_ofNat] at hU
  rw [map_natCast] at hp0
  have hJ : φ (fifthNormIntegral p)=H := by
    rw [RingHom.comp_apply, fifthNormIntegral_field p hp]
    simp only [map_sub, map_div₀, map_mul, map_ofNat, map_intCast, H, q₂, q₅]
  have hJ₁ : φ (fifthNormFirstIntegral p)=-(2/5 : K)*q₂^2-q₅*H := by
    rw [RingHom.comp_apply, fifthNormFirstIntegral_field p hp]
    simp only [map_sub, map_neg, map_div₀, map_mul, map_pow, map_ofNat, map_intCast,
      H, q₂, q₅]
  have hE₁ : ((entropyIntegral p).map φ).eval (u^2)=E := by
    rw [←Polynomial.map_map]
    exact entropyIntegral_base_change_eval p hp u
  have hE₂ : ((entropyIntegral p).map φ).eval (4*u^2)=E+C := by
    rw [show 4*u^2=(2*u)^2 by ring, ←Polynomial.map_map,
      entropyIntegral_base_change_eval p hp]
    dsimp only [C, E]
    ring
  have hO₁e : ((oddEntropyIntegral p).map φ).eval u=WPFiniteField.O p u := by
    rw [←Polynomial.map_map]
    exact oddEntropyIntegral_base_change_eval p hp u
  have hO₂e : ((oddEntropyIntegral p).map φ).eval (2*u)=WPFiniteField.O p (2*u) := by
    rw [←Polynomial.map_map]
    exact oddEntropyIntegral_base_change_eval p hp (2*u)
  have hcore : φ ((contract 2 (fifthCarryPolynomial p)).eval (smallIntegralInverse p 5))=
      ((fifthCarryPolynomial p).map φ).eval u := by
    have h := congrArg (fun P : (integralRationals p)[X] => (P.map φ).eval u)
      (integral_even_square_pullback p (fifthCarryPolynomial p)
        (fifthCarryPolynomial_even p hp))
    simp only [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X,
      eval_comp, eval_pow, eval_X] at h
    rw [hu] at h
    rw [←eval_map_apply, hs₅, h]
  change φ ((contract 2 (fifthCarryPolynomial p)).eval (smallIntegralInverse p 5))=_
  rw [hcore]
  simp only [fifthCarryPolynomial, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_comp, Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat,
    Polynomial.map_natCast, Polynomial.map_intCast, eval_add, eval_sub,
    eval_neg, eval_mul, eval_C, eval_pow, eval_comp, eval_X, eval_ofNat,
    eval_natCast, eval_intCast, eval_one,
    map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, map_natCast, map_intCast,
    hE₁, hE₂, hO₁e, hO₂e, hs₂, hs₅, hiU, hiW, hU, hp0, hJ, hJ₁,
    zero_mul, add_zero, mul_one]
  rw [hO₁,hO₂]
  have hlin := fifth_linear_digit h2 h5 q₂ q₅ E C H rfl
  have hquad := fifth_quadratic_digit h2 h5 r E C H hr
  have hsum := congrArg₂ (fun a b : K => a+b) hlin hquad
  unfold quadraticCorrection at hsum
  dsimp only [r, q₂, q₅, E, C, H] at hsum ⊢
  convert hsum using 1 <;> field_simp [h2, h5, hr0] <;> ring

/-- Reduce the canonical literal fifth-point carry only after its rational construction. -/
theorem actualFifthCarryIntegral_field (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u^2=(1/5 : K)) :
    (ZMod.castHom (dvd_refl p) K) (residueHom p (actualFifthCarryIntegral p))=
      actualFifthCarryField p u := by
  let φ : integralRationals p →+* K :=
    (ZMod.castHom (dvd_refl p) K).comp (residueHom p)
  have h5 : φ (smallIntegralInverse p 5)=(1/5 : K) := by
    rw [RingHom.comp_apply, smallIntegralInverse_field p 5 (by omega) (by omega)]
    simp only [map_inv₀, Nat.cast_ofNat, map_ofNat, one_div]
  have hpoint₂ : (2*u)^2=φ (4*smallIntegralInverse p 5) := by
    rw [map_mul, map_ofNat, h5, mul_pow, hu]
    ring
  have hpoint₀ : (-(11/5 : K)*u)^2=φ (121*(smallIntegralInverse p 5)^3) := by
    rw [map_mul, map_ofNat, map_pow, h5, mul_pow, hu]
    ring
  have h₁ := actual_entropy_carry_square_point p hp (smallIntegralInverse p 5) u
    (hu.trans h5.symm)
  have h₂ := actual_entropy_carry_square_point p hp (4*smallIntegralInverse p 5) (2*u) hpoint₂
  have h₀ := actual_entropy_carry_square_point p hp
    (121*(smallIntegralInverse p 5)^3) (-(11/5 : K)*u) hpoint₀
  change φ ((entropyCarryIntegral p).eval (smallIntegralInverse p 5))=_ at h₁
  change φ ((entropyCarryIntegral p).eval (4*smallIntegralInverse p 5))=_ at h₂
  change φ ((entropyCarryIntegral p).eval (121*(smallIntegralInverse p 5)^3))=_ at h₀
  have hcore := fifth_core_carry_field p hp u hu
  change φ ((contract 2 (fifthCarryPolynomial p)).eval (smallIntegralInverse p 5))=_ at hcore
  change φ (actualFifthCarryIntegral p)=_
  rw [actualFifthCarryIntegral, map_sub, map_add, map_mul, map_mul, map_ofNat,
    h5, map_sub, hcore, h₀, h₂, h₁]
  unfold actualFifthCarryField
  dsimp only
  ring

end CharacteristicP

end WPFieldAssembly.ActualEntropyFifth
