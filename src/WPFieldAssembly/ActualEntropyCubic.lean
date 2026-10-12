import WPFieldAssembly.ActualEntropyPolynomial

open Polynomial WPPIntegralReduction WPActualRankTwoHatLift
  WPFieldAssembly.ActualEntropyPolynomial

namespace WPFieldAssembly.ActualEntropyCubic

set_option maxHeartbeats 1200000

variable {K : Type*} [Field K] [CharZero K]

/-- The literal rational entropy is evaluated before any reduction. -/
noncomputable def evenPower (p : ℕ) (z : K) : K :=
  (2 - (1-z)^p - (1+z)^p)/(2*(p : K))

noncomputable def oddPower (p : ℕ) (z : K) : K :=
  ((1+z)^p - (1-z)^p - 2*z^p)/(2*(p : K))

theorem actual_evenPower (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (z : K) :
    ((entropySumQ p).map (algebraMap ℚ K)).eval (z^2) = evenPower p z := by
  have h := congrArg (fun P : ℚ[X] => (P.map (algebraMap ℚ K)).eval z)
    (actual_entropy_square_pullback p hp)
  simpa only [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X,
    eval_comp, eval_pow, eval_X, entropyPowerQ, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_sub, Polynomial.map_ofNat,
    Polynomial.map_one, Polynomial.map_add, eval_mul, eval_C, eval_sub,
    eval_ofNat, eval_one, eval_add, map_div₀, map_one, map_mul,
    map_ofNat, map_natCast, map_inv₀, one_mul, evenPower, div_eq_mul_inv, mul_comm] using h

theorem literal_entropy_split (p : ℕ) (hp : 0 < p) (z : K) :
    (1+z)^p = 1+z^p-(p : K)*evenPower p z+(p : K)*oddPower p z ∧
    (1-z)^p = 1-z^p-(p : K)*evenPower p z-(p : K)*oddPower p z := by
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  constructor <;> unfold evenPower oddPower <;> field_simp [hp0] <;> ring

/-- The quadratic norm keeps its whole correction, rather than only its field digit. -/
theorem literal_entropy_norm (p : ℕ) (hp : 0 < p) (z : K) :
    2*(p : K)*(evenPower p z + z^p*oddPower p z) =
      1-(z^p)^2-(1-z^2)^p +
        (p : K)^2*((evenPower p z)^2-(oddPower p z)^2) := by
  obtain ⟨ha, hb⟩ := literal_entropy_split p hp z
  have hm : (1-z)^p*(1+z)^p = (1-z^2)^p := by
    rw [←mul_pow, show (1-z)*(1+z) = 1-z^2 by ring]
  rw [ha, hb] at hm
  linear_combination -hm

noncomputable def quadraticCorrection (r s E₁ E₂ O₁ O₂ : K) : K :=
  -E₂^2-O₂^2-2*E₁*E₂+2*s*E₁*O₂+2*O₁*O₂-2*r*E₂*O₂-2*s*E₂*O₁

noncomputable def cubicCorrection (E₁ E₂ O₁ O₂ : K) : K :=
  E₁*(E₂^2+O₂^2)-2*E₂*O₁*O₂

/-- Exact cubic product identity, retaining the p and p² corrections. -/
theorem literal_entropy_cubic (p : ℕ) (hp : 0 < p) (z w T : K)
    (hminus : 1-T=(1-z)*(1+w)^2) (hplus : 1+T=(1+z)*(1-w)^2) :
    evenPower p T = (2*z^p*w^p-(w^p)^2)/(p : K) +
      evenPower p z*(1+(w^p)^2) + 2*evenPower p w*(1-z^p*w^p) +
      2*(z^p-w^p)*oddPower p w + 2*w^p*oddPower p z +
      (p : K)*quadraticCorrection (z^p) (w^p) (evenPower p z)
        (evenPower p w) (oddPower p z) (oddPower p w) +
      (p : K)^2*cubicCorrection (evenPower p z) (evenPower p w)
        (oddPower p z) (oddPower p w) := by
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  obtain ⟨ha, hb⟩ := literal_entropy_split p hp z
  obtain ⟨hc, hd⟩ := literal_entropy_split p hp w
  have hpw : ((1+w)^2)^p=((1+w)^p)^2 := by
    rw [←pow_mul, ←pow_mul, Nat.mul_comm 2 p]
  have hpm : ((1-w)^2)^p=((1-w)^p)^2 := by
    rw [←pow_mul, ←pow_mul, Nat.mul_comm 2 p]
  have hT : 2*(p : K)*evenPower p T =
      2-(1-z)^p*((1+w)^p)^2-(1+z)^p*((1-w)^p)^2 := by
    unfold evenPower
    simp only [hminus, hplus, mul_pow, hpw, hpm]
    field_simp [hp0]
  rw [ha, hb, hc, hd] at hT
  apply mul_left_cancel₀ (by exact_mod_cast (by omega : 2*p ≠ 0) :
    (2*(p : K)) ≠ 0)
  unfold quadraticCorrection cubicCorrection
  field_simp [hp0]
  linear_combination (1/2 : K)*hT

theorem actual_fifth_factorizations (u : K) (hu : u^2=(1/5 : K)) :
    1-(-(11/5 : K)*u)=(1-u)*(1+2*u)^2 ∧
    1+(-(11/5 : K)*u)=(1+u)*(1-2*u)^2 := by
  constructor
  · linear_combination (4*u) * hu
  · linear_combination -(4*u) * hu

/-- Both signs of the rational quadratic point use the same whole entropy identity. -/
theorem actual_fifth_cubic (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (u : K) (hu : u^2=(1/5 : K)) :
    evenPower p (-(11/5 : K)*u) =
      (2*u^p*(2*u)^p-((2*u)^p)^2)/(p : K) +
      evenPower p u*(1+((2*u)^p)^2) +
      2*evenPower p (2*u)*(1-u^p*(2*u)^p) +
      2*(u^p-(2*u)^p)*oddPower p (2*u) + 2*(2*u)^p*oddPower p u +
      (p : K)*quadraticCorrection (u^p) ((2*u)^p) (evenPower p u)
        (evenPower p (2*u)) (oddPower p u) (oddPower p (2*u)) +
      (p : K)^2*cubicCorrection (evenPower p u) (evenPower p (2*u))
        (oddPower p u) (oddPower p (2*u)) := by
  obtain ⟨hm, hp'⟩ := actual_fifth_factorizations u hu
  exact literal_entropy_cubic p (by omega) u (2*u) (-(11/5 : K)*u) hm hp'

noncomputable def fifthNormQ (p : ℕ) : ℚ :=
  ((5 : ℚ)^p-1-(4 : ℚ)^p)/(2*(p : ℚ)*(5 : ℚ)^p)

private theorem fifthNormQ_source (p : ℕ) (hp : 0 < p) :
    2*(p : K)*(fifthNormQ p : K) =
      1-(1/5 : K)^p-(4/5 : K)^p := by
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  unfold fifthNormQ
  push_cast
  rw [div_pow, div_pow, one_pow]
  field_simp [hp0]

theorem actual_fifth_norm_pair (p : ℕ) (hp : 0 < p)
    (u : K) (hu : u^2=(1/5 : K)) :
    evenPower p u+u^p*oddPower p u = (fifthNormQ p : K) +
      (p : K)/2*((evenPower p u)^2-(oddPower p u)^2) ∧
    evenPower p (2*u)+(2*u)^p*oddPower p (2*u) = (fifthNormQ p : K) +
      (p : K)/2*((evenPower p (2*u))^2-(oddPower p (2*u))^2) := by
  have hp0 : (2*(p : K)) ≠ 0 := by exact_mod_cast (by omega : 2*p ≠ 0)
  have hs : (u^p)^2=(1/5 : K)^p := by
    rw [←pow_mul, Nat.mul_comm p 2, pow_mul, hu]
  have hu2 : (2*u)^2=(4/5 : K) := by rw [mul_pow, hu]; ring
  have hs2 : ((2*u)^p)^2=(4/5 : K)^p := by
    rw [←pow_mul, Nat.mul_comm p 2, pow_mul, hu2]
  have h1 := literal_entropy_norm p hp u
  have h2 := literal_entropy_norm p hp (2*u)
  rw [hs, hu, show (1-(1/5 : K))=4/5 by ring] at h1
  rw [hs2, hu2, show (1-(4/5 : K))=1/5 by ring] at h2
  have hJ := fifthNormQ_source (K := K) p hp
  constructor
  · apply mul_left_cancel₀ hp0
    linear_combination h1-hJ
  · apply mul_left_cancel₀ hp0
    linear_combination h2-hJ

/-- The common norm has its original integer Fermat quotients before division. -/
theorem fifthNormQ_literal (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    fifthNormQ p =
      (5*(WPFiniteInversion.integerFermatQuotient p 5 : ℚ) -
        8*(WPFiniteInversion.integerFermatQuotient p 2 : ℚ) -
        4*(p : ℚ)*(WPFiniteInversion.integerFermatQuotient p 2 : ℚ)^2)/
      (10*(1+(p : ℚ)*(WPFiniteInversion.integerFermatQuotient p 5 : ℚ))) := by
  have h2unit : (2 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h5unit : (5 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h2q : (WPFiniteInversion.integerFermatQuotient p 2 : ℚ)*(p : ℚ) =
      (2 : ℚ)^(p-1)-1 := by
    exact_mod_cast WPFiniteInversion.integerFermatQuotient_mul p 2 (by simpa using h2unit)
  have h5q : (WPFiniteInversion.integerFermatQuotient p 5 : ℚ)*(p : ℚ) =
      (5 : ℚ)^(p-1)-1 := by
    exact_mod_cast WPFiniteInversion.integerFermatQuotient_mul p 5 (by simpa using h5unit)
  have h2pow : (2 : ℚ)^p = 2*(1+(p : ℚ)*
      (WPFiniteInversion.integerFermatQuotient p 2 : ℚ)) := by
    calc
      _ = (2 : ℚ)^(p-1)*2 := by
        rw [←pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
      _ = _ := by linear_combination -2*h2q
  have h5pow : (5 : ℚ)^p = 5*(1+(p : ℚ)*
      (WPFiniteInversion.integerFermatQuotient p 5 : ℚ)) := by
    calc
      _ = (5 : ℚ)^(p-1)*5 := by
        rw [←pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
      _ = _ := by linear_combination -5*h5q
  have h4pow : (4 : ℚ)^p = 4*(1+(p : ℚ)*
      (WPFiniteInversion.integerFermatQuotient p 2 : ℚ))^2 := by
    calc
      _ = ((2 : ℚ)^p)^2 := by
        rw [show (4 : ℚ)=2^2 by norm_num, ←pow_mul, ←pow_mul,
          Nat.mul_comm 2 p]
      _ = _ := by rw [h2pow]; ring
  have h5den : 1+(p : ℚ)*(WPFiniteInversion.integerFermatQuotient p 5 : ℚ) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h5pow
    exact (pow_ne_zero p (by norm_num : (5 : ℚ) ≠ 0)) h5pow
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold fifthNormQ
  rw [h4pow, h5pow]
  field_simp [hp0, h5den]
  ring

/-- Exact first-order unit expansions used before the literal p-division. -/
theorem fifth_unit_coefficients (P q₂ q₅ : K)
    (hU : 1+P*q₂ ≠ 0) (hW : 1+P*q₅ ≠ 0) :
    (4-4*(1+P*q₂)/(5*(1+P*q₅))-1/(1+P*q₂) =
      (11/5 : K)+P*(q₂/(1+P*q₂)-(4/5 : K)*(q₂-q₅)/(1+P*q₅))) ∧
    (1+4*(1+P*q₂)^2/(5*(1+P*q₅))-4*(1+P*q₂) =
      -(11/5 : K)+P*((4/5 : K)*(2*q₂-q₅+P*q₂^2)/(1+P*q₅)-4*q₂)) ∧
    ((5*q₅-8*q₂-4*P*q₂^2)/(10*(1+P*q₅)) =
      q₅/2-(4/5 : K)*q₂+P*(-(2/5 : K)*q₂^2/(1+P*q₅)-
        q₅*(q₅/2-(4/5 : K)*q₂)/(1+P*q₅))) ∧
    (1/(1+P*q₂)-2+4*(1+P*q₂)=3+P*(4*q₂-q₂/(1+P*q₂))) ∧
    (-4*(1+P*q₂)*q₂/(5*(1+P*q₅))=
      -(4/5 : K)*q₂+P*(-(4/5 : K)*q₂*(q₂-q₅)/(1+P*q₅))) := by
  have hU' : 1+q₂*P ≠ 0 := by simpa only [mul_comm] using hU
  have hW' : 1+q₅*P ≠ 0 := by simpa only [mul_comm] using hW
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp [hU, hW, hU', hW'] <;> ring

/-- Eliminate the two odd traces with their exact common norm, without choosing a Frobenius sign. -/
theorem norm_eliminated_expansion (P r U q J E₁ E₂ O₁ O₂ : K)
    (hP : P ≠ 0) (hU : U ≠ 0) (hpower : U=1+P*q)
    (hn₁ : E₁+r*O₁=J+P/2*(E₁^2-O₁^2))
    (hn₂ : E₂+(2*U*r)*O₂=J+P/2*(E₂^2-O₂^2)) :
    (2*r*(2*U*r)-(2*U*r)^2)/P + E₁*(1+(2*U*r)^2) +
      2*E₂*(1-r*(2*U*r))+2*(r-2*U*r)*O₂+2*(2*U*r)*O₁ +
      P*quadraticCorrection r (2*U*r) E₁ E₂ O₁ O₂ +
      P^2*cubicCorrection E₁ E₂ O₁ O₂ =
    -4*U*r^2*q + (4-4*U*r^2-1/U)*E₂ + (1+4*U^2*r^2-4*U)*E₁ +
      (1/U-2+4*U)*J +
      P*(quadraticCorrection r (2*U*r) E₁ E₂ O₁ O₂ +
        (1/(2*U)-1)*(E₂^2-O₂^2)+2*U*(E₁^2-O₁^2)) +
      P^2*cubicCorrection E₁ E₂ O₁ O₂ := by
  have hs : (2*r*(2*U*r)-(2*U*r)^2)/P = -4*U*r^2*q := by
    apply (div_eq_iff hP).2
    linear_combination -4*U*r^2*hpower
  have hO₁ : r*O₁=J-E₁+P/2*(E₁^2-O₁^2) := by linear_combination hn₁
  have hO₂ : (2*U*r)*O₂=J-E₂+P/2*(E₂^2-O₂^2) := by linear_combination hn₂
  have hl : E₁*(1+(2*U*r)^2)+2*E₂*(1-r*(2*U*r))+
      2*(r-2*U*r)*O₂+2*(2*U*r)*O₁ =
      (4-4*U*r^2-1/U)*E₂+(1+4*U^2*r^2-4*U)*E₁+(1/U-2+4*U)*J+
        P*((1/(2*U)-1)*(E₂^2-O₂^2)+2*U*(E₁^2-O₁^2)) := by
    calc
      _ = E₁*(1+(2*U*r)^2)+2*E₂*(1-r*(2*U*r))+
          (1/U-2)*((2*U*r)*O₂)+4*U*(r*O₁) := by
        field_simp [hU]
        ring
      _ = _ := by
        rw [hO₁, hO₂]
        field_simp [hU]
        ring
  rw [hs]
  linear_combination hl

/-- The actual Frobenius square is an original rational unit, before reduction. -/
theorem actual_fifth_frobenius_norm (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (u : K) (hu : u^2=(1/5 : K)) :
    (u^p)^2 = 1/(5*(1+(p : K)*
      (WPFiniteInversion.integerFermatQuotient p 5 : K))) := by
  have h5unit : (5 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have hq : (WPFiniteInversion.integerFermatQuotient p 5 : K)*(p : K) =
      (5 : K)^(p-1)-1 := by
    exact_mod_cast WPFiniteInversion.integerFermatQuotient_mul p 5 (by simpa using h5unit)
  have hpow : (5 : K)^p = 5*(1+(p : K)*
      (WPFiniteInversion.integerFermatQuotient p 5 : K)) := by
    calc
      _ = (5 : K)^(p-1)*5 := by
        rw [←pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
      _ = _ := by linear_combination -5*hq
  rw [←pow_mul, Nat.mul_comm p 2, pow_mul, hu, one_div_pow, hpow]

/-- The literal fifth-point cubic consumes both actual norm equations. -/
theorem actual_fifth_norm_eliminated (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (u : K) (hu : u^2=(1/5 : K)) :
    let U : K := (2 : K)^(p-1)
    let r : K := u^p
    evenPower p (-(11/5 : K)*u) =
      -4*U*r^2*(WPFiniteInversion.integerFermatQuotient p 2 : K) +
      (4-4*U*r^2-1/U)*evenPower p (2*u) +
      (1+4*U^2*r^2-4*U)*evenPower p u +
      (1/U-2+4*U)*(fifthNormQ p : K) +
      (p : K)*(quadraticCorrection r (2*U*r) (evenPower p u)
        (evenPower p (2*u)) (oddPower p u) (oddPower p (2*u)) +
        (1/(2*U)-1)*((evenPower p (2*u))^2-(oddPower p (2*u))^2) +
        2*U*((evenPower p u)^2-(oddPower p u)^2)) +
      (p : K)^2*cubicCorrection (evenPower p u) (evenPower p (2*u))
        (oddPower p u) (oddPower p (2*u)) := by
  dsimp only
  have h2unit : (2 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hq : (WPFiniteInversion.integerFermatQuotient p 2 : K)*(p : K) =
      (2 : K)^(p-1)-1 := by
    exact_mod_cast WPFiniteInversion.integerFermatQuotient_mul p 2 (by simpa using h2unit)
  have hU : (2 : K)^(p-1)=1+(p : K)*
      (WPFiniteInversion.integerFermatQuotient p 2 : K) := by
    linear_combination -hq
  have hs : (2*u)^p=2*(2 : K)^(p-1)*u^p := by
    rw [mul_pow]
    congr 1
    calc
      _ = (2 : K)^(p-1)*2 := by
        rw [←pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
      _ = _ := by ring
  have he := actual_fifth_cubic p hp u hu
  obtain ⟨hn₁, hn₂⟩ := actual_fifth_norm_pair p (by omega) u hu
  rw [hs] at he hn₂
  rw [he]
  exact norm_eliminated_expansion (p : K) (u^p) ((2 : K)^(p-1))
    (WPFiniteInversion.integerFermatQuotient p 2 : K) (fifthNormQ p : K)
    (evenPower p u) (evenPower p (2*u)) (oddPower p u) (oddPower p (2*u))
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    (pow_ne_zero _ (by norm_num)) hU hn₁ hn₂

noncomputable def fifthNormIntegral (p : ℕ) [Fact p.Prime] : integralRationals p :=
  (5*(WPFiniteInversion.integerFermatQuotient p 5 : integralRationals p) -
    8*(WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) -
    4*(p : integralRationals p)*
      (WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p)^2) *
    smallIntegralInverse p 2 * (smallIntegralInverse p 5)^p

/-- The p-divided norm is an actual integral rational lift. -/
theorem fifthNormIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fifthNormIntegral p).val = fifthNormQ p := by
  change (integralRationals p).subtype (fifthNormIntegral p) = _
  simp only [fifthNormIntegral, map_mul, map_sub, map_pow, map_ofNat,
    map_natCast, map_intCast, Subring.subtype_apply]
  rw [smallIntegralInverse_value p 2 (by omega) (by omega),
    smallIntegralInverse_value p 5 (by omega) (by omega)]
  have h5unit : (5 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have hq : (WPFiniteInversion.integerFermatQuotient p 5 : ℚ)*(p : ℚ) =
      (5 : ℚ)^(p-1)-1 := by
    exact_mod_cast WPFiniteInversion.integerFermatQuotient_mul p 5 (by simpa using h5unit)
  have hd : 10*(1+(p : ℚ)*(WPFiniteInversion.integerFermatQuotient p 5 : ℚ)) =
      2*(5 : ℚ)^p := by
    have hpow : (5 : ℚ)^p = (5 : ℚ)^(p-1)*5 := by
      rw [←pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    rw [hpow]
    linear_combination 10*hq
  rw [fifthNormQ_literal p hp, hd, one_div_pow]
  field_simp
  ring

theorem fifthNormIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (fifthNormIntegral p) =
      (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)/2 -
        (4/5 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
  simp only [fifthNormIntegral, map_mul, map_sub, map_pow, map_ofNat,
    map_natCast, map_intCast, ZMod.natCast_self, mul_zero, zero_mul, sub_zero]
  rw [smallIntegralInverse_field p 2 (by omega) (by omega),
    smallIntegralInverse_field p 5 (by omega) (by omega), ZMod.pow_card]
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  field_simp [h2, h5]
  ring

noncomputable def fifthNormLeadingIntegral (p : ℕ) [Fact p.Prime] : integralRationals p :=
  (WPFiniteInversion.integerFermatQuotient p 5 : integralRationals p)*smallIntegralInverse p 2 -
    4*(WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p)*smallIntegralInverse p 5

noncomputable def fifthNormFirstIntegral (p : ℕ) [Fact p.Prime] : integralRationals p :=
  (-2*(WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p)^2 -
    5*(WPFiniteInversion.integerFermatQuotient p 5 : integralRationals p)*
      fifthNormLeadingIntegral p)*(smallIntegralInverse p 5)^p

/-- The first norm carry is fixed by the original rational norm, before any field map. -/
theorem fifthNormIntegral_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    fifthNormIntegral p = fifthNormLeadingIntegral p +
      (p : integralRationals p)*fifthNormFirstIntegral p := by
  apply Subtype.ext
  change (fifthNormIntegral p).val =
    (integralRationals p).subtype (fifthNormLeadingIntegral p) +
      (p : ℚ)*(integralRationals p).subtype (fifthNormFirstIntegral p)
  rw [fifthNormIntegral_value p hp]
  simp only [fifthNormFirstIntegral, fifthNormLeadingIntegral,
    map_mul, map_sub, map_pow, map_neg, map_ofNat, map_intCast, Subring.subtype_apply]
  rw [smallIntegralInverse_value p 2 (by omega) (by omega),
    smallIntegralInverse_value p 5 (by omega) (by omega),
    fifthNormQ_literal p hp, one_div_pow]
  have h5unit : (5 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have hq : (WPFiniteInversion.integerFermatQuotient p 5 : ℚ)*(p : ℚ) =
      (5 : ℚ)^(p-1)-1 := by
    exact_mod_cast WPFiniteInversion.integerFermatQuotient_mul p 5 (by simpa using h5unit)
  have hpow : (5 : ℚ)^p =
      5*(1+(p : ℚ)*(WPFiniteInversion.integerFermatQuotient p 5 : ℚ)) := by
    calc
      _ = (5 : ℚ)^(p-1)*5 := by
        rw [←pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
      _ = _ := by linear_combination -5*hq
  have hden : 1+(p : ℚ)*(WPFiniteInversion.integerFermatQuotient p 5 : ℚ) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hpow
    exact (pow_ne_zero p (by norm_num : (5 : ℚ) ≠ 0)) hpow
  norm_num only [Nat.cast_ofNat]
  rw [hpow]
  have hden' : 1+(WPFiniteInversion.integerFermatQuotient p 5 : ℚ)*(p : ℚ) ≠ 0 := by
    simpa only [mul_comm] using hden
  field_simp [hden, hden']
  ring

theorem fifthNormFirstIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (fifthNormFirstIntegral p) =
      -(2/5 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2 -
        (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)*
          ((WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)/2 -
            (4/5 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)) := by
  simp only [fifthNormFirstIntegral, fifthNormLeadingIntegral,
    map_mul, map_sub, map_pow, map_neg, map_ofNat, map_intCast]
  rw [smallIntegralInverse_field p 2 (by omega) (by omega),
    smallIntegralInverse_field p 5 (by omega) (by omega), ZMod.pow_card]
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  field_simp [h2, h5]
  ring

/-- The actual unit coefficients contract to the linear first digit printed in SB102f. -/
theorem fifth_linear_digit {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0) (q₂ q₅ E C H : F)
    (hH : H=q₅/2-(4/5 : F)*q₂) :
    ((1/5 : F)*q₂+(4/5 : F)*q₅)*(E+C)+
      (-(12/5 : F)*q₂-(4/5 : F)*q₅)*E+
      3*(-(2/5 : F)*q₂^2-q₅*H)+3*q₂*H-(4/5 : F)*q₂*(q₂-q₅) =
    -(22/5 : F)*q₂^2+(47/10 : F)*q₂*q₅-(3/2 : F)*q₅^2+
      (q₂+4*q₅)*C/5-(11/5 : F)*q₂*E := by
  have h10 : (10 : F) ≠ 0 := by
    simpa only [show (10 : F)=2*5 by ring] using mul_ne_zero h2 h5
  rw [hH]
  field_simp [h2, h5, h10]
  ring

/-- The quadratic coefficient in SB102f is the whole norm correction. -/
theorem fifth_quadratic_digit {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0)
    (r E C H : F) (hr : r^2=(1/5 : F)) :
    quadraticCorrection r (2*r) E (E+C) ((H-E)/r) ((H-E-C)/(2*r)) -
        (1/2 : F)*((E+C)^2-((H-E-C)/(2*r))^2) +
        2*(E^2-((H-E)/r)^2) =
      -(33/8 : F)*E^2+(33/4 : F)*E*H+(11/4 : F)*E*C-
        (45/8 : F)*H^2-(35/4 : F)*H*C-(9/8 : F)*C^2 := by
  have hr0 : r ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by omega : (2 : ℕ) ≠ 0)] at hr
    exact (one_div_ne_zero h5) hr.symm
  have h4 : (4 : F) ≠ 0 := by
    simpa only [show (4 : F)=2^2 by ring] using pow_ne_zero 2 h2
  have h8 : (8 : F) ≠ 0 := by
    simpa only [show (8 : F)=2^3 by ring] using pow_ne_zero 3 h2
  unfold quadraticCorrection
  field_simp [hr0, h2, h4, h5, h8]
  ring_nf
  rw [hr]
  field_simp [h5]
  ring

end WPFieldAssembly.ActualEntropyCubic
