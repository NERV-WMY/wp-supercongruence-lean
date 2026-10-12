import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.Tactic

open Polynomial

namespace WPForcedSourceStokes

noncomputable section

variable {K : Type*} [Field K]

/-- Literal polynomial quotient of the reduced numerator and monic denominator. -/
noncomputable def rationalPolynomialPart (f : RatFunc K) : K[X] := f.num /ₘ f.denom

theorem monic_quotient_cancel_right (P D Q : K[X]) (hD : D.Monic) (hQ : Q.Monic) :
    (P * Q) /ₘ (D * Q) = P /ₘ D := by
  apply (div_modByMonic_unique (P /ₘ D) ((P %ₘ D) * Q) (hD.mul hQ) ?_).1
  constructor
  · have h := congrArg (fun F : K[X] => F * Q) (modByMonic_add_div P D)
    linear_combination h
  · rw [degree_mul, degree_mul]
    exact WithBot.add_lt_add_of_lt_of_le (degree_ne_bot.mpr hQ.ne_zero)
      (degree_modByMonic_lt P hD) le_rfl

theorem monic_quotient_scalar (P Q : K[X]) (hQ : Q.Monic) (a : K) :
    (C a * P) /ₘ Q = C a * (P /ₘ Q) := by
  apply (div_modByMonic_unique (C a * (P /ₘ Q)) (C a * (P %ₘ Q)) hQ ?_).1
  constructor
  · have h := congrArg (fun F : K[X] => C a * F) (modByMonic_add_div P Q)
    linear_combination h
  · rw [← smul_eq_C_mul]
    exact (degree_smul_le a (P %ₘ Q)).trans_lt (degree_modByMonic_lt P hQ)

theorem monic_quotient_add (P R Q : K[X]) (hQ : Q.Monic) :
    (P + R) /ₘ Q = P /ₘ Q + R /ₘ Q := by
  apply (div_modByMonic_unique (P /ₘ Q + R /ₘ Q) (P %ₘ Q + R %ₘ Q) hQ ?_).1
  constructor
  · linear_combination (modByMonic_add_div P Q) + (modByMonic_add_div R Q)
  · exact (degree_add_le _ _).trans_lt
      (max_lt (degree_modByMonic_lt P hQ) (degree_modByMonic_lt R hQ))

theorem rationalPolynomialPart_monic_fraction (P Q : K[X]) (hQ : Q.Monic) :
    rationalPolynomialPart (algebraMap K[X] (RatFunc K) P /
      algebraMap K[X] (RatFunc K) Q) = P /ₘ Q := by
  let f : RatFunc K := algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q
  have hc : f.num * Q = P * f.denom := (RatFunc.num_mul_eq_mul_denom_iff hQ.ne_zero).mpr rfl
  change f.num /ₘ f.denom = _
  rw [← monic_quotient_cancel_right f.num f.denom Q (RatFunc.monic_denom f) hQ,
    hc, mul_comm f.denom Q,
    monic_quotient_cancel_right P Q f.denom hQ (RatFunc.monic_denom f)]

theorem rationalPolynomialPart_fraction (P Q : K[X]) (hQ : Q ≠ 0) :
    rationalPolynomialPart (algebraMap K[X] (RatFunc K) P /
      algebraMap K[X] (RatFunc K) Q) = P / Q := by
  have hl : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  have hCi : RatFunc.C (Q.leadingCoeff : K) ≠ (0 : RatFunc K) := by
    intro h
    have h' : RatFunc.C (Q.leadingCoeff : K) = RatFunc.C (0 : K) := by simpa using h
    exact hl (RatFunc.C_injective h')
  have hCinv : RatFunc.C (Q.leadingCoeff⁻¹ : K) ≠ (0 : RatFunc K) := by
    simpa only [map_inv₀] using inv_ne_zero hCi
  let Qn : K[X] := Q * C Q.leadingCoeff⁻¹
  have hm : Qn.Monic := monic_mul_leadingCoeff_inv hQ
  have hfrac : algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q =
      algebraMap K[X] (RatFunc K) (C Q.leadingCoeff⁻¹ * P) /
        algebraMap K[X] (RatFunc K) Qn := by
    dsimp [Qn]
    simp only [map_mul, RatFunc.algebraMap_C]
    field_simp [RatFunc.algebraMap_ne_zero hQ, hCi, hCinv]
  rw [hfrac, rationalPolynomialPart_monic_fraction _ _ hm,
    monic_quotient_scalar _ _ hm, Polynomial.div_def]

theorem rationalPolynomialPart_polynomial (P : K[X]) :
    rationalPolynomialPart (algebraMap K[X] (RatFunc K) P) = P := by
  simpa using rationalPolynomialPart_fraction P 1 one_ne_zero

theorem rationalPolynomialPart_add (f g : RatFunc K) :
    rationalPolynomialPart (f + g) = rationalPolynomialPart f + rationalPolynomialPart g := by
  let D : K[X] := f.denom * g.denom
  have hD : D.Monic := (RatFunc.monic_denom f).mul (RatFunc.monic_denom g)
  have hsum : f + g = algebraMap K[X] (RatFunc K)
      (f.num * g.denom + g.num * f.denom) / algebraMap K[X] (RatFunc K) D := by
    conv_lhs => rw [← RatFunc.num_div_denom f, ← RatFunc.num_div_denom g]
    dsimp [D]
    simp only [map_add, map_mul]
    field_simp [RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f),
      RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero g)]
  rw [hsum, rationalPolynomialPart_monic_fraction _ _ hD, monic_quotient_add _ _ _ hD]
  dsimp [D, rationalPolynomialPart]
  rw [monic_quotient_cancel_right _ _ _ (RatFunc.monic_denom f) (RatFunc.monic_denom g),
    mul_comm f.denom g.denom,
    monic_quotient_cancel_right _ _ _ (RatFunc.monic_denom g) (RatFunc.monic_denom f)]

theorem rationalPolynomialPart_scalar (a : K) (f : RatFunc K) :
    rationalPolynomialPart (RatFunc.C a * f) = C a * rationalPolynomialPart f := by
  have hf : RatFunc.C a * f = algebraMap K[X] (RatFunc K) (C a * f.num) /
      algebraMap K[X] (RatFunc K) f.denom := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    simp only [map_mul, RatFunc.algebraMap_C]
    ring
  rw [hf, rationalPolynomialPart_monic_fraction _ _ (RatFunc.monic_denom f),
    monic_quotient_scalar _ _ (RatFunc.monic_denom f)]
  rfl

/-- Every polynomial-plus-proper-fraction expression has this exact polynomial part. -/
theorem rationalPolynomialPart_of_polynomial_add_proper
    (P R Q : K[X]) (hQ : Q ≠ 0) (hproper : R.degree < Q.degree) :
    rationalPolynomialPart (algebraMap K[X] (RatFunc K) P +
      algebraMap K[X] (RatFunc K) R / algebraMap K[X] (RatFunc K) Q) = P := by
  rw [rationalPolynomialPart_add, rationalPolynomialPart_polynomial,
    rationalPolynomialPart_fraction _ _ hQ,
    (Polynomial.div_eq_zero_iff hQ).mpr hproper, add_zero]

theorem rationalPolynomialPart_sum {ι : Type*} (s : Finset ι) (f : ι → RatFunc K) :
    rationalPolynomialPart (∑ i ∈ s, f i) = ∑ i ∈ s, rationalPolynomialPart (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rationalPolynomialPart, RatFunc.num_zero]
  | @insert i s hi ih => simp [hi, rationalPolynomialPart_add, ih]

theorem monic_quotient_coeff_mem (R : Subring K) (P Q : K[X])
    (hP : ∀ k, P.coeff k ∈ R) (hQ : ∀ k, Q.coeff k ∈ R) (hm : Q.Monic) (k : ℕ) :
    (P /ₘ Q).coeff k ∈ R := by
  have hp : P ∈ (mapRingHom R.subtype).range := (mem_map_range R.subtype).mpr (by
    intro k
    exact ⟨⟨P.coeff k, hP k⟩, rfl⟩)
  have hq : Q ∈ (mapRingHom R.subtype).range := (mem_map_range R.subtype).mpr (by
    intro k
    exact ⟨⟨Q.coeff k, hQ k⟩, rfl⟩)
  obtain ⟨P', hp⟩ := hp
  obtain ⟨Q', hq⟩ := hq
  change P'.map R.subtype = P at hp
  change Q'.map R.subtype = Q at hq
  have hm' : Q'.Monic := (Function.Injective.monic_map_iff Subtype.val_injective).mpr
    (hq.symm ▸ hm)
  have hmap : (P' /ₘ Q').map R.subtype = P /ₘ Q := by
    rw [map_divByMonic R.subtype hm', hp, hq]
  rw [← hmap, coeff_map]
  exact (P' /ₘ Q').coeff k |>.property

theorem ordinary_quotient_coeff_mem (R : Subring K) (P Q : K[X]) (hQ : Q ≠ 0)
    (hP : ∀ k, P.coeff k ∈ R) (hQc : ∀ k, Q.coeff k ∈ R)
    (hunit : Q.leadingCoeff⁻¹ ∈ R) (k : ℕ) : (P / Q).coeff k ∈ R := by
  rw [Polynomial.div_def, coeff_C_mul]
  apply R.mul_mem hunit
  apply monic_quotient_coeff_mem R P _ hP _ (monic_mul_leadingCoeff_inv hQ) k
  intro j
  rw [coeff_mul_C]
  exact R.mul_mem (hQc j) hunit

theorem ordinary_quotient_natDegree (P Q : K[X]) (hQ : Q ≠ 0) :
    (P / Q).natDegree = P.natDegree - Q.natDegree := by
  rw [Polynomial.div_def, natDegree_C_mul (inv_ne_zero (leadingCoeff_ne_zero.mpr hQ)),
    natDegree_divByMonic P (monic_mul_leadingCoeff_inv hQ),
    natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hQ))]

theorem rationalPolynomialPart_fraction_coeff_zero (P Q : K[X]) (hQ : Q ≠ 0)
    (k : ℕ) (hk : 0 < k) (hdeg : P.natDegree < k + Q.natDegree) :
    (rationalPolynomialPart (algebraMap K[X] (RatFunc K) P /
      algebraMap K[X] (RatFunc K) Q)).coeff k = 0 := by
  rw [rationalPolynomialPart_fraction _ _ hQ]
  apply coeff_eq_zero_of_natDegree_lt
  rw [ordinary_quotient_natDegree _ _ hQ]
  omega

/-- The extractor is precisely the unique polynomial quotient, with a proper remainder. -/
theorem rationalPolynomialPart_decomposition (f : RatFunc K) :
    f = algebraMap K[X] (RatFunc K) (rationalPolynomialPart f) +
      algebraMap K[X] (RatFunc K) (f.num %ₘ f.denom) /
        algebraMap K[X] (RatFunc K) f.denom ∧
      (f.num %ₘ f.denom).degree < f.denom.degree := by
  constructor
  · conv_lhs => rw [← RatFunc.num_div_denom f]
    have h := congrArg (algebraMap K[X] (RatFunc K)) (modByMonic_add_div f.num f.denom)
    simp only [map_add, map_mul] at h
    dsimp [rationalPolynomialPart]
    field_simp [RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)]
    linear_combination -h
  · exact degree_modByMonic_lt _ (RatFunc.monic_denom f)

end

end WPForcedSourceStokes
