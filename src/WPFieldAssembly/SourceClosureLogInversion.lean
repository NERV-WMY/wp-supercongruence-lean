import WPFieldAssembly.SourceClosureUniversalLog

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.SourceClosureUniversalLog

namespace WPFieldAssembly.SourceClosureLogInversion

/- STATEMENT_FIDELITY: whole full-cutoff Laurent identities, obtained by
   the literal j -> p-j reversal. These identities retain the signed
   Frobenius shift and do not substitute evaluation at a finite field. -/

variable {K : Type*} [Field K]

theorem scaledLog_invert (p : ℕ) [Fact p.Prime] [CharP K p]
    (c : K) (hc : c≠0) :
    invert (scaledLog p c) =
      -LaurentPolynomial.C (c^p)*T (-(p : ℤ))*scaledLog p c⁻¹ := by
  rw [scaledLog_full,scaledLog_full]
  simp only [map_sum,map_mul,invert_C,invert_T]
  rw [←WPFiniteInversion.full_cutoff_reflection p
    (fun j => LaurentPolynomial.C (c^j/(j : K))*T (-(j : ℤ))),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjp := Nat.le_of_lt (Finset.mem_Ico.mp hj).2
  have hcoeff : c^(p-j)/((p-j : ℕ) : K) = -(c^p)*((c⁻¹)^j/(j : K)) := by
    rw [WPFiniteField.reflected_denominator p j hj,pow_sub₀ c hc hjp]
    simp only [div_eq_mul_inv,inv_neg,inv_pow]
    ring
  have hexp : -((p-j : ℕ) : ℤ)=-(p : ℤ)+(j : ℤ) := by
    rw [Nat.cast_sub hjp]
    omega
  rw [hcoeff,hexp,T_add]
  simp only [map_mul,map_neg]
  ring

theorem scaledDilog_invert (p : ℕ) [Fact p.Prime] [CharP K p]
    (c : K) (hc : c≠0) :
    invert (scaledDilog p c) =
      LaurentPolynomial.C (c^p)*T (-(p : ℤ))*scaledDilog p c⁻¹ := by
  rw [scaledDilog_full,scaledDilog_full]
  simp only [map_sum,map_mul,invert_C,invert_T]
  rw [←WPFiniteInversion.full_cutoff_reflection p
    (fun j => LaurentPolynomial.C (c^j/(j : K)^2)*T (-(j : ℤ))),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjp := Nat.le_of_lt (Finset.mem_Ico.mp hj).2
  have hcoeff : c^(p-j)/((p-j : ℕ) : K)^2 = c^p*((c⁻¹)^j/(j : K)^2) := by
    rw [WPFiniteField.reflected_denominator p j hj,pow_sub₀ c hc hjp]
    simp only [even_two.neg_pow,div_eq_mul_inv,inv_pow]
    ring
  have hexp : -((p-j : ℕ) : ℤ)=-(p : ℤ)+(j : ℤ) := by
    rw [Nat.cast_sub hjp]
    omega
  rw [hcoeff,hexp,T_add]
  simp only [map_mul]
  ring

theorem originalJlog_invert (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    invert (originalJlog p : K[T;T⁻¹])=-originalJlog p := by
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have ha : (1/4 : K)≠0 := div_ne_zero one_ne_zero h4
  have h4p : (4 : K)^p=4 := WPFiniteField.natCast_pow_char p 4
  have hap : (1/4 : K)^p=1/4 := by rw [div_pow,one_pow,h4p]
  have htp : (T (p : ℤ)*T (-(p : ℤ)) : K[T;T⁻¹])=1 := by
    rw [←T_add,add_neg_cancel,T_zero]
  have hca : LaurentPolynomial.C (1/4 : K)*LaurentPolynomial.C (4 : K)=1 := by
    rw [←map_mul,one_div_mul_cancel h4,map_one]
  simp only [originalJlog,map_mul,map_sub,invert_C,invert_T,neg_neg,
    scaledLog_invert p 4 h4,scaledLog_invert p (1/4) ha,h4p,hap,
    show (4 : K)⁻¹=1/4 by simp only [one_div],
    show (1/4 : K)⁻¹=4 by simp only [one_div,inv_inv]]
  linear_combination
    LaurentPolynomial.C (2/15 : K)*
      (LaurentPolynomial.C (1/4 : K)*scaledLog p 4-
        LaurentPolynomial.C (4 : K)*scaledLog p (1/4))*htp+
    LaurentPolynomial.C (2/15 : K)*T (-(p : ℤ))*
      (scaledLog p (1/4)-scaledLog p 4)*hca

theorem originalJ2log_invert (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    invert (originalJ2log p : K[T;T⁻¹])=originalJ2log p := by
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have ha : (1/4 : K)≠0 := div_ne_zero one_ne_zero h4
  have h4p : (4 : K)^p=4 := WPFiniteField.natCast_pow_char p 4
  have hap : (1/4 : K)^p=1/4 := by rw [div_pow,one_pow,h4p]
  have htp : (T (p : ℤ)*T (-(p : ℤ)) : K[T;T⁻¹])=1 := by
    rw [←T_add,add_neg_cancel,T_zero]
  have hca : LaurentPolynomial.C (1/4 : K)*LaurentPolynomial.C (4 : K)=1 := by
    rw [←map_mul,one_div_mul_cancel h4,map_one]
  simp only [originalJ2log,map_mul,map_sub,invert_C,invert_T,neg_neg,
    scaledDilog_invert p 4 h4,scaledDilog_invert p (1/4) ha,h4p,hap,
    show (4 : K)⁻¹=1/4 by simp only [one_div],
    show (1/4 : K)⁻¹=4 by simp only [one_div,inv_inv]]
  linear_combination
    LaurentPolynomial.C (2/15 : K)*
      (LaurentPolynomial.C (4 : K)*scaledDilog p (1/4)-
        LaurentPolynomial.C (1/4 : K)*scaledDilog p 4)*htp+
    LaurentPolynomial.C (2/15 : K)*T (-(p : ℤ))*
      (scaledDilog p 4-scaledDilog p (1/4))*hca

end WPFieldAssembly.SourceClosureLogInversion
