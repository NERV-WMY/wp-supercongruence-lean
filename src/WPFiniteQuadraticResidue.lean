import WPFiniteLaurentEndpoint

open scoped LaurentSeries BigOperators
open HahnSeries Polynomial

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 1500000
set_option maxRecDepth 3000

variable {K : Type*} [Field K]

def finiteQuadraticPolynomial (m l : K) : K[X] :=
  X^2-Polynomial.C (2*m)*X+Polynomial.C l

def finiteQuadraticSeries (m l : K) : PowerSeries K :=
  (finiteQuadraticPolynomial m l : PowerSeries K)

def finiteQuadraticInverse (m l : K) : PowerSeries K :=
  (finiteQuadraticSeries m l)⁻¹

theorem finite_quadratic_constant (m l : K) :
    PowerSeries.constantCoeff (finiteQuadraticSeries m l) = l := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    finiteQuadraticSeries, Polynomial.coeff_coe]
  norm_num [finiteQuadraticPolynomial]

theorem finite_quadratic_coefficient (m l : K) (n : ℕ) :
    PowerSeries.coeff n (finiteQuadraticSeries m l) =
      (if n=2 then 1 else 0)-(2*m)*(if n=1 then 1 else 0)+
        (if n=0 then l else 0) := by
  simp only [finiteQuadraticSeries, finiteQuadraticPolynomial, Polynomial.coeff_coe,
    Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  simp only [eq_comm]

theorem finite_quadratic_inverse_zero (m l : K) :
    PowerSeries.coeff 0 (finiteQuadraticInverse m l) = l⁻¹ := by
  rw [finiteQuadraticInverse, PowerSeries.coeff_inv, if_pos rfl,
    finite_quadratic_constant]

theorem finite_quadratic_inverse_one (m l : K) :
    PowerSeries.coeff 1 (finiteQuadraticInverse m l) = 2*m*(l⁻¹)^2 := by
  change PowerSeries.coeff 1 (finiteQuadraticSeries m l)⁻¹ = _
  have hi0 : PowerSeries.coeff 0 (finiteQuadraticSeries m l)⁻¹ = l⁻¹ :=
    finite_quadratic_inverse_zero m l
  rw [PowerSeries.coeff_inv, if_neg (by decide),
    finite_quadratic_constant]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    finite_quadratic_coefficient, hi0]
  ring

theorem finite_quadratic_inverse_two (m l : K) :
    PowerSeries.coeff 2 (finiteQuadraticInverse m l) =
      4*m^2*(l⁻¹)^3-(l⁻¹)^2 := by
  change PowerSeries.coeff 2 (finiteQuadraticSeries m l)⁻¹ = _
  have hi0 : PowerSeries.coeff 0 (finiteQuadraticSeries m l)⁻¹ = l⁻¹ :=
    finite_quadratic_inverse_zero m l
  have hi1 : PowerSeries.coeff 1 (finiteQuadraticSeries m l)⁻¹ = 2*m*(l⁻¹)^2 :=
    finite_quadratic_inverse_one m l
  rw [PowerSeries.coeff_inv, if_neg (by decide),
    finite_quadratic_constant]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    finite_quadratic_coefficient, hi0, hi1]
  ring

/-- The inverse is integral coefficient by coefficient over any coefficient subring. -/
theorem finite_quadratic_inverse_integral (R : Subring K) (m l : K)
    (hm : m ∈ R) (hl : l ∈ R) (hli : l⁻¹ ∈ R) :
    ∀ n, PowerSeries.coeff n (finiteQuadraticInverse m l) ∈ R := by
  have hF : ∀ n, PowerSeries.coeff n (finiteQuadraticSeries m l) ∈ R := by
    intro n
    rw [finite_quadratic_coefficient]
    split_ifs <;> repeat' first
      | exact R.zero_mem
      | exact R.one_mem
      | exact hm
      | exact hl
      | exact natCast_mem R _
      | apply R.add_mem
      | apply R.sub_mem
      | apply R.mul_mem
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [finiteQuadraticInverse, PowerSeries.coeff_inv, finite_quadratic_constant]
    split_ifs with hn
    · exact hli
    · apply R.mul_mem (R.neg_mem hli)
      apply R.sum_mem
      intro a _ha
      split_ifs with ha
      · exact R.mul_mem (hF a.1) (ih a.2 ha)
      · exact R.zero_mem

/-- The actual rational inverse agrees with the inverse of the regular quadratic series. -/
theorem finite_quadratic_inverse_laurent (m l : K) (hl : l≠0) :
    algebraMap (RatFunc K) (LaurentSeries K)
      ((algebraMap K[X] (RatFunc K) (finiteQuadraticPolynomial m l))⁻¹) =
      (finiteQuadraticInverse m l : LaurentSeries K) := by
  have hprod := congrArg (fun F : PowerSeries K => (F : LaurentSeries K))
    (PowerSeries.mul_inv_cancel (finiteQuadraticSeries m l)
      (by simpa only [finite_quadratic_constant] using hl))
  simp only [PowerSeries.coe_mul, PowerSeries.coe_one] at hprod
  change (finiteQuadraticSeries m l : LaurentSeries K)*
    (finiteQuadraticInverse m l : LaurentSeries K)=1 at hprod
  rw [finiteQuadraticSeries, RatFunc.coe_coe] at hprod
  simp only [RatFunc.coePolynomial] at hprod
  rw [map_inv₀]
  have hn : algebraMap (RatFunc K) (LaurentSeries K)
      (algebraMap K[X] (RatFunc K) (finiteQuadraticPolynomial m l)) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hprod
    exact zero_ne_one hprod
  apply mul_left_cancel₀ hn
  rw [mul_inv_cancel₀ hn, hprod]

/-- Laurent residue selects the inverse coefficient and vanishes in the nonnegative chamber. -/
theorem finite_quadratic_power_residue (a b : ℕ) (m l : RatFunc ℚ) (hl : l≠0) :
    rationalResidue
      (bivS^a/(bivS^b*
        algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (finiteQuadraticPolynomial m l))) =
      if a<b then PowerSeries.coeff (b-a-1) (finiteQuadraticInverse m l) else 0 := by
  rw [div_mul_eq_div_div, rationalResidue, laurentResidue, map_div₀,
    actual_laurent_power_quotient, div_eq_mul_inv,
    ← map_inv₀, finite_quadratic_inverse_laurent m l hl,
    coeff_single_mul, one_mul, PowerSeries.coeff_coe]
  by_cases hab : a<b
  · have hi : ¬(-1-((a : ℤ)-(b : ℤ))<0) := by omega
    have hn : Int.natAbs (-1-((a : ℤ)-(b : ℤ)))=b-a-1 := by omega
    rw [if_neg hi, hn, if_pos hab]
  · have hi : -1-((a : ℤ)-(b : ℤ))<0 := by omega
    rw [if_pos hi, if_neg hab]

end

end WPForcedSourceStokes
