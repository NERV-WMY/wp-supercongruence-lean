import WPActualCentralResidueSource

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource
  WPActualEtaPole WPActualEtaSupport WPActualEtaPrimitive
  WPActualPositiveResidueSource WPActualChiSource WPActualCentralResidueSource
  WPActualResidueVanishing

namespace WPFirstResidue.LogarithmicHResidue

/-- For a nonpositive Laurent source, division lowers its entire upper bound to -1. -/
theorem monomialQuotient_nonpositive (a : ℚ) (n lo : ℤ)
    (_hl : lo ≤ 0) (hnl : lo ≤ n) (hn : n ≤ 0) :
    bounded (monomialQuotient a n) lo (-1) := by
  cases n with
  | ofNat n =>
    change (n : ℤ) ≤ 0 at hn
    have hn0 : n = 0 := by omega
    subst n
    exact bounded_zero _ _
  | negSucc n =>
    unfold monomialQuotient
    apply bounded_mono (bounded_mul
      (bounded_mul (bounded_neg (bounded_C _)) (bounded_T _))
      (forwardQuotient_bounded a (n + 1))) <;> omega

theorem dividedDifference_nonpositive (a : ℚ) (P : ℚ[T;T⁻¹]) (lo : ℤ)
    (hl : lo ≤ 0) (hP : bounded P lo 0) :
    bounded (dividedDifference a P) lo (-1) := by
  classical
  change bounded (Finsupp.linearCombination ℚ (monomialQuotient a) P.coeff) lo (-1)
  rw [Finsupp.linearCombination_apply]
  apply bounded_sum
  intro j hj
  change bounded (P.coeff j • monomialQuotient a j) lo (-1)
  rw [smul_eq_C_mul]
  have hjs := hP j (Finsupp.mem_support_iff.mp hj)
  exact bounded_mono (bounded_mul (bounded_C _)
    (monomialQuotient_nonpositive a j lo hl hjs.1 hjs.2)) (by omega) (by omega)

/-- Finite Laurent form of the residue theorem, with the endpoint explicitly retained. -/
theorem dividedDifference_residue_nonpositive (a : ℚ) (ha : a ≠ 0)
    (P : ℚ[T;T⁻¹]) (lo : ℤ) (hl : lo ≤ 0) (hP : bounded P lo 0) :
    (dividedDifference a P).coeff (-1) = P.coeff 0 - evaluate a ha P := by
  have hbound := dividedDifference_nonpositive a P lo hl hP
  have hzero : (dividedDifference a P).coeff 0 = 0 := by
    by_contra hz
    have h := (hbound 0 hz).2
    omega
  have h := congrArg (fun R : ℚ[T;T⁻¹] => R.coeff 0)
    (dividedDifference_identity a ha P)
  rw [sub_mul] at h
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    constant_mul_coefficient, hzero, mul_zero, sub_zero] at h
  rw [mul_comm (T 1), monomial_shift_coefficient] at h
  simpa using h

theorem Hpull_Q_nonpositive (e : ℕ) : bounded (Hpull e Qx) (-3 * (e : ℤ)) 0 := by
  rw [Hpull_expansion]
  apply bounded_sum
  intro n hn
  have hne := Finset.mem_range.mp hn
  exact bounded_mono (bounded_mul (bounded_C _) (bounded_pow Qx_bounded n))
    (by omega) (by omega)

theorem Hpull_reciprocal (e : ℕ) : invert (HX e) = Hpull e Qx := by
  change invert (substituteOver _ Vx) = substituteOver _ Qx
  rw [substituteOver_invert, actual_Vx_reciprocal]

theorem Hpull_Q_constant (e : ℕ) :
    (Hpull e Qx).coeff 0 = (Hpolynomial e).eval (4 / 125) := by
  rw [← Hpull_reciprocal, invert_apply]
  simpa using actual_HX_constant e

theorem Hpull_Q_endpoints (e : ℕ) :
    evaluate (1 / 4) (by norm_num) (Hpull e Qx) = 0 ∧
      evaluate 4 (by norm_num) (Hpull e Qx) = 0 := by
  constructor <;> rw [Hpull, evaluate_substitute, evaluate_Qx]
  · norm_num [Hpolynomial_zero]
  · norm_num [Hpolynomial_zero]

/-- Exact NC58 logarithmic term over Q; reduction does not invoke a global-residue axiom. -/
theorem actual_HQ_dlogV_residue (e : ℕ) :
    (weightedDifference (Hpull e Qx)).coeff (-1) =
      3 * (Hpolynomial e).eval (4 / 125) := by
  have hP := Hpull_Q_nonpositive e
  have hends := Hpull_Q_endpoints e
  rw [weightedDifference_apply]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, constant_mul_coefficient]
  rw [dividedDifference_residue_nonpositive (1 / 4) (by norm_num) _ _
    (by omega) hP, dividedDifference_residue_nonpositive 4 (by norm_num) _ _
    (by omega) hP, hends.1, hends.2, Hpull_Q_constant]
  ring

end WPFirstResidue.LogarithmicHResidue
