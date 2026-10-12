import WPActualChiSource
import WPActualEtaPrimitive

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPActualChiSource WPActualEtaPole WPActualEtaPrimitive
  WPActualEtaSupport WPActualNativeHasse WPActualPullbackSource WPPIntegralReduction

namespace WPActualEtaIntegrality

/-- The actual integral coefficient subring of finite Laurent polynomials. -/
def integralLaurent (p : ℕ) [Fact p.Prime] : Subring ℚ[T;T⁻¹] where
  carrier := {P | ∀ j, P.coeff j ∈ integralRationals p}
  zero_mem' := by intro j; exact (integralRationals p).zero_mem
  one_mem' := by
    intro j
    rw [show (1 : ℚ[T;T⁻¹]) = C 1 * T 0 by simp, finite_monomial_coeff]
    split_ifs
    · exact (integralRationals p).one_mem
    · exact (integralRationals p).zero_mem
  add_mem' := by
    intro P Q hP hQ j
    rw [AddMonoidAlgebra.coeff_add]
    exact (integralRationals p).add_mem (hP j) (hQ j)
  neg_mem' := by
    intro P hP j
    rw [AddMonoidAlgebra.coeff_neg]
    exact (integralRationals p).neg_mem (hP j)
  mul_mem' := by
    intro P Q hP hQ j
    rw [AddMonoidAlgebra.coeff_mul]
    apply (integralRationals p).sum_mem
    intro a _
    apply (integralRationals p).sum_mem
    intro b _
    change (if a + b = j then P.coeff a * Q.coeff b else 0) ∈ integralRationals p
    split_ifs
    · exact (integralRationals p).mul_mem (hP a) (hQ b)
    · exact (integralRationals p).zero_mem

theorem integralLaurent_iff (p : ℕ) [Fact p.Prime] (P : ℚ[T;T⁻¹]) :
    P ∈ integralLaurent p ↔ ∀ j, 0 ≤ padicValRat p (P.coeff j) := Iff.rfl

theorem integral_C (p : ℕ) [Fact p.Prime] (c : ℚ) (hc : 0 ≤ padicValRat p c) :
    C c ∈ integralLaurent p := by
  intro j
  rw [show C c = C c * T 0 by simp, finite_monomial_coeff]
  split_ifs
  · exact hc
  · exact (integralRationals p).zero_mem

theorem integral_T (p : ℕ) [Fact p.Prime] (j : ℤ) : T j ∈ integralLaurent p := by
  intro k
  rw [show (T j : ℚ[T;T⁻¹]) = C 1 * T j by simp, finite_monomial_coeff]
  split_ifs <;> simp

theorem coefficientMap_subtype_integral (p : ℕ) [Fact p.Prime]
    (P : (integralRationals p)[T;T⁻¹]) :
    coefficientMap (integralRationals p).subtype P ∈ integralLaurent p := by
  intro j
  rw [coefficientMap_coeff]
  exact (P.coeff j).property

theorem integral_Vx (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) : Vx ∈ integralLaurent p := by
  have h := coefficientMap_subtype_integral p
    (Polynomial.toLaurent (WPHasseIntegralTransport.integralV p hp))
  rw [coefficientMap_toLaurent, WPHasseIntegralTransport.integralV_map_rational] at h
  exact h

theorem integral_zpow (p : ℕ) [Fact p.Prime] (a : ℚ)
    (ha : a ∈ integralRationals p) (hai : a⁻¹ ∈ integralRationals p) (j : ℤ) :
    a ^ j ∈ integralRationals p := by
  cases j with
  | ofNat n => exact (integralRationals p).pow_mem ha n
  | negSucc n =>
    simpa only [zpow_negSucc, ← inv_pow] using (integralRationals p).pow_mem hai (n + 1)

theorem forwardQuotient_integral (p : ℕ) [Fact p.Prime] (a : ℚ)
    (ha : a ∈ integralRationals p) (n : ℕ) : forwardQuotient a n ∈ integralLaurent p := by
  induction n with
  | zero => exact (integralLaurent p).zero_mem
  | succ n ih =>
    exact (integralLaurent p).add_mem (integral_T p n)
      ((integralLaurent p).mul_mem (integral_C p a ha) ih)

theorem monomialQuotient_integral (p : ℕ) [Fact p.Prime] (a : ℚ)
    (ha : a ∈ integralRationals p) (hai : a⁻¹ ∈ integralRationals p) (j : ℤ) :
    monomialQuotient a j ∈ integralLaurent p := by
  cases j with
  | ofNat n => exact forwardQuotient_integral p a ha n
  | negSucc n =>
    exact (integralLaurent p).mul_mem
      ((integralLaurent p).mul_mem
        ((integralLaurent p).neg_mem (integral_C p _ (integral_zpow p a ha hai _)))
        (integral_T p _)) (forwardQuotient_integral p a ha (n + 1))

theorem dividedDifference_integral (p : ℕ) [Fact p.Prime] (a : ℚ)
    (ha : a ∈ integralRationals p) (hai : a⁻¹ ∈ integralRationals p)
    (P : ℚ[T;T⁻¹]) (hP : P ∈ integralLaurent p) :
    dividedDifference a P ∈ integralLaurent p := by
  classical
  change Finsupp.linearCombination ℚ (monomialQuotient a) P.coeff ∈ integralLaurent p
  rw [Finsupp.linearCombination_apply]
  apply (integralLaurent p).sum_mem
  intro j _
  change P.coeff j • monomialQuotient a j ∈ integralLaurent p
  rw [smul_eq_C_mul]
  exact (integralLaurent p).mul_mem (integral_C p _ (hP j))
    (monomialQuotient_integral p a ha hai j)

theorem native_Hcoefficient_integral (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    0 ≤ padicValRat p (WPReview.nativeCoefficient n / (n : ℚ)) := by
  by_cases hz : n = 0
  · subst n; simp
  · have hi := WPFiniteConductorPolynomial.small_inverse_integral p n (by omega) hn
    change 0 ≤ padicValRat p (1 / (n : ℚ)) at hi
    have hinv : (n : ℚ)⁻¹ ∈ integralRationals p := by
      change 0 ≤ padicValRat p (n : ℚ)⁻¹
      simpa only [one_div] using hi
    exact (integralRationals p).mul_mem (actual_native_coefficient_integral p n hp hn)
      hinv

theorem actual_HX_integral (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) : HX e ∈ integralLaurent p := by
  rw [HX, Hpull_expansion]
  apply (integralLaurent p).sum_mem
  intro n hn
  exact (integralLaurent p).mul_mem
    (integral_C p _ (native_Hcoefficient_integral p n hp (by
      have := Finset.mem_range.mp hn; omega)))
    ((integralLaurent p).pow_mem (integral_Vx p hp) n)

theorem actual_AX_integral (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hd : p / 6 ≤ e) :
    AX p ((p - 1) / 2) e ∈ integralLaurent p := by
  exact (integralLaurent p).add_mem (actual_chiX_integral p e hp he hd)
    (actual_HX_integral p e hp he)

theorem actual_Peta_integral (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hd : p / 6 ≤ e) :
    Peta p ((p - 1) / 2) e ∈ integralLaurent p := by
  let R := integralRationals p
  let L := integralLaurent p
  have hhalf : (1 / 2 : ℚ) ∈ R :=
    WPFiniteConductorPolynomial.small_inverse_integral p 2 (by norm_num) (by omega)
  have hquarter : (1 / 4 : ℚ) ∈ R := by
    simpa only [show (1 / 2 : ℚ) ^ 2 = 1 / 4 by norm_num] using R.pow_mem hhalf 2
  have h4 : (4 : ℚ) ∈ R := natCast_mem R 4
  have h2 : (2 : ℚ) ∈ R := natCast_mem R 2
  have hinvquarter : (1 / 4 : ℚ)⁻¹ ∈ R := by simpa only [show (1 / 4 : ℚ)⁻¹ = 4 by norm_num] using h4
  have hinv4 : (4 : ℚ)⁻¹ ∈ R := by simpa only [show (4 : ℚ)⁻¹ = 1 / 4 by norm_num] using hquarter
  have hA := actual_AX_integral p e hp he hd
  exact L.sub_mem
    (L.add_mem (L.mul_mem (integral_C p 2 h2)
      (dividedDifference_integral p (1 / 4) hquarter hinvquarter _ hA))
      (dividedDifference_integral p 4 h4 hinv4 _ hA))
    (L.mul_mem (L.mul_mem (integral_C p (1 / 2) hhalf)
      (actual_HX_integral p e hp he)) (integral_T p (-1)))

theorem canonicalPrimitive_integral (p : ℕ) [Fact p.Prime]
    (P : ℚ[T;T⁻¹]) (hP : P ∈ integralLaurent p) :
    canonicalPrimitive p P ∈ integralLaurent p := by
  intro k
  rw [canonicalPrimitive_coeff]
  by_cases hd : (p : ℤ) ∣ k
  · rw [if_pos hd]; exact (integralRationals p).zero_mem
  · rw [if_neg hd]
    have hi : (k : ℚ)⁻¹ ∈ integralRationals p := by
      change 0 ≤ padicValRat p (k : ℚ)⁻¹
      rw [padicValRat.inv, integer_denominator_unit p k hd]
      simp
    exact (integralRationals p).mul_mem (hP (k - 1)) hi

/-- The actual whole canonical primitive is integral, with every resonant slot fixed to zero. -/
theorem actual_Aeta_integral (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hd : p / 6 ≤ e) (j : ℤ) :
    0 ≤ padicValRat p ((Aeta p ((p - 1) / 2) e).coeff j) := by
  exact canonicalPrimitive_integral p _ (actual_Peta_integral p e hp he hd) j

theorem actual_native_cutoff_Aeta_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (j : ℤ) :
    0 ≤ padicValRat p ((Aeta p ((p - 1) / 2) (p - 1 - p / 6)).coeff j) := by
  apply actual_Aeta_integral p _ (by omega) (by omega) _ j
  have hdiv := Nat.div_mul_le_self p 6
  omega

end WPActualEtaIntegrality
