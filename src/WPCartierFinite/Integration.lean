import WPCartierFinite.SelectionRule
import WPCartierFinite.Derivatives
import WPCartierFinite.LiteralPolynomial
import WPCartierFinite.ScalarAlgebra
import WPCartierFinite.KernelTail
import WPCartierFinite.Vectors

namespace WPCartierFinite
noncomputable section
open scoped BigOperators

def IntegralCoefficients (p : ℕ) (P : LaurentPolynomial) : Prop :=
  ∀ x, pIntegral p (P.coeff x)

theorem pIntegral_valuation_nonnegative (p : ℕ) (q : ℚ) (hq : pIntegral p q) :
    0 ≤ padicValRat p q := by
  rw [padicValRat, padicValNat.eq_zero_of_not_dvd hq]
  simp

theorem rationalCongruent_zero_mul_pIntegral (p precision : ℕ) (hp : p.Prime)
    (a q : ℚ) (ha : WPReview.RationalCongruent p precision a 0) (hq : pIntegral p q) :
    WPReview.RationalCongruent p precision (a * q) 0 := by
  let : Fact p.Prime := ⟨hp⟩
  rcases ha with ha | ha
  · subst a
    exact Or.inl (by simp)
  · by_cases haz : a = 0
    · exact Or.inl (by simp [haz])
    by_cases hqz : q = 0
    · exact Or.inl (by simp [hqz])
    right
    rw [sub_zero, padicValRat.mul haz hqz]
    rw [sub_zero] at ha
    have hv := pIntegral_valuation_nonnegative p q hq
    omega

theorem integralCoefficients_one (p : ℕ) (hp : p.Prime) : IntegralCoefficients p 1 := by
  classical
  intro x
  by_cases hx : x = 0
  · subst x
    simpa using pIntegral_natCast p hp 1
  · simpa [AddMonoidAlgebra.one_def, Finsupp.single_apply, hx, Ne.symm hx] using
      pIntegral_natCast p hp 0

theorem integralCoefficients_mul (p : ℕ) (hp : p.Prime) {P Q : LaurentPolynomial}
    (hP : IntegralCoefficients p P) (hQ : IntegralCoefficients p Q) :
    IntegralCoefficients p (P * Q) := by
  classical
  intro x
  rw [AddMonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum]
  apply pIntegral_sum p hp
  intro a ha
  apply pIntegral_sum p hp
  intro b hb
  split_ifs
  · exact pIntegral_mul p hp (hP a) (hQ b)
  · exact pIntegral_natCast p hp 0

theorem integralCoefficients_pow (p : ℕ) (hp : p.Prime) {P : LaurentPolynomial}
    (hP : IntegralCoefficients p P) (n : ℕ) : IntegralCoefficients p (P ^ n) := by
  induction n with
  | zero => simpa using integralCoefficients_one p hp
  | succ n hn => simpa [pow_succ] using integralCoefficients_mul p hp hn hP

theorem canonicalCoefficients_integral (p : ℕ) (hp : p.Prime) (P : LaurentPolynomial)
    (hP : IntegralCoefficients p P) (a : Fin 6 → ℕ) :
    pIntegral p (canonicalCoefficients P a) := by
  classical
  by_cases ha : a ∈ Set.range canonicalSixNat
  · obtain ⟨x, rfl⟩ := ha
    rw [canonicalCoefficients_apply]
    exact hP x
  · rw [canonicalCoefficients, Finsupp.mapDomain_of_notMem_range P.coeff a ha]
    exact pIntegral_natCast p hp 0

theorem laurentMap_supportBound (P : OrdinaryPolynomial) :
    SupportBound (laurentMap P) P.totalDegree := by
  classical
  intro x hx
  have hnx := Finsupp.mem_support_iff.mp hx
  rw [laurentMap_coefficient] at hnx
  obtain ⟨b, hb, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnx
  have hbx : ordinaryExponent b = x := by
    by_contra hn
    simp [hn] at hv
  calc
    canonicalDegree x = canonicalDegree (qSix (fun i => (b i : ℤ))) := by
      rw [← hbx, ordinaryExponent_qSix]
    _ ≤ ∑ i, b i := canonicalDegree_le_ordinary _
    _ ≤ P.totalDegree := by simpa [Finsupp.sum_fintype] using MvPolynomial.le_totalDegree hb

theorem literalF_support : SupportBound literalF 1 :=
  supportBound_mono (laurentMap_supportBound ordinaryF) ordinaryF_degree

theorem literalG_support (p : ℕ) : SupportBound (literalG p) p :=
  supportBound_mono (laurentMap_supportBound (ordinaryG p)) (ordinaryG_degree p)

def finiteNumerator (p : ℕ) (hp : 0 < p) (k r : ℕ) : LaurentPolynomial :=
  kappa p hp (literalG p ^ k * literalF ^ (p - r))

theorem finiteNumerator_support (p : ℕ) (hp : 0 < p) (k r : ℕ)
    (hr : 1 ≤ r) (hrp : r ≤ p) : SupportBound (finiteNumerator p hp k r) k := by
  have hinput := supportBound_mul (supportBound_pow (literalG_support p) k)
    (supportBound_pow literalF_support (p - r))
  have hstrict : ∀ x ∈ (literalG p ^ k * literalF ^ (p - r)).coeff.support,
      canonicalDegree x < p * (k + 1) := by
    intro x hx
    have h := hinput x hx
    simp only [Nat.mul_one] at h
    have hsub := Nat.sub_add_cancel hrp
    nlinarith
  intro x hx
  have h := kappa_support_strict p hp _ (k + 1) hstrict x hx
  omega

theorem finiteNumerator_integral (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (k r : ℕ) : IntegralCoefficients p (finiteNumerator p hp.pos k r) := by
  intro x
  rw [finiteNumerator, kappa_coeff]
  exact integralCoefficients_mul p hp
    (integralCoefficients_pow p hp (literalG_coefficient_integral p hp hp7) k)
    (integralCoefficients_pow p hp (literalF_coefficient_integral p hp hp7) (p - r)) _

def actualFiniteCoefficients (p : ℕ) (hp : 0 < p) : Fin 5 → Fin 5 → SixExponent →₀ ℚ :=
  fun k r => canonicalCoefficients (finiteNumerator p hp k.val (r.val + 1))

def finiteCartierArray (p : ℕ) (hp : 0 < p) : Fin 5 → LowVector :=
  finiteCoefficientArray p (actualFiniteCoefficients p hp)

theorem actualFiniteCoefficients_integral (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (k r : Fin 5) (a : SixExponent) : pIntegral p (actualFiniteCoefficients p hp.pos k r a) :=
  canonicalCoefficients_integral p hp _ (finiteNumerator_integral p hp hp7 _ _) a

theorem finiteCartierArray_integral (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (r i : Fin 5) : pIntegral p (finiteCartierArray p hp.pos r i) :=
  finiteCoefficientArray_integral p hp hp7 _ (actualFiniteCoefficients_integral p hp hp7) r i

theorem actualFiniteCoefficients_support (p : ℕ) (hp : 0 < p) (hp7 : 7 ≤ p)
    (k r : Fin 5) (a : SixExponent) (ha : a ∈ (actualFiniteCoefficients p hp k r).support) :
    exponentDegree a ≤ k.val ∧ ∃ i, a i = 0 := by
  constructor
  · exact canonicalCoefficients_support_degree _ k.val
      (finiteNumerator_support p hp k.val (r.val + 1) (by omega) (by omega)) a ha
  · exact canonicalCoefficients_support_has_zero _ a ha

theorem finiteCartierArray_scalar_row (p : ℕ) (hp : 0 < p) (hp7 : 7 ≤ p) (r : Fin 5) :
    scalarRow (finiteCartierArray p hp r) =
      WPReview.fiveInterpolation
        (fun a => WPReview.finiteCoefficient p (a * p - (r.val + 1))) := by
  rw [finiteCartierArray, scalarRow_finiteCoefficientArray]
  simp only [actualFiniteCoefficients, canonicalCoefficients_zero,
    finiteNumerator, constantCoefficient_kappa]
  have h := literal_five_weight_finiteCoefficient p (r.val + 1) hp (by omega)
  simpa [Fin.sum_univ_succ, Finset.sum_range_succ, add_assoc] using h

theorem finiteCartierArray_marked_identity (p : ℕ) (hp : 0 < p) (hp7 : 7 ≤ p) :
    9 * arrayMarkedScalar (finiteCartierArray p hp) =
      WPReview.fifteenCoefficientCombination p := by
  rw [arrayMarkedScalar_eq]
  rw [finiteCartierArray_scalar_row p hp hp7 0,
    finiteCartierArray_scalar_row p hp hp7 1,
    finiteCartierArray_scalar_row p hp hp7 2]
  norm_num [WPReview.fifteenCoefficientCombination, WPReview.weightedFiniteCoefficient,
    WPReview.fiveInterpolation]
  ring

theorem markedVector_integral (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (r : Fin 5) :
    pIntegral p (markedVector r) := by
  fin_cases r
  · exact pIntegral_of_fraction p 25 9 (prime_not_dvd_nine p hp hp7)
  · exact pIntegral_of_fraction p (-210) 9 (prime_not_dvd_nine p hp hp7)
  · exact pIntegral_of_fraction p 266 9 (prime_not_dvd_nine p hp hp7)
  · exact pIntegral_natCast p hp 0
  · exact pIntegral_natCast p hp 0

theorem finiteCartierArray_marked_integral (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    pIntegral p (arrayMarkedScalar (finiteCartierArray p hp.pos)) := by
  unfold arrayMarkedScalar scalarRow
  apply pIntegral_sum p hp
  intro i hi
  apply pIntegral_sum p hp
  intro r hr
  exact pIntegral_mul p hp (finiteCartierArray_integral p hp hp7 r i)
    (markedVector_integral p hp hp7 r)

theorem finiteCartierArray_literal_congruence (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    WPReview.RationalCongruent p 5 (arrayMarkedScalar (finiteCartierArray p hp.pos))
      (WPReview.literalSum p) :=
  literalCongruence_of_arrayIdentity p hp hp7 _
    (finiteCartierArray_marked_identity p hp.pos hp7)

theorem finiteCartierMatrix_literal_congruence (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    WPReview.RationalCongruent p 5
      (dotProduct (1 : LowVector)
        ((coefficientMatrix (finiteCartierArray p hp.pos)).mulVec markedVector))
      (WPReview.literalSum p) := by
  rw [← arrayMarkedScalar_matrix]
  exact finiteCartierArray_literal_congruence p hp hp7

theorem finiteCartierMatrix_marked_identity (p : ℕ) (hp : 0 < p) (hp7 : 7 ≤ p) :
    9 * dotProduct (1 : LowVector)
      ((coefficientMatrix (finiteCartierArray p hp)).mulVec markedVector) =
        WPReview.fifteenCoefficientCombination p := by
  rw [← arrayMarkedScalar_matrix]
  exact finiteCartierArray_marked_identity p hp hp7

theorem marked_pairing : dotProduct (1 : LowVector) markedVector = 9 := by
  simpa [dotProduct, scalarRow] using scalarRow_markedVector

theorem inverseTraceNumerator_support (p : ℕ) (hp : 0 < p) (j : ℕ) :
    SupportBound (kappa p hp (literalG p ^ j)) j := by
  apply kappa_support_closed
  simpa [Nat.mul_comm] using supportBound_pow (literalG_support p) j

theorem inverseTraceNumerator_strict (p : ℕ) (hp : 0 < p) (r j : ℕ) (hr : 1 ≤ r) :
    ∀ x ∈ (kappa p hp (literalG p ^ j)).coeff.support, canonicalDegree x < r + j := by
  intro x hx
  have h := inverseTraceNumerator_support p hp j x hx
  omega

theorem actual_inverse_trace_tail_eventual (p precision : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ cutoff : ℕ, ∀ r N j : ℕ, ∀ x : Exponents,
      1 ≤ r → r ≤ 5 → 1 ≤ N → N ≤ j → cutoff ≤ j →
      WPReview.RationalCongruent p precision
        (inverseTraceTailScalar p r N j * (kappa p hp.pos (literalG p ^ j)).coeff x) 0 := by
  obtain ⟨cutoff, h⟩ := inverse_trace_tail_eventual p precision hp hp7
  refine ⟨cutoff, fun r N j x hr hr5 hN hNj hj => ?_⟩
  apply rationalCongruent_zero_mul_pIntegral p precision hp
    _ _ (h r N j hr hr5 hN hNj hj)
  rw [kappa_coeff]
  exact integralCoefficients_pow p hp (literalG_coefficient_integral p hp hp7) j _

theorem actual_factorial_tail_eventual (p precision : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ cutoff : ℕ, ∀ k r : ℕ, ∀ x : Exponents, cutoff ≤ k →
      WPReview.RationalCongruent p precision
        (factorialTailScalar p k * (finiteNumerator p hp.pos k r).coeff x) 0 := by
  obtain ⟨cutoff, h⟩ := factorial_tail_eventual p precision hp hp7
  exact ⟨cutoff, fun k r x hk => rationalCongruent_zero_mul_pIntegral p precision hp
    _ _ (h k hk) (finiteNumerator_integral p hp hp7 k r x)⟩

theorem actual_inverse_trace_image (p : ℕ) (hp : 0 < p) (r N M : ℕ)
    (hr : 1 ≤ r) (hN : 1 ≤ N) :
    finiteInverseTraceImage (kappa p hp) (literalG p) p r N M =
      ∑ j ∈ Finset.range M,
        if j = 0 then Finsupp.single r (1 : LaurentPolynomial)
        else if j < N then 0 else
          ((-1 : ℚ) ^ (N - 1) * (p : ℚ) ^ j * ((r + j - 1).choose j : ℚ) *
            ((j - 1).choose (N - 1) : ℚ)) •
              Finsupp.single (r + j) (kappa p hp (literalG p ^ j)) := by
  simpa only [kappa_one] using finite_inverse_trace_image (kappa p hp) (literalG p) p r N M hr hN

end
end WPCartierFinite
