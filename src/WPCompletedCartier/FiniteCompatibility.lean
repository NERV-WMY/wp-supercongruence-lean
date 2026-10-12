import WPResidueQuotient.PolePresentation
import Mathlib.Tactic

namespace WPCompletedCartier

noncomputable section

open scoped BigOperators

section Telescoping

variable {A : Type*} [AddCommGroup A]

theorem normalized_pascal_telescoping (h K : ℕ) (t : ℕ → A) :
    (∑ k ∈ Finset.range K, ((h + k) • t k - (k + 1) • t (k + 1))) =
      h • (∑ k ∈ Finset.range K, t k) - K • t K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, smul_add]
      rw [add_nsmul]
      abel

end Telescoping

section Numerator

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]

theorem selector_denominator_step
    (κ : P →ₗ[R] P) (φ : P →ₐ[R] P) (f G B : P) (p k : ℕ)
    (hG : f ^ p = φ f - (p : R) • G)
    (hκ : ∀ H : P, κ (H * φ f) = κ H * f) :
    κ (B * f ^ p * G ^ k) =
      f * κ (B * G ^ k) - (p : R) • κ (B * G ^ (k + 1)) := by
  have he : B * f ^ p * G ^ k =
      (B * G ^ k) * φ f - (p : R) • (B * G ^ (k + 1)) := by
    rw [hG, Algebra.smul_def, Algebra.smul_def, pow_succ]
    ring
  rw [he, map_sub, map_smul, hκ, mul_comm (κ (B * G ^ k)) f]

def selectedNumerator (κ : P →ₗ[R] P) (f G A : P) (p m h k : ℕ) : P :=
  κ (A * f ^ (p * h - m) * G ^ k)

theorem selectedNumerator_successor
    (κ : P →ₗ[R] P) (φ : P →ₐ[R] P) (f G A : P) (p m h k : ℕ)
    (hadmissible : m ≤ p * h)
    (hG : f ^ p = φ f - (p : R) • G)
    (hκ : ∀ H : P, κ (H * φ f) = κ H * f) :
    selectedNumerator κ f G A p m (h + 1) k =
      f * selectedNumerator κ f G A p m h k -
        (p : R) • selectedNumerator κ f G A p m h (k + 1) := by
  have he : p * (h + 1) - m = p * h - m + p := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  simp only [selectedNumerator, he, pow_add, ← mul_assoc]
  simpa only [pow_succ, pow_zero, pow_one, one_mul, mul_assoc] using
    selector_denominator_step κ φ f G (A * f ^ (p * h - m)) p k hG hκ

theorem selectedNumerator_common_pole
    (κ : P →ₗ[R] P) (f G A : P) (p m M h k : ℕ)
    (hmM : m ≤ M) (hM : M ≤ p * h) :
    selectedNumerator κ f G (A * f ^ (M - m)) p M h k =
      selectedNumerator κ f G A p m h k := by
  have he : M - m + (p * h - M) = p * h - m := by omega
  simp only [selectedNumerator, mul_assoc, ← pow_add, he]

end Numerator

section ActualFractions

open WPResidueQuotient

variable {R : Type*} [CommRing R]

def gammaNumeratorMap (u : R) (m : ℕ) :
    WPResidueQuotient.LaurentPolynomial R →ₗ[R] ActualRing u :=
  numeratorLinearMap u (Gamma u m)

theorem gammaNumeratorMap_eq_factorial (u : R) (m : ℕ) (hm : 1 ≤ m) :
    gammaNumeratorMap u m = factorialNumeratorMap u (m - 1) := by
  have he : m - 1 + 1 = m := by omega
  simp only [gammaNumeratorMap, factorialNumeratorMap, ← Gamma_succ, he]

theorem gammaNumeratorMap_raise (u : R) (m : ℕ) (hm : 0 < m)
    (Q : WPResidueQuotient.LaurentPolynomial R) :
    gammaNumeratorMap u (m + 1) (torusPolynomial u * Q) =
      (m : R) • gammaNumeratorMap u m Q := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  simp only [gammaNumeratorMap, numeratorLinearMap, LinearMap.coe_mk,
    AddHom.coe_mk, Gamma_succ, map_mul, Algebra.smul_def, map_natCast]
  calc
    _ = algebraMap (WPResidueQuotient.LaurentPolynomial R) (ActualRing u) Q *
        (factorialPole u (n + 1) *
          algebraMap (WPResidueQuotient.LaurentPolynomial R) (ActualRing u)
            (torusPolynomial u)) := by ring
    _ = algebraMap (WPResidueQuotient.LaurentPolynomial R) (ActualRing u) Q *
        ((n + 1 : ActualRing u) * factorialPole u n) := by
      rw [← factorialPole_raise]
    _ = _ := by push_cast; ring

def clearedTerm (u : R)
    (κ : WPResidueQuotient.LaurentPolynomial R →ₗ[R]
      WPResidueQuotient.LaurentPolynomial R)
    (G A : WPResidueQuotient.LaurentPolynomial R)
    (p m h : ℕ) (α : ℕ → R) (k : ℕ) : ActualRing u :=
  α k • gammaNumeratorMap u (h + k)
    (selectedNumerator κ (torusPolynomial u) G A p m h k)

theorem clearedTerm_successor (u : R)
    (κ : WPResidueQuotient.LaurentPolynomial R →ₗ[R]
      WPResidueQuotient.LaurentPolynomial R)
    (φ : WPResidueQuotient.LaurentPolynomial R →ₐ[R]
      WPResidueQuotient.LaurentPolynomial R)
    (G A : WPResidueQuotient.LaurentPolynomial R)
    (p m h : ℕ) (α : ℕ → R) (hh : 0 < h) (hadmissible : m ≤ p * h)
    (hG : torusPolynomial u ^ p = φ (torusPolynomial u) - (p : R) • G)
    (hκ : ∀ H, κ (H * φ (torusPolynomial u)) = κ H * torusPolynomial u)
    (hα : ∀ k : ℕ, ((k + 1 : ℕ) : R) * α (k + 1) = (p : R) * α k)
    (k : ℕ) :
    clearedTerm u κ G A p m (h + 1) α k =
      (h + k) • clearedTerm u κ G A p m h α k -
        (k + 1) • clearedTerm u κ G A p m h α (k + 1) := by
  unfold clearedTerm
  rw [selectedNumerator_successor κ φ (torusPolynomial u) G A p m h k
    hadmissible hG hκ]
  have hi : h + 1 + k = h + k + 1 := by omega
  rw [hi, map_sub, map_smul, smul_sub,
    gammaNumeratorMap_raise u (h + k) (by omega)]
  have hj : h + (k + 1) = h + k + 1 := by omega
  rw [hj]
  simp only [smul_smul, ← Nat.cast_smul_eq_nsmul R,
    Nat.cast_add, Nat.cast_one]
  have hα' : ((k : R) + 1) * α (k + 1) = (p : R) * α k := by
    simpa only [Nat.cast_add, Nat.cast_one] using hα k
  rw [hα']
  congr 1 <;> ring

theorem cleared_approximations_pascal (u : R)
    (κ : WPResidueQuotient.LaurentPolynomial R →ₗ[R]
      WPResidueQuotient.LaurentPolynomial R)
    (φ : WPResidueQuotient.LaurentPolynomial R →ₐ[R]
      WPResidueQuotient.LaurentPolynomial R)
    (G A : WPResidueQuotient.LaurentPolynomial R)
    (p m h : ℕ) (α : ℕ → R) (hh : 0 < h) (hadmissible : m ≤ p * h)
    (hG : torusPolynomial u ^ p = φ (torusPolynomial u) - (p : R) • G)
    (hκ : ∀ H, κ (H * φ (torusPolynomial u)) = κ H * torusPolynomial u)
    (hα : ∀ k : ℕ, ((k + 1 : ℕ) : R) * α (k + 1) = (p : R) * α k)
    (K : ℕ) :
    (∑ k ∈ Finset.range K, clearedTerm u κ G A p m (h + 1) α k) =
      h • (∑ k ∈ Finset.range K, clearedTerm u κ G A p m h α k) -
        K • clearedTerm u κ G A p m h α K := by
  simp_rw [clearedTerm_successor u κ φ G A p m h α hh hadmissible hG hκ hα]
  exact normalized_pascal_telescoping h K _

end ActualFractions

end

end WPCompletedCartier
