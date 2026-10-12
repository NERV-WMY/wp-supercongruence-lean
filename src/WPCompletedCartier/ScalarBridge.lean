import WPCompletedCartier.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

namespace WPCompletedCartier.ScalarBridge

noncomputable section
open scoped BigOperators
open WPCartierFinite

/-- The integral error lattice in the p-adic field, with its actual scalar factor. -/
def QpCongruent (p precision : ℕ) [Fact p.Prime] (a b : ℚ_[p]) : Prop :=
  ∃ z : ℤ_[p], a - b = (p : ℚ_[p]) ^ precision * (z : ℚ_[p])

theorem qpCongruent_iff_norm (p precision : ℕ) [Fact p.Prime] (a b : ℚ_[p]) :
    QpCongruent p precision a b ↔ ‖a - b‖ ≤ (p : ℝ) ^ (-precision : ℤ) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hnormpos : 0 < ‖(p : ℚ_[p]) ^ precision‖ :=
    norm_pos_iff.mpr (pow_ne_zero _ hp0)
  constructor
  · rintro ⟨z, hz⟩
    rw [hz, norm_mul, ← Padic.norm_p_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) z.property
  · intro h
    have hz : ‖(a - b) / (p : ℚ_[p]) ^ precision‖ ≤ 1 := by
      rw [norm_div]
      apply (div_le_one hnormpos).mpr
      simpa only [Padic.norm_p_pow] using h
    refine ⟨⟨(a - b) / (p : ℚ_[p]) ^ precision, hz⟩, ?_⟩
    dsimp
    field_simp

/-- Casting the finite rational congruence produces an error in the original Zp lattice. -/
theorem rationalCongruent_cast (p precision : ℕ) [Fact p.Prime] (a b : ℚ)
    (h : WPReview.RationalCongruent p precision a b) :
    QpCongruent p precision (a : ℚ_[p]) (b : ℚ_[p]) := by
  apply (qpCongruent_iff_norm p precision _ _).mpr
  rcases h with h | h
  · subst b
    simp
  · by_cases hz : a - b = 0
    · rw [← Rat.cast_sub, hz]
      simp
    · rw [← Rat.cast_sub, Padic.eq_padicNorm,
        padicNorm.eq_zpow_of_nonzero hz, Rat.cast_zpow, Rat.cast_natCast]
      have hpReal : (1 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Fact.out : p.Prime).one_lt.le
      exact zpow_le_zpow_right₀ hpReal (neg_le_neg h)

def integralRational (p : ℕ) [Fact p.Prime] (q : ℚ) (hq : pIntegral p q) : ℤ_[p] :=
  ⟨(q : ℚ_[p]), Padic.norm_rat_le_one hq⟩

@[simp] theorem integralRational_coe (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : pIntegral p q) : (integralRational p q hq : ℚ_[p]) = (q : ℚ_[p]) := rfl

theorem qpCongruent_refl (p precision : ℕ) [Fact p.Prime] (a : ℚ_[p]) :
    QpCongruent p precision a a := ⟨0, by simp⟩

theorem qpCongruent_add (p precision : ℕ) [Fact p.Prime]
    {a b c d : ℚ_[p]} (hab : QpCongruent p precision a b)
    (hcd : QpCongruent p precision c d) : QpCongruent p precision (a + c) (b + d) := by
  obtain ⟨z, hz⟩ := hab
  obtain ⟨w, hw⟩ := hcd
  refine ⟨z + w, ?_⟩
  rw [PadicInt.coe_add, mul_add, ← hz, ← hw]
  ring

theorem qpCongruent_trans (p precision : ℕ) [Fact p.Prime]
    {a b c : ℚ_[p]} (hab : QpCongruent p precision a b)
    (hbc : QpCongruent p precision b c) : QpCongruent p precision a c := by
  obtain ⟨z, hz⟩ := hab
  obtain ⟨w, hw⟩ := hbc
  refine ⟨z + w, ?_⟩
  rw [PadicInt.coe_add, mul_add, ← hz, ← hw]
  ring

theorem qpCongruent_mul_integral (p precision : ℕ) [Fact p.Prime]
    {a b : ℚ_[p]} (hab : QpCongruent p precision a b) (c : ℤ_[p]) :
    QpCongruent p precision (a * (c : ℚ_[p])) (b * (c : ℚ_[p])) := by
  obtain ⟨z, hz⟩ := hab
  refine ⟨z * c, ?_⟩
  rw [PadicInt.coe_mul, ← mul_assoc, ← hz]
  ring

theorem qpCongruent_sum (p precision : ℕ) [Fact p.Prime] {α : Type*}
    (s : Finset α) (a b : α → ℚ_[p])
    (h : ∀ i ∈ s, QpCongruent p precision (a i) (b i)) :
    QpCongruent p precision (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using qpCongruent_refl p precision 0
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact qpCongruent_add p precision (h i (Finset.mem_insert_self i s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

def markedZp (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) : Fin 5 → ℤ_[p] :=
  fun r => integralRational p (markedVector r)
    (markedVector_integral p Fact.out hp7 r)

@[simp] theorem markedZp_coe (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) (r : Fin 5) :
    (markedZp p hp7 r : ℚ_[p]) = (markedVector r : ℚ_[p]) := rfl

def finiteMatrixQp (p : ℕ) [Fact p.Prime] : Matrix (Fin 5) (Fin 5) ℚ_[p] :=
  fun i r => (coefficientMatrix (finiteCartierArray p (Fact.out : p.Prime).pos) i r : ℚ_[p])

def markedQp (p : ℕ) [Fact p.Prime] : Fin 5 → ℚ_[p] :=
  fun r => (markedVector r : ℚ_[p])

theorem finiteMarkedScalar_cast (p : ℕ) [Fact p.Prime] :
    dotProduct (1 : Fin 5 → ℚ_[p]) ((finiteMatrixQp p).mulVec (markedQp p)) =
      ((dotProduct (1 : LowVector)
        ((coefficientMatrix (finiteCartierArray p (Fact.out : p.Prime).pos)).mulVec
          markedVector) : ℚ) : ℚ_[p]) := by
  simp [finiteMatrixQp, markedQp, Matrix.mulVec, dotProduct, Rat.cast_sum]

theorem finiteCartierMatrix_literal_cast (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    QpCongruent p 5
      (dotProduct (1 : Fin 5 → ℚ_[p]) ((finiteMatrixQp p).mulVec (markedQp p)))
      (WPReview.literalSum p : ℚ_[p]) := by
  rw [finiteMarkedScalar_cast]
  exact rationalCongruent_cast p 5 _ _
    (finiteCartierMatrix_literal_congruence p Fact.out hp7)

/-- The only operator premise is the actual entrywise congruence that the construction must prove. -/
theorem actualMatrix_literal_transfer (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (C : Matrix (Fin 5) (Fin 5) ℚ_[p])
    (hC : ∀ i r, QpCongruent p 5 (C i r) (finiteMatrixQp p i r)) :
    QpCongruent p 5
      (dotProduct (1 : Fin 5 → ℚ_[p]) (C.mulVec (markedQp p)))
      (WPReview.literalSum p : ℚ_[p]) := by
  apply qpCongruent_trans p 5 _ (finiteCartierMatrix_literal_cast p hp7)
  simp only [dotProduct, Pi.one_apply, one_mul, Matrix.mulVec]
  apply qpCongruent_sum
  intro i hi
  apply qpCongruent_sum
  intro r hr
  simpa only [markedZp_coe, markedQp] using
    qpCongruent_mul_integral p 5 (hC i r) (markedZp p hp7 r)

theorem marked_pairing_qp (p : ℕ) [Fact p.Prime] :
    dotProduct (1 : Fin 5 → ℚ_[p]) (markedQp p) = 9 := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[p])) marked_pairing
  simpa [markedQp, dotProduct, Rat.cast_sum] using h

theorem marked_pairing_zp (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    (∑ r : Fin 5, markedZp p hp7 r) = 9 := by
  apply PadicInt.ext
  simpa only [PadicInt.coe_sum, markedZp_coe,
    show ((9 : ℤ_[p]) : ℚ_[p]) = 9 from rfl,
    dotProduct, Pi.one_apply, one_mul, markedQp] using marked_pairing_qp p

theorem lowPole_denominator_isUnit (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (a : SixExponent) (k : ℕ) (hk : k ≤ 4) :
    IsUnit ((3 ^ exponentDegree a * k.factorial : ℕ) : ℤ_[p]) :=
  WPResidueQuotient.Parameter.padic_nat_isUnit p _
    (lowPole_denominator_unit p Fact.out hp7 a k hk)

theorem nine_isUnit (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) : IsUnit (9 : ℤ_[p]) :=
  WPResidueQuotient.Parameter.padic_nat_isUnit p 9
    (prime_not_dvd_nine p Fact.out hp7)

theorem lowPole_factorial_isUnit (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) (i : Fin 5) :
    IsUnit (i.val.factorial : ℤ_[p]) := by
  apply WPResidueQuotient.Parameter.padic_nat_isUnit
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp
    ((Fact.out : p.Prime).coprime_factorial_of_lt (by omega))

theorem literalSum_integral (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    pIntegral p (WPReview.literalSum p) := by
  rw [WPReview.literal_sum_eq_cleared p (Fact.out : p.Prime).pos]
  exact pIntegral_of_fraction p (WPReview.clearedSum p) _
    (WPReview.clearing_denominator_unit p Fact.out hp7)

def literalSumZp (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) : ℤ_[p] :=
  integralRational p (WPReview.literalSum p) (literalSum_integral p hp7)

@[simp] theorem literalSumZp_coe (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    (literalSumZp p hp7 : ℚ_[p]) = (WPReview.literalSum p : ℚ_[p]) := rfl

/-- The field condition is equivalent to membership in the actual principal integral ideal. -/
theorem qpCongruent_coe_iff_ideal (p precision : ℕ) [Fact p.Prime] (a b : ℤ_[p]) :
    QpCongruent p precision (a : ℚ_[p]) (b : ℚ_[p]) ↔
      a - b ∈ Ideal.span ({(p : ℤ_[p]) ^ precision} : Set ℤ_[p]) := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply PadicInt.ext
    simpa only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast,
      PadicInt.coe_sub] using hz
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have h := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hz
    simpa only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast,
      PadicInt.coe_sub] using h

theorem actualZpMatrix_literal_transfer (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (C : Matrix (Fin 5) (Fin 5) ℤ_[p])
    (hC : ∀ i r, QpCongruent p 5 (C i r : ℚ_[p]) (finiteMatrixQp p i r)) :
    dotProduct (1 : Fin 5 → ℤ_[p]) (C.mulVec (markedZp p hp7)) - literalSumZp p hp7 ∈
      Ideal.span ({(p : ℤ_[p]) ^ 5} : Set ℤ_[p]) := by
  apply (qpCongruent_coe_iff_ideal p 5 _ _).mp
  have h := actualMatrix_literal_transfer p hp7 (fun i r => (C i r : ℚ_[p])) hC
  simpa only [dotProduct, Matrix.mulVec, Pi.one_apply, one_mul,
    PadicInt.coe_sum, PadicInt.coe_mul, markedZp_coe, literalSumZp_coe, markedQp] using h

def gammaMarkedVector : LowVector := ![25 / 9, -210 / 9, 133 / 9, 0, 0]

def inverseFactorialMatrix : Matrix (Fin 5) (Fin 5) ℚ :=
  Matrix.diagonal (fun i => (i.val.factorial : ℚ)⁻¹)

theorem factorialMatrix_mulVec (v : LowVector) :
    factorialMatrix.mulVec v = factorialDiagonal v := by
  ext i
  simp [factorialMatrix, factorialDiagonal, Matrix.mulVec_diagonal]

theorem factorialMatrix_marked : factorialMatrix.mulVec gammaMarkedVector = markedVector := by
  rw [factorialMatrix_mulVec]
  ext i
  fin_cases i <;> norm_num [factorialDiagonal, gammaMarkedVector, markedVector]

theorem gamma_marked_pairing : gammaLambda gammaMarkedVector = 9 := by
  rw [← scalarRow_factorialDiagonal, ← factorialMatrix_mulVec, factorialMatrix_marked]
  exact scalarRow_markedVector

theorem factorialMatrix_inverse_left : inverseFactorialMatrix * factorialMatrix = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [inverseFactorialMatrix, factorialMatrix,
      Nat.factorial_ne_zero]
  · simp [inverseFactorialMatrix, factorialMatrix, h]

theorem factorialMatrix_inverse_right : factorialMatrix * inverseFactorialMatrix = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [inverseFactorialMatrix, factorialMatrix,
      Nat.factorial_ne_zero]
  · simp [inverseFactorialMatrix, factorialMatrix, h]

/-- Change of actual coordinates multiplies the output by H and the input by its inverse. -/
theorem factorial_conjugation_entries (C : Matrix (Fin 5) (Fin 5) ℚ) (i r : Fin 5) :
    (factorialMatrix * C * inverseFactorialMatrix) i r =
      (i.val.factorial : ℚ) * C i r / (r.val.factorial : ℚ) := by
  simp [factorialMatrix, inverseFactorialMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
    div_eq_mul_inv, mul_assoc]

theorem normalized_marked_scalar (C : Matrix (Fin 5) (Fin 5) ℚ) :
    dotProduct (1 : LowVector)
      ((factorialMatrix * C * inverseFactorialMatrix).mulVec markedVector) =
        gammaLambda (C.mulVec gammaMarkedVector) := by
  have hm : inverseFactorialMatrix.mulVec markedVector = gammaMarkedVector := by
    rw [← factorialMatrix_marked, Matrix.mulVec_mulVec,
      factorialMatrix_inverse_left, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hm, factorialMatrix_mulVec]
  simpa only [scalarRow, dotProduct, Pi.one_apply, one_mul] using
    scalarRow_factorialDiagonal (C.mulVec gammaMarkedVector)

end
end WPCompletedCartier.ScalarBridge
