import WPResidueFrobenius.Truncation
import Mathlib.Data.Nat.Choose.Sum

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators

def binomialWeight (r k : ℕ) : ℚ := (-1 : ℚ)^k * ((r+k-1).choose k : ℚ)

theorem binomialWeight_zero (r : ℕ) : binomialWeight r 0 = 1 := by
  simp [binomialWeight]

theorem binomialWeight_factorial (r k : ℕ) (hr : 1 ≤ r) :
    binomialWeight r k = (-1 : ℚ)^k * ((r+k-1).factorial : ℚ) /
      ((k.factorial : ℚ)*((r-1).factorial : ℚ)) := by
  have hn : r+k-1-k = r-1 := by omega
  have hf := Nat.choose_mul_factorial_mul_factorial (show k ≤ r+k-1 by omega)
  rw [hn] at hf
  have hc : ((r+k-1).choose k : ℚ) * (k.factorial : ℚ) * ((r-1).factorial : ℚ) =
      ((r+k-1).factorial : ℚ) := by exact_mod_cast hf
  apply (eq_div_iff (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero k)
    (by exact_mod_cast Nat.factorial_ne_zero (r-1)))).mpr
  dsimp [binomialWeight]
  rw [← hc]
  ring

theorem binomialWeight_derivative (r k : ℕ) (hr : 1 ≤ r) :
    (k+1 : ℚ)*binomialWeight r (k+1) = -(r+k : ℚ)*binomialWeight r k := by
  have hn : r+k-1+1 = r+k := by omega
  have h := Nat.add_one_mul_choose_eq (r+k-1) k
  rw [hn] at h
  have hc : (r+k : ℚ)*((r+k-1).choose k : ℚ) =
      ((r+k).choose (k+1) : ℚ)*(k+1) := by exact_mod_cast h
  dsimp [binomialWeight]
  rw [pow_succ]
  linear_combination ((-1 : ℚ)^k)*hc

theorem binomialWeight_raise (r k : ℕ) (hr : 1 ≤ r) :
    (r : ℚ)*binomialWeight (r+1) k = (r+k : ℚ)*binomialWeight r k := by
  have hn : r+k-1+1 = r+k := by omega
  have hs : r+k-k = r := by omega
  have h := Nat.choose_mul_succ_eq (r+k-1) k
  rw [hn, hs] at h
  have hc : ((r+k-1).choose k : ℚ)*(r+k) = ((r+k).choose k : ℚ)*r := by
    exact_mod_cast h
  have hindex : r+1+k-1 = r+k := by omega
  dsimp [binomialWeight]
  rw [hindex]
  linear_combination -((-1 : ℚ)^k)*hc

theorem binomialWeight_pascal (r k : ℕ) :
    binomialWeight (r+1) (k+1) + binomialWeight (r+1) k = binomialWeight r (k+1) := by
  have h₁ : r+1+(k+1)-1 = (r+k)+1 := by omega
  have h₂ : r+1+k-1 = r+k := by omega
  have h₃ : r+(k+1)-1 = r+k := by omega
  simp only [binomialWeight, h₁, h₂, h₃, Nat.choose_succ_succ, Nat.cast_add, pow_succ]
  ring

def binomialPartial {R : Type*} [CommRing R] [Algebra ℚ R] (r N : ℕ) (X : R) : R :=
  ∑ k ∈ Finset.range N, algebraMap ℚ R (binomialWeight r k) * X^k

theorem binomialPartial_succ {R : Type*} [CommRing R] [Algebra ℚ R]
    (r N : ℕ) (X : R) : binomialPartial r (N+1) X =
      binomialPartial r N X + algebraMap ℚ R (binomialWeight r N)*X^N := by
  exact Finset.sum_range_succ _ N

/-- Finite denominator raising retains its last term. -/
theorem binomialPartial_raise {R : Type*} [CommRing R] [Algebra ℚ R]
    (r N : ℕ) (X : R) :
    (1+X)*binomialPartial (r+1) (N+1) X - binomialPartial r (N+1) X =
      algebraMap ℚ R (binomialWeight (r+1) N) * X^(N+1) := by
  induction N with
  | zero => simp [binomialPartial, binomialWeight_zero]
  | succ N ih =>
      rw [binomialPartial_succ (r+1) (N+1), binomialPartial_succ r (N+1)]
      have hc := congrArg (algebraMap ℚ R) (binomialWeight_pascal r N)
      rw [map_add] at hc
      rw [← hc, pow_succ X (N+1)]
      linear_combination ih

def binomialPartialDerivative {R : Type*} [CommRing R] [Algebra ℚ R]
    (r N : ℕ) (X : R) : R :=
  ∑ k ∈ Finset.range N, algebraMap ℚ R ((k+1)*binomialWeight r (k+1))*X^k

/-- Differentiating a finite binomial sum retains the last coefficient. -/
theorem binomialPartial_derivative {R : Type*} [CommRing R] [Algebra ℚ R]
    (r N : ℕ) (hr : 1 ≤ r) (X : R) :
    binomialPartialDerivative r N X = -(r : R)*binomialPartial (r+1) N X := by
  unfold binomialPartialDerivative binomialPartial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hc : (k+1 : ℚ)*binomialWeight r (k+1) = -(r : ℚ)*binomialWeight (r+1) k := by
    linear_combination (binomialWeight_derivative r k hr) + (binomialWeight_raise r k hr)
  rw [hc, map_mul, map_neg]
  simp only [map_natCast]
  ring

theorem derivation_binomialPartial {R : Type*} [CommRing R] [Algebra ℚ R]
    (D : Derivation ℚ R R) (r N : ℕ) (X : R) :
    D (binomialPartial r (N+1) X) = D X * binomialPartialDerivative r N X := by
  induction N with
  | zero => simp [binomialPartial, binomialWeight_zero, binomialPartialDerivative]
  | succ N ih =>
      rw [binomialPartial_succ r (N+1), map_add, ih, Derivation.leibniz,
        Derivation.leibniz_pow]
      simp [binomialPartialDerivative, Algebra.smul_def, Finset.sum_range_succ]
      ring

/-- The ordered five-dimensional logarithmic volume has its literal Jacobian factor. -/
theorem ordered_top_volume (R : Type*) [CommRing R] (p : ℕ) :
    Matrix.det ((p : R) • (1 : Matrix (Fin 5) (Fin 5) R)) = (p : R)^5 := by
  simp

theorem pullbackScalar_binomial (p r k : ℕ) (hr : 1 ≤ r) :
    pullbackScalar p r k * ((p*(r+k)-1).factorial : ℚ) =
      (p : ℚ)^(5+k)*((r-1).factorial : ℚ)*binomialWeight r k := by
  rw [binomialWeight_factorial r k hr]
  unfold pullbackScalar
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hrn : ((r-1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (r-1)
  have hn : ((p*(r+k)-1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

theorem primitiveTailScalar_binomial (p r k : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    primitiveTailScalar p r (k+1) * ((p*(r+k)).factorial : ℚ) =
      (p : ℚ)^(5+k)*((r-1).factorial : ℚ)*r*binomialWeight (r+1) k := by
  have hpos : 1 ≤ p*(r+k) := Nat.mul_pos hp.pos (by omega)
  have he : p*(r+k)-1+1 = p*(r+k) := by omega
  have hf := Nat.factorial_succ (p*(r+k)-1)
  rw [he] at hf
  have hfQ : ((p*(r+k)).factorial : ℚ) =
      (p : ℚ)*(r+k)*((p*(r+k)-1).factorial : ℚ) := by exact_mod_cast hf
  rw [primitiveTailScalar, Nat.add_sub_cancel, hfQ]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  calc
    _ = (r+k : ℚ)*(pullbackScalar p r k*((p*(r+k)-1).factorial : ℚ)) := by field_simp
    _ = _ := by
      rw [pullbackScalar_binomial p r k hr]
      linear_combination -(p : ℚ)^(5+k)*((r-1).factorial : ℚ)*binomialWeight_raise r k hr

end WPResidueFrobenius
