import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open scoped BigOperators

namespace WPFiniteInversion

/-- The literal full-cutoff finite polylogarithm of weight `k`. -/
def finitePolylog (p k : ℕ) [Fact p.Prime] (x : ZMod p) : ZMod p :=
  ∑ j ∈ Finset.Ico 1 p, x ^ j / (j : ZMod p) ^ k

/-- The literal full-cutoff finite logarithm. -/
def ell (p : ℕ) [Fact p.Prime] (x : ZMod p) : ZMod p :=
  ∑ j ∈ Finset.Ico 1 p, x ^ j / (j : ZMod p)

/-- The literal full-cutoff finite dilogarithm. -/
def R (p : ℕ) [Fact p.Prime] (x : ZMod p) : ZMod p :=
  ∑ j ∈ Finset.Ico 1 p, x ^ j / (j : ZMod p) ^ 2

theorem denominator_ne_zero (p j : ℕ) (hj : j ∈ Finset.Ico 1 p) :
    (j : ZMod p) ≠ 0 := by
  intro hzero
  have hdvd := (ZMod.natCast_eq_zero_iff j p).mp hzero
  have hj' := Finset.mem_Ico.mp hj
  exact Nat.not_dvd_of_pos_of_lt (by omega) hj'.2 hdvd

theorem denominator_isUnit (p j : ℕ) [Fact p.Prime]
    (hj : j ∈ Finset.Ico 1 p) : IsUnit (j : ZMod p) := by
  exact isUnit_iff_ne_zero.mpr (denominator_ne_zero p j hj)

theorem reflected_denominator (p j : ℕ) (hj : j ∈ Finset.Ico 1 p) :
    ((p - j : ℕ) : ZMod p) = -(j : ZMod p) := by
  rw [Nat.cast_sub (Nat.le_of_lt (Finset.mem_Ico.mp hj).2), ZMod.natCast_self]
  simp

theorem full_cutoff_reflection (p : ℕ) {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) :
    (∑ j ∈ Finset.Ico 1 p, f (p - j)) = ∑ j ∈ Finset.Ico 1 p, f j := by
  simpa using (Finset.sum_Ico_reflect f 1 (m := p) (n := p) (Nat.le_succ p))

theorem finitePolylog_inversion (p k : ℕ) [Fact p.Prime]
    (x : ZMod p) (hx : x ≠ 0) :
    finitePolylog p k x⁻¹ = (-1) ^ k * (x ^ p)⁻¹ * finitePolylog p k x := by
  unfold finitePolylog
  rw [← full_cutoff_reflection p (fun j => x⁻¹ ^ j / (j : ZMod p) ^ k)]
  calc
    (∑ j ∈ Finset.Ico 1 p, x⁻¹ ^ (p - j) / ((p - j : ℕ) : ZMod p) ^ k) =
        ∑ j ∈ Finset.Ico 1 p,
          ((-1 : ZMod p) ^ k * (x ^ p)⁻¹) * (x ^ j / (j : ZMod p) ^ k) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [inv_pow_sub₀ hx (Nat.le_of_lt (Finset.mem_Ico.mp hj).2),
        reflected_denominator p j hj]
      simp only [div_eq_mul_inv]
      rw [← inv_pow (-(j : ZMod p)) k, inv_neg]
      rw [neg_pow ((j : ZMod p)⁻¹) k]
      rw [← inv_pow (j : ZMod p) k]
      ring
    _ = (-1) ^ k * (x ^ p)⁻¹ *
        ∑ j ∈ Finset.Ico 1 p, x ^ j / (j : ZMod p) ^ k := by
      rw [Finset.mul_sum]

theorem ell_inversion (p : ℕ) [Fact p.Prime] (x : ZMod p) (hx : x ≠ 0) :
    ell p x⁻¹ = -(x ^ p)⁻¹ * ell p x := by
  simpa [finitePolylog, ell] using finitePolylog_inversion p 1 x hx

theorem R_inversion (p : ℕ) [Fact p.Prime] (x : ZMod p) (hx : x ≠ 0) :
    R p x⁻¹ = (x ^ p)⁻¹ * R p x := by
  simpa [finitePolylog, R] using finitePolylog_inversion p 2 x hx

end WPFiniteInversion
