import WPActualCentralResidueSource
import Mathlib.Algebra.Polynomial.Taylor

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction

namespace WPNativeParameterTaylor

/-- The quotient derivative used by the actual finite parameter coefficient. -/
noncomputable def quotientJet (A D : ℚ[X]) (t : ℚ) : ℚ :=
  (A.derivative.eval t * D.eval t - A.eval t * D.derivative.eval t) / (D.eval t) ^ 2

/-- The exact first Taylor remainder stays in the integral coefficient ring. -/
theorem integral_quotient_first_remainder (p : ℕ) [Fact p.Prime]
    (A D : (integralRationals p)[X]) (t : integralRationals p)
    (hD0 : (D.eval 0).val ≠ 0) (hDt : (D.eval t).val ≠ 0)
    (hi0 : (D.eval 0).val⁻¹ ∈ integralRationals p)
    (hit : (D.eval t).val⁻¹ ∈ integralRationals p) :
    ∃ r : integralRationals p,
      (A.eval 0).val / (D.eval 0).val - (A.eval t).val / (D.eval t).val +
        t.val * ((A.derivative.eval t).val * (D.eval t).val -
          (A.eval t).val * (D.derivative.eval t).val) / (D.eval t).val ^ 2 =
        t.val ^ 2 * r.val := by
  obtain ⟨a, ha⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add A t (-t)
  obtain ⟨d, hd⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add D t (-t)
  rw [add_neg_cancel] at ha hd
  have hA : (A.eval 0).val = a.val * t.val ^ 2 -
      (A.derivative.eval t).val * t.val + (A.eval t).val := by
    simpa [sub_eq_add_neg] using (congrArg (integralRationals p).subtype ha).symm
  have hD : (D.eval 0).val = d.val * t.val ^ 2 -
      (D.derivative.eval t).val * t.val + (D.eval t).val := by
    simpa [sub_eq_add_neg] using (congrArg (integralRationals p).subtype hd).symm
  let J : integralRationals p :=
    A.derivative.eval t * D.eval t - A.eval t * D.derivative.eval t
  let u0 : integralRationals p := ⟨(D.eval 0).val⁻¹, hi0⟩
  let ut : integralRationals p := ⟨(D.eval t).val⁻¹, hit⟩
  refine ⟨((a * D.eval t - A.eval t * d) * D.eval t -
      J * D.derivative.eval t + t * J * d) * u0 * ut ^ 2, ?_⟩
  change _ = t.val ^ 2 *
    (((a.val * (D.eval t).val - (A.eval t).val * d.val) * (D.eval t).val -
      ((A.derivative.eval t).val * (D.eval t).val -
        (A.eval t).val * (D.derivative.eval t).val) * (D.derivative.eval t).val +
      t.val * ((A.derivative.eval t).val * (D.eval t).val -
        (A.eval t).val * (D.derivative.eval t).val) * d.val) *
      (D.eval 0).val⁻¹ * ((D.eval t).val⁻¹) ^ 2)
  field_simp [hD0, hDt]
  rw [hA, hD]
  ring

theorem integral_inverse_of_residue_ne_zero (p : ℕ) [Fact p.Prime]
    (q : integralRationals p) (hq : residueHom p q ≠ 0) :
    q.val ≠ 0 ∧ q.val⁻¹ ∈ integralRationals p := by
  have hq0 : q.val ≠ 0 := by
    intro hz
    apply hq
    change (q.val : ZMod p) = 0
    rw [hz, Rat.cast_zero]
  have hv : padicValRat p q.val = 0 := by
    have hi := q.property
    change 0 ≤ padicValRat p q.val at hi
    have hn : ¬1 ≤ padicValRat p q.val := by
      intro hn
      apply hq
      exact (integral_residue_zero_iff p _ hi).mpr
        (Or.inr (by simpa only [WPReview.RationalCongruent, sub_zero, Nat.cast_one] using hn))
    omega
  refine ⟨hq0, ?_⟩
  change 0 ≤ padicValRat p q.val⁻¹
  rw [padicValRat.inv, hv]
  simp

end WPNativeParameterTaylor
