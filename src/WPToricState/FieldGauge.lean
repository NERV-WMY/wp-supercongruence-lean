import WPToricState.Gauge
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section

namespace WPToricState

open Polynomial

variable (p : ℕ) [Fact p.Prime]

abbrev RationalField := FractionRing (Polynomial (ZMod p))

def fieldV : Matrix (Fin 3) (Fin 3) (RationalField p) :=
  (algebraMap (Polynomial (ZMod p)) (RationalField p)).mapMatrix (V p)

theorem det_V_at_zero : (V p).det.eval 0 = 1 := by
  change (Polynomial.evalRingHom 0) (V p).det = 1
  rw [RingHom.map_det]
  change Matrix.det (fun i j => (V p i j).eval 0) = 1
  rw [V_at_zero, Matrix.det_one]

theorem det_V_nonzero : (V p).det ≠ 0 := by
  intro hz
  have he := det_V_at_zero p
  rw [hz, Polynomial.eval_zero] at he
  exact zero_ne_one he

theorem fieldV_det_nonzero : (fieldV p).det ≠ 0 := by
  intro hz
  have he := (algebraMap (Polynomial (ZMod p)) (RationalField p)).map_det (V p)
  have hm : algebraMap (Polynomial (ZMod p)) (RationalField p) (V p).det =
      algebraMap (Polynomial (ZMod p)) (RationalField p) 0 := by
    rw [map_zero]
    exact he.trans hz
  exact det_V_nonzero p ((IsFractionRing.injective (Polynomial (ZMod p)) (RationalField p)) hm)

theorem fieldV_inverse_exists : ∃ B : Matrix (Fin 3) (Fin 3) (RationalField p),
    fieldV p * B = 1 ∧ B * fieldV p = 1 := by
  have hu : IsUnit (fieldV p).det := isUnit_iff_ne_zero.mpr (fieldV_det_nonzero p)
  exact ⟨(fieldV p)⁻¹, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu⟩

end WPToricState

