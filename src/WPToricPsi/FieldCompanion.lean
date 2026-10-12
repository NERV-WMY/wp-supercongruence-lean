import WPPsi.FieldDerivation
import WPToricState.FieldGauge
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

open WPPsi

namespace WPToricPsi

open Polynomial

variable (p : ℕ) [Fact p.Prime]

def oneMinus : K p := polyMap p (1 - X)

theorem oneMinus_nonzero : oneMinus p ≠ 0 := by
  have hz : (1 - X : Polynomial (ZMod p)) ≠ 0 := by
    intro h
    have hc := congrArg (fun P : Polynomial (ZMod p) => P.coeff 1) h
    norm_num [Polynomial.coeff_one] at hc
  simpa only [oneMinus, polyMap, map_zero] using
    (IsFractionRing.injective (Polynomial (ZMod p)) (K p)).ne hz

def fieldJ : Matrix (Fin 3) (Fin 3) (K p) :=
  (polyMap p).mapMatrix (WPToricState.J p)

def fieldNpoly : Matrix (Fin 3) (Fin 3) (K p) :=
  (polyMap p).mapMatrix (WPToricState.Npoly p)

def fieldN : Matrix (Fin 3) (Fin 3) (K p) :=
  fun i j => (oneMinus p)⁻¹ * fieldNpoly p i j

def thetaMatrix (M : Matrix (Fin 3) (Fin 3) (K p)) :
    Matrix (Fin 3) (Fin 3) (K p) := fun i j => theta p (M i j)

theorem fieldJ_entry (i j : Fin 3) :
    fieldJ p i j = algebraMap (ZMod p) (K p) (WPToricState.jordan p i j) := by
  change polyMap p (C (WPToricState.jordan p i j)) = _
  simp only [polyMap]
  rfl

theorem theta_fieldJ (i j : Fin 3) : theta p (fieldJ p i j) = 0 := by
  rw [fieldJ_entry]
  exact (theta p).map_algebraMap _

theorem fieldJ_third_zero : fieldJ p ^ 3 = 0 := by
  rw [fieldJ, ← map_pow, WPToricState.J_third_zero, map_zero]

theorem theta_fieldV (i j : Fin 3) :
    theta p (WPToricState.fieldV p i j) = polyMap p (WPRho.theta (WPToricState.V p i j)) :=
  theta_poly p _

theorem cleared_field_gauge (hp7 : 7 ≤ p) (i j : Fin 3) :
    oneMinus p * theta p (WPToricState.fieldV p i j) =
      (fieldNpoly p * WPToricState.fieldV p) i j -
        oneMinus p * (WPToricState.fieldV p * fieldJ p) i j := by
  have he := congrArg (polyMap p)
    (congrFun (congrFun (WPToricState.cleared_gauge_equation p hp7) i) j)
  change polyMap p ((1 - X) * WPRho.theta (WPToricState.V p i j)) =
    polyMap p ((WPToricState.Npoly p * WPToricState.V p) i j -
      (1 - X) * (WPToricState.V p * WPToricState.J p) i j) at he
  simp only [map_sub, map_mul] at he
  rw [(polyMap p).map_matrix_mul, (polyMap p).map_matrix_mul] at he
  rw [theta_fieldV]
  simpa only [oneMinus, map_sub, fieldNpoly, fieldJ, WPToricState.fieldV, polyMap,
    RingHom.mapMatrix_apply] using he

theorem fieldN_mul_entry (M : Matrix (Fin 3) (Fin 3) (K p)) (i j : Fin 3) :
    (fieldN p * M) i j = (oneMinus p)⁻¹ * (fieldNpoly p * M) i j := by
  simp only [Matrix.mul_apply, fieldN, Finset.mul_sum, mul_assoc]

theorem field_gauge_equation (hp7 : 7 ≤ p) :
    thetaMatrix p (WPToricState.fieldV p) =
      fieldN p * WPToricState.fieldV p - WPToricState.fieldV p * fieldJ p := by
  apply Matrix.ext
  intro i j
  apply mul_left_cancel₀ (oneMinus_nonzero p)
  change oneMinus p * theta p (WPToricState.fieldV p i j) =
    oneMinus p * ((fieldN p * WPToricState.fieldV p) i j -
      (WPToricState.fieldV p * fieldJ p) i j)
  rw [mul_sub, fieldN_mul_entry, ← mul_assoc, mul_inv_cancel₀ (oneMinus_nonzero p), one_mul]
  exact cleared_field_gauge p hp7 i j

end WPToricPsi

