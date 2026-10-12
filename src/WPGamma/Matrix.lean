import WPDual
import Mathlib.LinearAlgebra.Matrix.Block

noncomputable section

namespace WPGamma

open WPPsi Polynomial

variable (p : ℕ) [Fact p.Prime]

def q : K p := (6 : K p)⁻¹

def gammaM : Matrix (Fin 5) (Fin 5) (K p) :=
  !![-1, 0, 0, 0, (oneMinus p)⁻¹;
     1, -2, 0, 0, -31 * (oneMinus p)⁻¹;
     0, 1, -3, 0, 90 * (oneMinus p)⁻¹;
     0, 0, 1, -4, -65 * (oneMinus p)⁻¹;
     0, 0, 0, 1, 15 * (oneMinus p)⁻¹ - 5]

def gammaZ : Matrix (Fin 5) (Fin 5) (K p) := q p • gammaM p

def Tbase : Matrix (Fin 5) (Fin 5) (ZMod p) :=
  let b := (6 : ZMod p)⁻¹
  !![1, -b, b ^ 2, -b ^ 3, b ^ 4;
     0, b, -3 * b ^ 2, 7 * b ^ 3, -15 * b ^ 4;
     0, 0, b ^ 2, -6 * b ^ 3, 25 * b ^ 4;
     0, 0, 0, b ^ 3, -10 * b ^ 4;
     0, 0, 0, 0, b ^ 4]

def T : Matrix (Fin 5) (Fin 5) (K p) :=
  (algebraMap (ZMod p) (K p)).mapMatrix (Tbase p)

theorem T_actual : T p =
    !![1, -q p, q p ^ 2, -q p ^ 3, q p ^ 4;
       0, q p, -3 * q p ^ 2, 7 * q p ^ 3, -15 * q p ^ 4;
       0, 0, q p ^ 2, -6 * q p ^ 3, 25 * q p ^ 4;
       0, 0, 0, q p ^ 3, -10 * q p ^ 4;
       0, 0, 0, 0, q p ^ 4] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [T, Tbase, RingHom.mapMatrix_apply, Matrix.map_apply, q, map_inv₀, map_ofNat]

theorem T_upper : (T p).IsUpperTriangular := by
  intro i j hij
  rw [T_actual]
  fin_cases i <;> fin_cases j <;> simp_all

theorem det_T : (T p).det = q p ^ 10 := by
  rw [Matrix.det_of_isUpperTriangular (T_upper p), T_actual]
  simp [Fin.prod_univ_succ]
  ring

theorem q_nonzero (hp7 : 7 ≤ p) : q p ≠ 0 := by
  exact inv_ne_zero (isUnit_iff_ne_zero.mp (WPDual.six_field_unit p hp7))

theorem det_T_nonzero (hp7 : 7 ≤ p) : (T p).det ≠ 0 := by
  rw [det_T]
  exact pow_ne_zero _ (q_nonzero p hp7)

theorem T_inv_mul (hp7 : 7 ≤ p) : (T p)⁻¹ * T p = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (det_T_nonzero p hp7))

theorem T_mul_inv (hp7 : 7 ≤ p) : T p * (T p)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_T_nonzero p hp7))

theorem theta_T : thetaMatrix p (T p) = 0 := by
  apply Matrix.ext
  intro i j
  change theta p (algebraMap (ZMod p) (K p) (Tbase p i j)) = 0
  exact (theta p).map_algebraMap _

end WPGamma
