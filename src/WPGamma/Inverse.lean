import WPGamma.Actual

noncomputable section

namespace WPGamma

open WPPsi

variable (p : ℕ) [Fact p.Prime]

def TInverse : Matrix (Fin 5) (Fin 5) (K p) :=
  !![1, 1, 2, 6, 24;
     0, 6, 18, 66, 300;
     0, 0, 36, 216, 1260;
     0, 0, 0, 216, 2160;
     0, 0, 0, 0, 1296]

theorem TInverse_mul_T (hp7 : 7 ≤ p) : TInverse p * T p = 1 := by
  have h6 : (6 : K p) ≠ 0 := isUnit_iff_ne_zero.mp (WPDual.six_field_unit p hp7)
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [TInverse, T_actual, Matrix.mul_apply, Fin.sum_univ_succ, q] <;>
    field_simp <;> ring

theorem TInverse_eq_inv (hp7 : 7 ≤ p) : TInverse p = (T p)⁻¹ := by
  calc
    TInverse p = TInverse p * (T p * (T p)⁻¹) := by rw [T_mul_inv p hp7, mul_one]
    _ = (TInverse p * T p) * (T p)⁻¹ := (mul_assoc _ _ _).symm
    _ = (T p)⁻¹ := by rw [TInverse_mul_T p hp7, one_mul]

theorem T_mul_TInverse (hp7 : 7 ≤ p) : T p * TInverse p = 1 := by
  rw [TInverse_eq_inv p hp7]
  exact T_mul_inv p hp7

theorem det_T_literal : (T p).det = (6 : K p) ^ (-10 : ℤ) := by
  simpa only [q, zpow_neg, zpow_ofNat, inv_pow] using det_T p

end WPGamma
