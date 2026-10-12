import WPGamma.Matrix

noncomputable section

namespace WPGamma

open WPPsi Polynomial

variable (p : ℕ) [Fact p.Prime]

theorem gamma_cyclic_matrix (hp7 : 7 ≤ p) :
    gammaZ p * T p = T p * (fieldN p).transpose := by
  have h6 : (6 : K p) ≠ 0 := isUnit_iff_ne_zero.mp (WPDual.six_field_unit p hp7)
  have hd : 1 - polyMap p X ≠ 0 := by
    simpa only [oneMinus_literal] using oneMinus_nonzero p
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaZ, gammaM, T_actual, Matrix.mul_apply, Fin.sum_univ_succ,
      fieldN_actual_entry, WPState.lowerCoeff, q, map_inv₀, map_ofNat, oneMinus_literal] <;>
    field_simp <;> ring

end WPGamma
