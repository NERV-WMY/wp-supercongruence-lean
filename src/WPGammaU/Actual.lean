import WPGammaU.Connection

noncomputable section

namespace WPGammaU

open WPPsi Polynomial

variable (p : ℕ) [Fact p.Prime]

def u : K p := polyMap p X
def z : K p := (6*u p)^6
def delta : K p := 1-z p
def literalGammaM : Matrix (Fin 5) (Fin 5) (K p) :=
  !![-1, 0, 0, 0, (delta p)⁻¹;
     1, -2, 0, 0, -31*(delta p)⁻¹;
     0, 1, -3, 0, 90*(delta p)⁻¹;
     0, 0, 1, -4, -65*(delta p)⁻¹;
     0, 0, 0, 1, 15*(delta p)⁻¹-5]
def literalNabla : StateEnd p := euler p+matrixAction p (literalGammaM p)

theorem delta_nonzero (hp7 : 7 ≤ p) : delta p ≠ 0 := by
  have he : delta p=substitute p hp7 (oneMinus p) := (substitute_delta p hp7).symm
  rw [he]
  simpa only [map_zero] using (substitute p hp7).injective.ne (oneMinus_nonzero p)

theorem theta_u : theta p (u p)=u p := by
  rw [u, theta_poly]
  simp [WPRho.theta]

theorem theta_z : theta p (z p)=6*z p := by
  have h6 : theta p (6 : K p)=0 := by
    simpa only [map_ofNat] using (theta p).map_algebraMap (6 : ZMod p)
  rw [z, (theta p).leibniz_pow, (theta p).leibniz, theta_u]
  rw [h6]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

theorem gammaM_eq_literal (hp7 : 7 ≤ p) : gammaM p hp7=literalGammaM p := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaM, mappedMatrix, WPGamma.gammaM, literalGammaM,
      map_sub, map_mul, map_inv₀, map_ofNat, substitute_delta, delta, z, u]

theorem nabla_eq_literal (hp7 : 7 ≤ p) : nabla p hp7=literalNabla p := by
  rw [nabla, literalNabla, gammaM_eq_literal]

theorem literalNabla_apply (v : StateSpace p) (i : Fin 5) :
    literalNabla p v i=theta p (v i)+∑ j, literalGammaM p i j*v j := rfl

theorem literalNabla_leibniz (a : K p) (v : StateSpace p) :
    literalNabla p (a • v)=theta p a • v+a • literalNabla p v := by
  funext i
  simp only [literalNabla_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
    (theta p).leibniz, mul_add, Finset.mul_sum]
  have hs : (∑ j, literalGammaM p i j*(a*v j)) =
      ∑ j, a*(literalGammaM p i j*v j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  ring

theorem actual_literal_u_fifth_zero (hp7 : 7 ≤ p) :
    (literalNabla p^p-literalNabla p)^5=0 := by
  rw [← nabla_eq_literal p hp7]
  exact actual_u_field_fifth_zero p hp7

end WPGammaU
