import WPToricC.Connection

noncomputable section

namespace WPToricC

open WPPsi WPToricPsi

variable (p : ℕ) [Fact p.Prime]

def cConnection : StateEnd p := euler p + matrixAction p
  !![-1 / 2, 0, (1 / 8) * (1 - 27 * c p ^ 3)⁻¹;
      1, -3 / 2, (-13 / 4) * (1 - 27 * c p ^ 3)⁻¹;
      0, 1, (9 / 2) * (1 - 27 * c p ^ 3)⁻¹ - 5 / 2]

def transport (hp7 : 7 ≤ p) : StateEnd p where
  toFun v := fun i => sigma p hp7 (v i)
  map_add' v w := by funext i; exact map_add _ _ _
  map_smul' a v := by
    funext i
    simp only [RingHom.id_apply, Pi.smul_apply, Algebra.smul_def, map_mul, sigma_base]

theorem theta_c : theta p (c p) = c p := by
  rw [c, theta_poly]
  simp [WPRho.theta]

theorem theta_pulled_parameter (hp7 : 7 ≤ p) :
    theta p (27 * c p ^ 3) = 3 * (27 * c p ^ 3) := by
  rw [← sigma_parameter p hp7, theta_sigma]
  change 3 * sigma p hp7 (theta p (c p)) = _
  rw [theta_c]
  rfl

theorem sigma_fraction (hp7 : 7 ≤ p) (P Q : Polynomial (ZMod p)) :
    sigma p hp7 (polyMap p P / polyMap p Q) =
      polyMap p (polySub p P) / polyMap p (polySub p Q) := by
  rw [map_div₀, sigma_poly, sigma_poly]

theorem denominator_image_nonzero (hp7 : 7 ≤ p) (Q : Polynomial (ZMod p)) (hQ : Q ≠ 0) :
    polyMap p (polySub p Q) ≠ 0 := by
  rw [← sigma_poly p hp7]
  simpa only [polyMap, map_zero] using (sigma_injective p hp7).ne
    ((IsFractionRing.injective (Polynomial (ZMod p)) (K p)).ne hQ)

theorem cConnection_eq (hp7 : 7 ≤ p) : cConnection p = cNabla p hp7 := by
  rw [cNabla, cM_literal]
  rfl

theorem actual_parameter_connection_third_zero (hp7 : 7 ≤ p) :
    (cConnection p ^ p - cConnection p) ^ 3 = 0 := by
  rw [cConnection_eq p hp7]
  exact actual_c_field_third_zero p hp7

theorem cConnection_leibniz (a : K p) (v : StateSpace p) :
    cConnection p (a • v) = theta p a • v + a • cConnection p v := by
  funext i
  change theta p (a * v i) + ∑ j, _ * (a * v j) =
    theta p a * v i + a * (theta p (v i) + ∑ j, _ * v j)
  rw [(theta p).leibniz]
  simp only [smul_eq_mul, mul_add, Finset.mul_sum]
  have hs : (∑ j, (!![-1 / 2, 0, (1 / 8) * (1 - 27 * c p ^ 3)⁻¹;
      1, -3 / 2, (-13 / 4) * (1 - 27 * c p ^ 3)⁻¹;
      0, 1, (9 / 2) * (1 - 27 * c p ^ 3)⁻¹ - 5 / 2] :
      Matrix (Fin 3) (Fin 3) (K p)) i j * (a * v j)) =
      ∑ j, a * ((!![-1 / 2, 0, (1 / 8) * (1 - 27 * c p ^ 3)⁻¹;
      1, -3 / 2, (-13 / 4) * (1 - 27 * c p ^ 3)⁻¹;
      0, 1, (9 / 2) * (1 - 27 * c p ^ 3)⁻¹ - 5 / 2] :
      Matrix (Fin 3) (Fin 3) (K p)) i j * v j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  ring

theorem transport_injective (hp7 : 7 ≤ p) : Function.Injective (transport p hp7) := by
  intro v w h
  funext i
  exact sigma_injective p hp7 (congrFun h i)

theorem cConnection_transport (hp7 : 7 ≤ p) :
    cConnection p * transport p hp7 = transport p hp7 * WPToricGamma.gammaU p := by
  rw [cConnection_eq p hp7]
  apply LinearMap.ext
  intro v
  funext i
  rw [WPToricGamma.gammaU_actual p hp7]
  change theta p (sigma p hp7 (v i)) +
      ∑ j, sigma p hp7 (WPToricGamma.gammaM p i j) * sigma p hp7 (v j) =
    sigma p hp7 ((3 : ZMod p) • theta p (v i) +
      ∑ j, WPToricGamma.gammaM p i j * v j)
  rw [Algebra.smul_def, map_ofNat, map_add, map_mul, map_ofNat, theta_sigma, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact (map_mul _ _ _).symm

theorem cConnection_pcurvature_matrix (hp7 : 7 ≤ p) :
    cConnection p ^ p - cConnection p =
      matrixAction p (cG p hp7 * (-cJ p) * cGInverse p hp7) := by
  rw [cConnection_eq p hp7]
  exact cPsi_is_matrix p hp7

theorem actual_parameter_pcurvature_K_linear (hp7 : 7 ≤ p) (a : K p) (v : StateSpace p) :
    (cConnection p ^ p - cConnection p) (a • v) =
      a • (cConnection p ^ p - cConnection p) v := by
  rw [cConnection_eq p hp7]
  exact cPsi_K_linear p hp7 a v

end WPToricC
