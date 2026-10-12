import WPGammaURegular.Ring

noncomputable section

namespace WPGammaURegular

open WPPsi

variable (p : ℕ) [Fact p.Prime]

abbrev RegularSpace := Fin 5 → R p
abbrev RegularEnd := Module.End (ZMod p) (RegularSpace p)

def deltaInverse : R p := ⟨(WPGammaU.delta p)⁻¹, delta_inv_mem p⟩

def gammaM : Matrix (Fin 5) (Fin 5) (R p) :=
  !![-1, 0, 0, 0, deltaInverse p;
     1, -2, 0, 0, -31*deltaInverse p;
     0, 1, -3, 0, 90*deltaInverse p;
     0, 0, 1, -4, -65*deltaInverse p;
     0, 0, 0, 1, 15*deltaInverse p-5]

theorem gammaM_val (i j : Fin 5) :
    (gammaM p i j : K p)=WPGammaU.literalGammaM p i j := by
  fin_cases i <;> fin_cases j <;>
    simp [gammaM, WPGammaU.literalGammaM, deltaInverse]
  all_goals norm_cast
  all_goals apply Or.inl; norm_cast

def liftVector : RegularSpace p →ₗ[ZMod p] StateSpace p where
  toFun v := fun i => (v i : K p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem liftVector_injective : Function.Injective (liftVector p) := by
  intro v w h
  funext i
  apply Subtype.ext
  exact congrFun h i

def euler : RegularEnd p where
  toFun v := fun i => regularTheta p (v i)
  map_add' v w := by funext i; exact map_add (regularTheta p) (v i) (w i)
  map_smul' a v := by funext i; exact (regularTheta p).map_smul a (v i)

def matrixAction (M : Matrix (Fin 5) (Fin 5) (R p)) : RegularEnd p :=
  M.mulVecLin.restrictScalars (ZMod p)

def gammaNabla : RegularEnd p := euler p+matrixAction p (gammaM p)
def gammaPsi : RegularEnd p := gammaNabla p^p-gammaNabla p

theorem gammaNabla_leibniz (a : R p) (v : RegularSpace p) :
    gammaNabla p (a • v)=regularTheta p a • v+a • gammaNabla p v := by
  funext i
  change regularTheta p (a*v i)+(∑ j, gammaM p i j*(a*v j))=
    regularTheta p a*v i+a*(regularTheta p (v i)+∑ j, gammaM p i j*v j)
  rw [(regularTheta p).leibniz]
  simp only [smul_eq_mul, mul_add, Finset.mul_sum]
  have hs : (∑ j, gammaM p i j*(a*v j))=∑ j, a*(gammaM p i j*v j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  ring

theorem liftVector_euler (v : RegularSpace p) :
    liftVector p (euler p v)=WPPsi.euler p (liftVector p v) := rfl

theorem liftVector_matrix (v : RegularSpace p) :
    liftVector p (matrixAction p (gammaM p) v)=
      WPPsi.matrixAction p (WPGammaU.literalGammaM p) (liftVector p v) := by
  funext i
  change (coefficientRing p).val (∑ j, gammaM p i j*v j)=
    ∑ j, WPGammaU.literalGammaM p i j*(v j : K p)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul]
  change (gammaM p i j : K p)*(v j : K p)=_
  rw [gammaM_val]

theorem gammaNabla_intertwines (v : RegularSpace p) :
    liftVector p (gammaNabla p v)=WPGammaU.literalNabla p (liftVector p v) := by
  change liftVector p (euler p v+matrixAction p (gammaM p) v)=_
  rw [map_add, liftVector_euler, liftVector_matrix]
  rfl

theorem gammaNabla_power_intertwines (n : ℕ) (v : RegularSpace p) :
    liftVector p ((gammaNabla p^n) v)=
      (WPGammaU.literalNabla p^n) (liftVector p v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, gammaNabla_intertwines, ih,
      pow_succ', Module.End.mul_apply]

theorem gammaPsi_intertwines (v : RegularSpace p) :
    liftVector p (gammaPsi p v)=
      (WPGammaU.literalNabla p^p-WPGammaU.literalNabla p) (liftVector p v) := by
  change liftVector p ((gammaNabla p^p) v-gammaNabla p v)=_
  rw [map_sub, gammaNabla_power_intertwines, gammaNabla_intertwines]
  rfl

theorem gammaPsi_power_intertwines (n : ℕ) (v : RegularSpace p) :
    liftVector p ((gammaPsi p^n) v)=
      ((WPGammaU.literalNabla p^p-WPGammaU.literalNabla p)^n) (liftVector p v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, gammaPsi_intertwines, ih,
      pow_succ', Module.End.mul_apply]

theorem actual_regular_u_fifth_zero (hp7 : 7 ≤ p) :
    (gammaNabla p^p-gammaNabla p)^5=0 := by
  change gammaPsi p^5=0
  apply LinearMap.ext
  intro v
  apply liftVector_injective p
  rw [gammaPsi_power_intertwines, WPGammaU.actual_literal_u_fifth_zero p hp7]
  rfl

end WPGammaURegular
