import WPToricCRegular.Ring

noncomputable section

namespace WPToricCRegular

open WPPsi

variable (p : ℕ) [Fact p.Prime]

abbrev RegularSpace := Fin 3 → R p
abbrev RegularEnd := Module.End (ZMod p) (RegularSpace p)

def fraction (n d : ℕ) : R p := algebraMap (ZMod p) (R p) ((n : ZMod p) / (d : ZMod p))

def gammaM : Matrix (Fin 3) (Fin 3) (R p) :=
  !![-fraction p 1 2, 0, fraction p 1 8 * regularPoleInverse p;
      1, -fraction p 3 2, -fraction p 13 4 * regularPoleInverse p;
      0, 1, fraction p 9 2 * regularPoleInverse p - fraction p 5 2]

def fieldM : Matrix (Fin 3) (Fin 3) (K p) :=
  !![-1 / 2, 0, (1 / 8) * (pole p)⁻¹;
      1, -3 / 2, (-13 / 4) * (pole p)⁻¹;
      0, 1, (9 / 2) * (pole p)⁻¹ - 5 / 2]

theorem fraction_val (n d : ℕ) : (fraction p n d : K p) = (n : K p) / (d : K p) := by
  change algebraMap (ZMod p) (K p) ((n : ZMod p) / (d : ZMod p)) = _
  rw [map_div₀, map_natCast, map_natCast]

theorem gammaM_val (i j : Fin 3) : (gammaM p i j : K p) = fieldM p i j := by
  fin_cases i <;> fin_cases j <;>
    simp [gammaM, fieldM, fraction_val, regularPoleInverse]
  all_goals norm_cast
  all_goals norm_num
  all_goals ring

theorem fieldM_eq_actual (hp7 : 7 ≤ p) : fieldM p = WPToricC.cM p hp7 := by
  rw [WPToricC.cM_literal]
  rfl

def liftVector : RegularSpace p →ₗ[ZMod p] WPToricPsi.StateSpace p where
  toFun v := fun i => (v i : K p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem liftVector_injective : Function.Injective (liftVector p) := by
  intro v w h
  funext i
  apply Subtype.ext
  exact congrFun h i

theorem liftVector_smul (a : R p) (v : RegularSpace p) :
    liftVector p (a • v) = (a : K p) • liftVector p v := rfl

def euler : RegularEnd p where
  toFun v := fun i => regularTheta p (v i)
  map_add' v w := by funext i; exact map_add (regularTheta p) (v i) (w i)
  map_smul' a v := by funext i; exact (regularTheta p).map_smul a (v i)

def matrixAction (M : Matrix (Fin 3) (Fin 3) (R p)) : RegularEnd p :=
  M.mulVecLin.restrictScalars (ZMod p)

def gammaNabla : RegularEnd p := euler p + matrixAction p (gammaM p)
def gammaPsi : RegularEnd p := gammaNabla p ^ p - gammaNabla p

theorem euler_pow_entry (n : ℕ) (v : RegularSpace p) (i : Fin 3) :
    (euler p ^ n) v i = (regularTheta p)^[n] (v i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    change regularTheta p ((euler p ^ n) v i) = _
    rw [ih, Function.iterate_succ_apply']

theorem euler_prime : euler p ^ p = euler p := by
  apply LinearMap.ext
  intro v
  funext i
  rw [euler_pow_entry]
  exact regularTheta_prime p _

theorem liftVector_euler (v : RegularSpace p) :
    liftVector p (euler p v) = WPToricPsi.euler p (liftVector p v) := rfl

theorem liftVector_matrix (v : RegularSpace p) :
    liftVector p (matrixAction p (gammaM p) v) =
      WPToricPsi.matrixAction p (fieldM p) (liftVector p v) := by
  funext i
  change (coefficientRing p).val (∑ j, gammaM p i j * v j) =
    ∑ j, fieldM p i j * (v j : K p)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul]
  change (gammaM p i j : K p) * (v j : K p) = _
  rw [gammaM_val]

theorem gammaNabla_intertwines (v : RegularSpace p) :
    liftVector p (gammaNabla p v) = WPToricC.cConnection p (liftVector p v) := by
  change liftVector p (euler p v + matrixAction p (gammaM p) v) = _
  rw [map_add, liftVector_euler, liftVector_matrix]
  rfl

theorem gammaNabla_power_intertwines (n : ℕ) (v : RegularSpace p) :
    liftVector p ((gammaNabla p ^ n) v) =
      (WPToricC.cConnection p ^ n) (liftVector p v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, gammaNabla_intertwines, ih,
      pow_succ', Module.End.mul_apply]

theorem gammaPsi_intertwines (v : RegularSpace p) :
    liftVector p (gammaPsi p v) =
      (WPToricC.cConnection p ^ p - WPToricC.cConnection p) (liftVector p v) := by
  change liftVector p ((gammaNabla p ^ p) v - gammaNabla p v) = _
  rw [map_sub, gammaNabla_power_intertwines, gammaNabla_intertwines]
  rfl

theorem gammaPsi_power_intertwines (n : ℕ) (v : RegularSpace p) :
    liftVector p ((gammaPsi p ^ n) v) =
      ((WPToricC.cConnection p ^ p - WPToricC.cConnection p) ^ n) (liftVector p v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, gammaPsi_intertwines, ih,
      pow_succ', Module.End.mul_apply]

theorem actual_regular_third_zero (hp7 : 7 ≤ p) :
    (gammaNabla p ^ p - gammaNabla p) ^ 3 = 0 := by
  change gammaPsi p ^ 3 = 0
  apply LinearMap.ext
  intro v
  apply liftVector_injective p
  rw [gammaPsi_power_intertwines, WPToricC.actual_parameter_connection_third_zero p hp7]
  rfl

theorem gammaNabla_leibniz (a : R p) (v : RegularSpace p) :
    gammaNabla p (a • v) = regularTheta p a • v + a • gammaNabla p v := by
  apply liftVector_injective p
  rw [gammaNabla_intertwines, liftVector_smul, WPToricC.cConnection_leibniz,
    map_add, liftVector_smul, liftVector_smul, gammaNabla_intertwines]
  rfl

theorem gammaPsi_R_linear (hp7 : 7 ≤ p) (a : R p) (v : RegularSpace p) :
    gammaPsi p (a • v) = a • gammaPsi p v := by
  apply liftVector_injective p
  rw [gammaPsi_intertwines, liftVector_smul,
    WPToricC.actual_parameter_pcurvature_K_linear p hp7,
    liftVector_smul, gammaPsi_intertwines]

end WPToricCRegular
