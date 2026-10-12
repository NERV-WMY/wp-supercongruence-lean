import WPToricCRegular
import WPGammaURegular.StepBlocks

noncomputable section

namespace WPToricCBlocks

open Polynomial

variable (p : ℕ) [Fact p.Prime]

abbrev RegularEnd := WPToricCRegular.RegularEnd p

def evaluate : Polynomial (ZMod p) →+* RegularEnd p :=
  Polynomial.eval₂RingHom' (algebraMap (ZMod p) (RegularEnd p))
    (WPToricCRegular.gammaNabla p)
    (fun a => Algebra.commute_algebraMap_left a (WPToricCRegular.gammaNabla p))

theorem evaluate_X : evaluate p X = WPToricCRegular.gammaNabla p := by
  change Polynomial.eval₂ _ _ X = _
  exact Polynomial.eval₂_X _ _

theorem evaluate_C (a : ZMod p) :
    evaluate p (C a) = algebraMap (ZMod p) (RegularEnd p) a := by
  change Polynomial.eval₂ _ _ (C a) = _
  exact Polynomial.eval₂_C _ _

theorem evaluate_factor (a : ZMod p) :
    evaluate p (X + C a) = WPToricCRegular.gammaNabla p +
      algebraMap (ZMod p) (RegularEnd p) a := by
  rw [map_add, evaluate_X, evaluate_C]

theorem evaluate_primeCore :
    evaluate p (WPGammaBlocks.primeCore p) = WPToricCRegular.gammaPsi p := by
  rw [WPGammaBlocks.primeCore, map_sub, map_pow, evaluate_X]
  rfl

def operatorProduct (a d : ZMod p) (m : ℕ) : RegularEnd p :=
  ((List.range m).map fun j => WPToricCRegular.gammaNabla p +
    algebraMap (ZMod p) (RegularEnd p) (a + d * (j : ZMod p))).prod

theorem operatorProduct_evaluate (a d : ZMod p) (m : ℕ) :
    operatorProduct p a d m =
      evaluate p (WPGammaURegular.steppedPolynomial p a d m) := by
  induction m with
  | zero => simp [operatorProduct, WPGammaURegular.steppedPolynomial]
  | succ m ih =>
    rw [WPGammaURegular.steppedPolynomial, Finset.prod_range_succ,
      map_mul, evaluate_factor]
    change _ = evaluate p (WPGammaURegular.steppedPolynomial p a d m) * _
    rw [← ih]
    simp [operatorProduct, List.range_succ]

theorem operatorProduct_add (a d : ZMod p) (m n : ℕ) :
    operatorProduct p a d (m+n) = operatorProduct p a d m *
      operatorProduct p (a+d*(m : ZMod p)) d n := by
  simp only [operatorProduct_evaluate, WPGammaURegular.steppedPolynomial_add, map_mul]

theorem operatorProduct_prime_multiples (a d : ZMod p) (hd : d ≠ 0) (n : ℕ) :
    operatorProduct p a d (p*n) = WPToricCRegular.gammaPsi p ^ n := by
  rw [operatorProduct_evaluate,
    WPGammaURegular.steppedPolynomial_prime_multiples p a d hd n,
    map_pow, evaluate_primeCore]

theorem operatorProduct_three_prime_zero (hp7 : 7 ≤ p)
    (a d : ZMod p) (hd : d ≠ 0) : operatorProduct p a d (3*p) = 0 := by
  rw [Nat.mul_comm 3 p, operatorProduct_prime_multiples p a d hd]
  exact WPToricCRegular.actual_regular_third_zero p hp7

theorem long_product_zero (hp7 : 7 ≤ p) (a d : ZMod p) (hd : d ≠ 0)
    (m : ℕ) (hm : 3*p ≤ m) : operatorProduct p a d m = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [operatorProduct_add, operatorProduct_three_prime_zero p hp7 a d hd, zero_mul]

theorem three_nonzero (hp7 : 7 ≤ p) : (3 : ZMod p) ≠ 0 := by
  intro hzero
  have hd := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
  have hle := Nat.le_of_dvd (by decide : 0 < 3) hd
  omega

theorem original_vertex_long_product_zero (hp7 : 7 ≤ p) (a : ZMod p)
    (m : ℕ) (hm : 3*p ≤ m) : operatorProduct p a (-3) m = 0 := by
  exact long_product_zero p hp7 a (-3) (neg_ne_zero.mpr (three_nonzero p hp7)) m hm

theorem half_shift_long_product_zero (hp7 : 7 ≤ p)
    (m : ℕ) (hm : 3*p ≤ m) : operatorProduct p (1/2) 1 m = 0 := by
  exact long_product_zero p hp7 (1/2) 1 one_ne_zero m hm

theorem surrounded_long_product_zero (hp7 : 7 ≤ p)
    (a d : ZMod p) (hd : d ≠ 0) (m : ℕ) (hm : 3*p ≤ m) (A B : RegularEnd p) :
    A * operatorProduct p a d m * B = 0 := by
  rw [long_product_zero p hp7 a d hd m hm, mul_zero, zero_mul]

end WPToricCBlocks
