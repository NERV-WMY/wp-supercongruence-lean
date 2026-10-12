import WPGammaURegular.Connection
import WPGammaBlocks.Polynomial

noncomputable section

namespace WPGammaURegular

open Polynomial

variable (p : ℕ) [Fact p.Prime]

def evaluate : Polynomial (ZMod p) →+* RegularEnd p :=
  Polynomial.eval₂RingHom' (algebraMap (ZMod p) (RegularEnd p)) (gammaNabla p)
    (fun a => Algebra.commute_algebraMap_left a (gammaNabla p))

theorem evaluate_X : evaluate p X=gammaNabla p := by
  change Polynomial.eval₂ _ _ X=_
  exact Polynomial.eval₂_X _ _

theorem evaluate_C (a : ZMod p) :
    evaluate p (C a)=algebraMap (ZMod p) (RegularEnd p) a := by
  change Polynomial.eval₂ _ _ (C a)=_
  exact Polynomial.eval₂_C _ _

theorem evaluate_factor (a : ZMod p) :
    evaluate p (X+C a)=gammaNabla p+algebraMap (ZMod p) (RegularEnd p) a := by
  rw [map_add, evaluate_X, evaluate_C]

theorem evaluate_primeCore : evaluate p (WPGammaBlocks.primeCore p)=gammaPsi p := by
  rw [WPGammaBlocks.primeCore, map_sub, map_pow, evaluate_X]
  rfl

def operatorProduct (a : ZMod p) (m : ℕ) : RegularEnd p :=
  ((List.range m).map fun j =>
    gammaNabla p+algebraMap (ZMod p) (RegularEnd p) (a+(j : ZMod p))).prod

theorem operatorProduct_evaluate (a : ZMod p) (m : ℕ) :
    operatorProduct p a m=evaluate p (WPGammaBlocks.product p a m) := by
  induction m with
  | zero => simp [operatorProduct, WPGammaBlocks.product]
  | succ m ih =>
    rw [WPGammaBlocks.product_succ, map_mul, evaluate_factor, ← ih]
    simp [operatorProduct, List.range_succ]

theorem operatorProduct_add (a : ZMod p) (m n : ℕ) :
    operatorProduct p a (m+n)=
      operatorProduct p a m*operatorProduct p (a+(m : ZMod p)) n := by
  simp only [operatorProduct_evaluate, WPGammaBlocks.product_add, map_mul]

theorem operatorProduct_five_prime (a : ZMod p) :
    operatorProduct p a (5*p)=gammaPsi p^5 := by
  rw [operatorProduct_evaluate, WPGammaBlocks.product_five_prime, map_pow,
    evaluate_primeCore]

theorem operatorProduct_five_prime_zero (hp7 : 7 ≤ p) (a : ZMod p) :
    operatorProduct p a (5*p)=0 := by
  rw [operatorProduct_five_prime]
  exact actual_regular_u_fifth_zero p hp7

theorem long_product_zero (hp7 : 7 ≤ p) (a : ZMod p) (m : ℕ) (hm : 5*p ≤ m) :
    operatorProduct p a m=0 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [operatorProduct_add, operatorProduct_five_prime_zero p hp7, zero_mul]

theorem surrounded_long_product_zero (hp7 : 7 ≤ p) (a : ZMod p)
    (m : ℕ) (hm : 5*p ≤ m) (A B : RegularEnd p) :
    A*operatorProduct p a m*B=0 := by
  rw [long_product_zero p hp7 a m hm, mul_zero, zero_mul]

end WPGammaURegular
