import WPGammaURegular.Blocks

noncomputable section

namespace WPGammaURegular

open Polynomial

variable (p : ℕ) [Fact p.Prime]

def steppedPolynomial (a d : ZMod p) (m : ℕ) : Polynomial (ZMod p) :=
  ∏ j ∈ Finset.range m, (X+C (a+d*(j : ZMod p)))

theorem stepped_residue_bijective (a d : ZMod p) (hd : d ≠ 0) :
    Function.Bijective (fun k : Fin p => -(a+d*(k.val : ZMod p))) := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  constructor
  · intro k l h
    have he : d*(k.val : ZMod p)=d*(l.val : ZMod p) :=
      add_left_cancel (neg_injective h)
    have hv := congrArg ZMod.val (mul_left_cancel₀ hd he)
    rw [ZMod.val_natCast_of_lt k.isLt, ZMod.val_natCast_of_lt l.isLt] at hv
    exact Fin.ext hv
  · intro b
    refine ⟨⟨((-b-a)/d).val, ZMod.val_lt _⟩, ?_⟩
    simp only [ZMod.natCast_zmod_val]
    field_simp
    ring

theorem steppedPolynomial_prime (a d : ZMod p) (hd : d ≠ 0) :
    steppedPolynomial p a d p=WPGammaBlocks.primeCore p := by
  calc
    steppedPolynomial p a d p=
        ∏ k : Fin p, (X+C (a+d*(k.val : ZMod p))) := by
      exact (Fin.prod_univ_eq_prod_range _ _).symm
    _ = ∏ b : ZMod p, (X-C b : Polynomial (ZMod p)) := by
      apply Fintype.prod_bijective (fun k : Fin p => -(a+d*(k.val : ZMod p)))
        (stepped_residue_bijective p a d hd)
      intro k
      simp
      ring
    _ = _ := WPFiveFactor.prime_field_factorization p Fact.out

theorem steppedPolynomial_add (a d : ZMod p) (m n : ℕ) :
    steppedPolynomial p a d (m+n)=
      steppedPolynomial p a d m*steppedPolynomial p (a+d*(m : ZMod p)) d n := by
  unfold steppedPolynomial
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp only [Nat.cast_add]
  congr 2
  ring

theorem steppedPolynomial_prime_multiples (a d : ZMod p) (hd : d ≠ 0) (n : ℕ) :
    steppedPolynomial p a d (p*n)=WPGammaBlocks.primeCore p^n := by
  induction n with
  | zero => simp [steppedPolynomial]
  | succ n ih =>
    rw [Nat.mul_succ, steppedPolynomial_add, ih, steppedPolynomial_prime p _ d hd,
      pow_succ]

def steppedOperatorProduct (a d : ZMod p) (m : ℕ) : RegularEnd p :=
  ((List.range m).map fun j =>
    gammaNabla p+algebraMap (ZMod p) (RegularEnd p) (a+d*(j : ZMod p))).prod

theorem steppedOperatorProduct_evaluate (a d : ZMod p) (m : ℕ) :
    steppedOperatorProduct p a d m=evaluate p (steppedPolynomial p a d m) := by
  induction m with
  | zero => simp [steppedOperatorProduct, steppedPolynomial]
  | succ m ih =>
    rw [steppedPolynomial, Finset.prod_range_succ, map_mul, evaluate_factor]
    change _=evaluate p (steppedPolynomial p a d m)*_
    rw [← ih]
    simp [steppedOperatorProduct, List.range_succ]

theorem steppedOperatorProduct_add (a d : ZMod p) (m n : ℕ) :
    steppedOperatorProduct p a d (m+n)=
      steppedOperatorProduct p a d m*steppedOperatorProduct p (a+d*(m : ZMod p)) d n := by
  simp only [steppedOperatorProduct_evaluate, steppedPolynomial_add, map_mul]

theorem steppedOperatorProduct_five_prime_zero (hp7 : 7 ≤ p)
    (a d : ZMod p) (hd : d ≠ 0) : steppedOperatorProduct p a d (5*p)=0 := by
  rw [steppedOperatorProduct_evaluate]
  have he := steppedPolynomial_prime_multiples p a d hd 5
  rw [Nat.mul_comm p 5] at he
  rw [he, map_pow, evaluate_primeCore]
  exact actual_regular_u_fifth_zero p hp7

theorem stepped_long_product_zero (hp7 : 7 ≤ p) (a d : ZMod p) (hd : d ≠ 0)
    (m : ℕ) (hm : 5*p ≤ m) : steppedOperatorProduct p a d m=0 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [steppedOperatorProduct_add, steppedOperatorProduct_five_prime_zero p hp7 a d hd,
    zero_mul]

theorem original_vertex_long_product_zero (hp7 : 7 ≤ p) (a : ZMod p)
    (m : ℕ) (hm : 5*p ≤ m) : steppedOperatorProduct p a (-6) m=0 := by
  apply stepped_long_product_zero p hp7 a (-6) _ m hm
  exact neg_ne_zero.mpr (WPFiveFactor.six_unit p Fact.out hp7).ne_zero

theorem stepped_surrounded_long_product_zero (hp7 : 7 ≤ p)
    (a d : ZMod p) (hd : d ≠ 0) (m : ℕ) (hm : 5*p ≤ m) (A B : RegularEnd p) :
    A*steppedOperatorProduct p a d m*B=0 := by
  rw [stepped_long_product_zero p hp7 a d hd m hm, mul_zero, zero_mul]

end WPGammaURegular
