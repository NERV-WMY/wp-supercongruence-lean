import WPFiveFactor.Terminal

noncomputable section

namespace WPFiveFactor

open Polynomial

theorem residue_enumeration_bijective (p : ℕ) (hp : p.Prime) (a : ZMod p) :
    Function.Bijective (fun k : Fin p => -(a + (k.val : ZMod p))) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · intro k l hkl
    have heq : (k.val : ZMod p) = (l.val : ZMod p) := add_left_cancel (neg_injective hkl)
    have hval := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt k.isLt, ZMod.val_natCast_of_lt l.isLt] at hval
    exact Fin.ext hval
  · intro b
    refine ⟨⟨(-b - a).val, ZMod.val_lt (-b - a)⟩, ?_⟩
    simp

theorem prime_field_factorization (p : ℕ) [NeZero p] (hp : p.Prime) :
    (∏ a : ZMod p, (X - C a : Polynomial (ZMod p))) = X ^ p - X := by
  let : Fact p.Prime := ⟨hp⟩
  have hr : (X ^ p - X : Polynomial (ZMod p)).roots = Finset.univ.val := by
    simpa only [ZMod.card] using FiniteField.roots_X_pow_card_sub_X (ZMod p)
  have hd : (X ^ p - X : Polynomial (ZMod p)).natDegree = p :=
    FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp.one_lt
  have hm : (X ^ p - X : Polynomial (ZMod p)).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast hp.one_lt
  have hc : (X ^ p - X : Polynomial (ZMod p)).roots.card =
      (X ^ p - X : Polynomial (ZMod p)).natDegree := by
    rw [hr, hd]
    simp [ZMod.card]
  have heq := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hc
  rw [hr] at heq
  exact heq

theorem pBlock_exact (p : ℕ) (hp : p.Prime) (a : ZMod p) :
    pBlock p a = (X : Polynomial (ZMod p)) ^ p - X := by
  let : Fact p.Prime := ⟨hp⟩
  calc
    pBlock p a = ∏ b : ZMod p, (X - C b : Polynomial (ZMod p)) := by
      apply Fintype.prod_bijective (fun k : Fin p => -(a + (k.val : ZMod p)))
        (residue_enumeration_bijective p hp a)
      intro k
      simp
      ring
    _ = _ := prime_field_factorization p hp

theorem pBlock_zero_exact (p : ℕ) (hp : p.Prime) :
    pBlock p 0 = (X : Polynomial (ZMod p)) ^ p - X := by
  exact pBlock_exact p hp 0

theorem five_factor_exact (p : ℕ) (hp : p.Prime) :
    fiveFactorBlock p = ((X : Polynomial (ZMod p)) ^ p - X) ^ 5 := by
  simp [fiveFactorBlock, pBlock_exact p hp]

end WPFiveFactor
