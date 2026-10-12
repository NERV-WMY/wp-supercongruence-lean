import WPGamma

noncomputable section

namespace WPGammaBlocks

open Polynomial

variable (p : ℕ) [Fact p.Prime]

def product (α : ZMod p) (m : ℕ) : Polynomial (ZMod p) :=
  ∏ j ∈ Finset.range m, (X + C (α + (j : ZMod p)))

def primeCore : Polynomial (ZMod p) := X ^ p - X

theorem product_zero (α : ZMod p) : product p α 0 = 1 := by
  simp [product]

theorem product_succ (α : ZMod p) (m : ℕ) :
    product p α (m + 1) = product p α m * (X + C (α + (m : ZMod p))) := by
  exact Finset.prod_range_succ _ _

theorem product_add (α : ZMod p) (m n : ℕ) :
    product p α (m + n) = product p α m * product p (α + (m : ZMod p)) n := by
  unfold product
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp [Nat.cast_add, add_assoc]

theorem product_prime (α : ZMod p) : product p α p = primeCore p := by
  have h := WPFiveFactor.pBlock_exact p (Fact.out : p.Prime) α
  change (∏ k : Fin p, (X + C (α + (k.val : ZMod p)))) = primeCore p at h
  have hh := Fin.prod_univ_eq_prod_range (fun k : ℕ => (X + C (α + (k : ZMod p)))) p
  exact hh.symm.trans h

theorem product_prime_multiples (α : ZMod p) (n : ℕ) :
    product p α (p * n) = primeCore p ^ n := by
  induction n with
  | zero => simp [product]
  | succ n ih =>
    rw [Nat.mul_succ, product_add, ih, product_prime, pow_succ]

theorem product_five_prime (α : ZMod p) :
    product p α (5 * p) = primeCore p ^ 5 := by
  simpa only [Nat.mul_comm p 5] using product_prime_multiples p α 5

theorem product_five_prime_shifted (α : ZMod p) (s : ℕ) :
    product p (α + (s : ZMod p)) (5 * p) = (X ^ p - X : Polynomial (ZMod p)) ^ 5 :=
  product_five_prime p _

theorem five_prime_multiple_residue (q : ℕ) : ((5 * p * q : ℕ) : ZMod p) = 0 := by
  simp [Nat.cast_mul]

theorem product_factorization (α : ZMod p) (q r : ℕ) :
    product p α (5 * p * q + r) = (primeCore p ^ 5) ^ q * product p α r := by
  rw [product_add, five_prime_multiple_residue, add_zero]
  have hmul : 5 * p * q = p * (5 * q) := by ring
  rw [hmul, product_prime_multiples, pow_mul]

theorem product_division_factorization (α : ZMod p) (m : ℕ) :
    product p α m = (primeCore p ^ 5) ^ (m / (5 * p)) * product p α (m % (5 * p)) := by
  have h := product_factorization p α (m / (5 * p)) (m % (5 * p))
  simpa only [Nat.div_add_mod] using h

theorem division_remainder_bound (m : ℕ) : m % (5 * p) < 5 * p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  exact Nat.mod_lt _ (by omega)

theorem two_unit (hp7 : 7 ≤ p) : IsUnit (2 : ZMod p) := by
  apply (ZMod.isUnit_iff_coprime 2 p).mpr
  apply Nat.Coprime.symm
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hd
  have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
  omega

theorem half_shift_normalized (hp7 : 7 ≤ p) : (2 : ZMod p) * (1 / 2 : ZMod p) = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := (two_unit p hp7).ne_zero
  simp [h2]

end WPGammaBlocks
