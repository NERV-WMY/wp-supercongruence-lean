import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic

open scoped BigOperators LaurentPolynomial
open LaurentPolynomial

namespace WPFiniteCartier

variable {R : Type*} [CommSemiring R]

private theorem index_injective (p : ℕ) (hp : 0 < p) :
    Function.Injective (fun k : ℤ => (p : ℤ) * (k + 1) - 1) := by
  intro k l h
  have hpz : 0 < (p : ℤ) := by omega
  nlinarith

/-- Finite coefficient selection on differentials: x^(pk+p-1)dx maps to x^k dx. -/
noncomputable def cartier (p : ℕ) (hp : 0 < p) (P : R[T;T⁻¹]) : R[T;T⁻¹] :=
  (AddMonoidAlgebra.coeffEquiv).symm
    (Finsupp.comapDomain (fun k : ℤ => (p : ℤ) * (k + 1) - 1) P.coeff
      (index_injective p hp).injOn)

@[simp] theorem cartier_coeff (p : ℕ) (hp : 0 < p) (P : R[T;T⁻¹]) (k : ℤ) :
    (cartier p hp P).coeff k = P.coeff ((p : ℤ) * (k + 1) - 1) := by
  rfl

theorem cartier_add (p : ℕ) (hp : 0 < p) (P Q : R[T;T⁻¹]) :
    cartier p hp (P + Q) = cartier p hp P + cartier p hp Q := by
  ext k
  simp only [cartier_coeff, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

theorem cartier_zero (p : ℕ) (hp : 0 < p) :
    cartier p hp (0 : R[T;T⁻¹]) = 0 := by
  ext k
  simp

theorem coefficient_monomial_mul (P : R[T;T⁻¹]) (a : R) (n k : ℤ) :
    (C a * T n * P).coeff k = a * P.coeff (k - n) := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  have hk : k = n + (k - n) := by ring
  conv_lhs => rw [hk]
  exact AddMonoidAlgebra.coeff_single_mul_add P a n (k - n)

/-- The complete finite selection commutes with every p-fold Laurent shift. -/
theorem cartier_monomial_shift (p : ℕ) (hp : 0 < p)
    (P : R[T;T⁻¹]) (a : R) (n : ℤ) :
    cartier p hp (C a * T ((p : ℤ) * n) * P) =
      C a * T n * cartier p hp P := by
  ext k
  simp only [cartier_coeff, coefficient_monomial_mul]
  congr 2
  ring

section PrimeField

theorem cartier_monomial_frobenius (p : ℕ) [Fact p.Prime]
    (P : (ZMod p)[T;T⁻¹]) (a : ZMod p) (n : ℤ) :
    cartier p (Fact.out : p.Prime).pos ((C a * T n) ^ p * P) =
      C a * T n * cartier p (Fact.out : p.Prime).pos P := by
  rw [mul_pow, ← map_pow, T_pow, ZMod.pow_card]
  simpa only [mul_comm (p : ℤ) n] using
    cartier_monomial_shift p (Fact.out : p.Prime).pos P a n

/-- The literal weighted selection used by NC66, for every finite Laurent source. -/
theorem cartier_frobenius_product (p : ℕ) [Fact p.Prime]
    (H P : (ZMod p)[T;T⁻¹]) :
    cartier p (Fact.out : p.Prime).pos (H ^ p * P) =
      H * cartier p (Fact.out : p.Prime).pos P := by
  have hC : Function.Injective (C : ZMod p →+* (ZMod p)[T;T⁻¹]) := by
    intro a b h
    have hc := congrArg (fun Q : (ZMod p)[T;T⁻¹] => Q.coeff 0) h
    simpa using hc
  let : CharP (ZMod p)[T;T⁻¹] p := charP_of_injective_ringHom hC p
  refine LaurentPolynomial.induction_on H ?_ ?_ ?_ ?_
  · intro a
    simpa only [T_zero, mul_one] using cartier_monomial_frobenius p P a 0
  · intro H J hH hJ
    rw [add_pow_char, add_mul, cartier_add, add_mul, hH, hJ]
  · intro n a _ih
    exact cartier_monomial_frobenius p P a (n + 1)
  · intro n a _ih
    exact cartier_monomial_frobenius p P a (-n - 1)

end PrimeField

/-- The selected differential monomial is retained with its exact quotient index. -/
theorem cartier_selected_monomial (p : ℕ) (hp : 0 < p) (a : R) (k : ℤ) :
    cartier p hp (C a * T ((p : ℤ) * (k + 1) - 1)) = C a * T k := by
  ext j
  simp only [cartier_coeff, ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp only [(index_injective p hp).eq_iff]

theorem cartier_unselected_monomial (p : ℕ) (hp : 0 < p) (a : R) (n : ℤ)
    (hn : ¬(p : ℤ) ∣ n + 1) :
    cartier p hp (C a * T n) = 0 := by
  ext k
  have hne : n ≠ (p : ℤ) * (k + 1) - 1 := by
    intro he
    apply hn
    exact ⟨k + 1, by linarith⟩
  simp only [cartier_coeff, ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hne,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

/-- Actual pullback of x^j dx under x=y²: the factor 2 and odd index are explicit. -/
noncomputable def quadraticPullback (P : R[T;T⁻¹]) : R[T;T⁻¹] :=
  C 2 * AddMonoidAlgebra.mapDomain (fun j : ℤ => 2 * j + 1) P

theorem quadraticPullback_zero : quadraticPullback (0 : R[T;T⁻¹]) = 0 := by
  simp [quadraticPullback]

theorem quadraticPullback_add (P Q : R[T;T⁻¹]) :
    quadraticPullback (P + Q) = quadraticPullback P + quadraticPullback Q := by
  simp only [quadraticPullback, AddMonoidAlgebra.mapDomain_add, mul_add]

theorem quadraticPullback_monomial (a : R) (n : ℤ) :
    quadraticPullback (C a * T n) = C (2 * a) * T (2 * n + 1) := by
  unfold quadraticPullback
  rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.mapDomain_single,
    LaurentPolynomial.single_eq_C_mul_T, ← mul_assoc, ← map_mul]

private theorem odd_divides_double (p a : ℤ) (hp : Odd p) :
    p ∣ 2 * a ↔ p ∣ a := by
  constructor
  · rintro ⟨z, hz⟩
    have hprod : Even (p * z) := by rw [← hz]; exact even_two_mul a
    have hpnot : ¬Even p := Int.not_even_iff_odd.mpr hp
    have hzEven : Even z := (Int.even_mul.mp hprod).resolve_left hpnot
    obtain ⟨v, hv⟩ := hzEven
    refine ⟨v, ?_⟩
    rw [hv] at hz
    nlinarith
  · rintro ⟨z, hz⟩
    refine ⟨2 * z, ?_⟩
    rw [hz]
    ring

theorem cartier_quadratic_monomial (p : ℕ) (hp : 0 < p) (hpodd : Odd p)
    (a : R) (n : ℤ) :
    cartier p hp (quadraticPullback (C a * T n)) =
      quadraticPullback (cartier p hp (C a * T n)) := by
  have hpzodd : Odd (p : ℤ) := by exact_mod_cast hpodd
  by_cases hn : (p : ℤ) ∣ n + 1
  · obtain ⟨b, hb⟩ := hn
    have hnindex : n = (p : ℤ) * ((b - 1) + 1) - 1 := by linarith
    have hquad : 2 * n + 1 = (p : ℤ) * ((2 * b - 1) + 1) - 1 := by nlinarith
    rw [quadraticPullback_monomial, hquad, cartier_selected_monomial,
      hnindex, cartier_selected_monomial, quadraticPullback_monomial]
    congr 2
    ring
  · have hnquad : ¬(p : ℤ) ∣ (2 * n + 1) + 1 := by
      intro hd
      apply hn
      apply (odd_divides_double (p : ℤ) (n + 1) hpzodd).mp
      convert hd using 1
      ring
    rw [quadraticPullback_monomial, cartier_unselected_monomial p hp _ _ hnquad,
      cartier_unselected_monomial p hp _ _ hn, quadraticPullback_zero]

/-- NC66's full quadratic differential pullback, including negative Laurent powers. -/
theorem cartier_quadratic_pullback (p : ℕ) (hp : 0 < p) (hpodd : Odd p)
    (P : R[T;T⁻¹]) :
    cartier p hp (quadraticPullback P) = quadraticPullback (cartier p hp P) := by
  refine LaurentPolynomial.induction_on P ?_ ?_ ?_ ?_
  · intro a
    simpa only [T_zero, mul_one] using cartier_quadratic_monomial p hp hpodd a 0
  · intro P Q hP hQ
    rw [quadraticPullback_add, cartier_add, cartier_add, quadraticPullback_add, hP, hQ]
  · intro n a _ih
    exact cartier_quadratic_monomial p hp hpodd a (n + 1)
  · intro n a _ih
    exact cartier_quadratic_monomial p hp hpodd a (-n - 1)

end WPFiniteCartier
