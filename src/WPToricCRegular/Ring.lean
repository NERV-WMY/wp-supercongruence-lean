import WPToricC
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

noncomputable section

namespace WPToricCRegular

open WPPsi

variable (p : ℕ) [Fact p.Prime]

def pole : K p := 1 - 27 * WPToricC.c p ^ 3

def coefficientRing : Subalgebra (ZMod p) (K p) :=
  Algebra.adjoin (ZMod p) {WPToricC.c p, (WPToricC.c p)⁻¹, (pole p)⁻¹}

abbrev R := coefficientRing p

theorem c_mem : WPToricC.c p ∈ coefficientRing p :=
  Algebra.subset_adjoin (by simp)

theorem c_inv_mem : (WPToricC.c p)⁻¹ ∈ coefficientRing p :=
  Algebra.subset_adjoin (by simp)

theorem pole_inv_mem : (pole p)⁻¹ ∈ coefficientRing p :=
  Algebra.subset_adjoin (by simp)

theorem pole_mem : pole p ∈ coefficientRing p :=
  (coefficientRing p).sub_mem (coefficientRing p).one_mem
    ((coefficientRing p).mul_mem ((coefficientRing p).natCast_mem 27)
      ((coefficientRing p).pow_mem (c_mem p) 3))

theorem c_nonzero : WPToricC.c p ≠ 0 := by
  intro h
  have he : polyMap p Polynomial.X = polyMap p 0 := by
    simpa only [WPToricC.c, map_zero] using h
  exact Polynomial.X_ne_zero ((IsFractionRing.injective (Polynomial (ZMod p)) (K p)) he)

theorem pole_nonzero (hp7 : 7 ≤ p) : pole p ≠ 0 := WPToricC.cubic_pole_nonzero p hp7

theorem theta_pole : theta p (pole p) = -81 * WPToricC.c p ^ 3 := by
  have h27 : theta p (27 : K p) = 0 := by
    simpa only [map_ofNat] using (theta p).map_algebraMap (27 : ZMod p)
  rw [pole, (theta p).map_sub, (theta p).map_one_eq_zero, (theta p).leibniz,
    (theta p).leibniz_pow, WPToricC.theta_c, h27]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, zero_sub]
  ring

theorem theta_mem (a : K p) (ha : a ∈ coefficientRing p) :
    theta p a ∈ coefficientRing p := by
  refine Algebra.adjoin_induction (p := fun a _ => theta p a ∈ coefficientRing p)
    ?_ ?_ ?_ ?_ ha
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · rw [WPToricC.theta_c]
      exact c_mem p
    · rw [(theta p).leibniz_inv, WPToricC.theta_c]
      change -(WPToricC.c p)⁻¹ ^ 2 * WPToricC.c p ∈ coefficientRing p
      exact (coefficientRing p).mul_mem
        ((coefficientRing p).neg_mem ((coefficientRing p).pow_mem (c_inv_mem p) 2))
        (c_mem p)
    · rw [(theta p).leibniz_inv, theta_pole]
      change -(pole p)⁻¹ ^ 2 * (-81 * WPToricC.c p ^ 3) ∈ coefficientRing p
      exact (coefficientRing p).mul_mem
        ((coefficientRing p).neg_mem ((coefficientRing p).pow_mem (pole_inv_mem p) 2))
        ((coefficientRing p).mul_mem
          ((coefficientRing p).neg_mem ((coefficientRing p).natCast_mem 81))
          ((coefficientRing p).pow_mem (c_mem p) 3))
  · intro a
    rw [(theta p).map_algebraMap]
    exact (coefficientRing p).zero_mem
  · intro a b _ _ ha hb
    rw [(theta p).map_add]
    exact (coefficientRing p).add_mem ha hb
  · intro a b ha hb hta htb
    rw [(theta p).leibniz]
    change a * theta p b + b * theta p a ∈ coefficientRing p
    exact (coefficientRing p).add_mem
      ((coefficientRing p).mul_mem ha htb) ((coefficientRing p).mul_mem hb hta)

def regularTheta : Derivation (ZMod p) (R p) (R p) where
  toFun a := ⟨theta p (a : K p), theta_mem p _ a.property⟩
  map_add' a b := by apply Subtype.ext; exact (theta p).map_add _ _
  map_smul' a b := by apply Subtype.ext; exact (theta p).map_smul _ _
  map_one_eq_zero' := by apply Subtype.ext; exact (theta p).map_one_eq_zero
  leibniz' a b := by apply Subtype.ext; exact (theta p).leibniz _ _

theorem regularTheta_val (a : R p) :
    (regularTheta p a : K p) = theta p (a : K p) := rfl

theorem regularTheta_iterate_val (n : ℕ) (a : R p) :
    ((regularTheta p)^[n] a : K p) = (theta p)^[n] (a : K p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', regularTheta_val, ih]

theorem regularTheta_prime (a : R p) : (regularTheta p)^[p] a = regularTheta p a := by
  apply Subtype.ext
  rw [regularTheta_iterate_val, regularTheta_val]
  exact theta_prime_field p _

def regularC : R p := ⟨WPToricC.c p, c_mem p⟩
def regularCInverse : R p := ⟨(WPToricC.c p)⁻¹, c_inv_mem p⟩
def regularPole : R p := 1 - 27 * regularC p ^ 3
def regularPoleInverse : R p := ⟨(pole p)⁻¹, pole_inv_mem p⟩

theorem regularPole_val : (regularPole p : K p) = pole p := by
  change (coefficientRing p).val (regularPole p) = _
  simp only [regularPole, map_sub, map_one, map_mul, map_pow, map_ofNat]
  rfl

theorem regularC_mul_inverse : regularC p * regularCInverse p = 1 := by
  apply Subtype.ext
  exact mul_inv_cancel₀ (c_nonzero p)

theorem regularC_inverse_mul : regularCInverse p * regularC p = 1 := by
  rw [mul_comm, regularC_mul_inverse]

theorem regularPole_mul_inverse (hp7 : 7 ≤ p) : regularPole p * regularPoleInverse p = 1 := by
  apply Subtype.ext
  change (regularPole p : K p) * (pole p)⁻¹ = 1
  rw [regularPole_val, mul_inv_cancel₀ (pole_nonzero p hp7)]

theorem regularPole_inverse_mul (hp7 : 7 ≤ p) : regularPoleInverse p * regularPole p = 1 := by
  rw [mul_comm, regularPole_mul_inverse p hp7]

end WPToricCRegular
