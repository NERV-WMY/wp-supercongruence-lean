import WPGammaU
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

noncomputable section

namespace WPGammaURegular

open WPPsi

variable (p : ℕ) [Fact p.Prime]

def coefficientRing : Subalgebra (ZMod p) (K p) :=
  Algebra.adjoin (ZMod p) {WPGammaU.u p, (WPGammaU.u p)⁻¹, (WPGammaU.delta p)⁻¹}

abbrev R := coefficientRing p

theorem u_mem : WPGammaU.u p ∈ coefficientRing p :=
  Algebra.subset_adjoin (by simp)

theorem u_inv_mem : (WPGammaU.u p)⁻¹ ∈ coefficientRing p :=
  Algebra.subset_adjoin (by simp)

theorem delta_inv_mem : (WPGammaU.delta p)⁻¹ ∈ coefficientRing p :=
  Algebra.subset_adjoin (by simp)

theorem six_mem : (6 : K p) ∈ coefficientRing p := by
  simpa only [map_ofNat] using (coefficientRing p).algebraMap_mem (6 : ZMod p)

theorem z_mem : WPGammaU.z p ∈ coefficientRing p :=
  (coefficientRing p).pow_mem ((coefficientRing p).mul_mem (six_mem p) (u_mem p)) 6

theorem theta_delta : theta p (WPGammaU.delta p)=-6*WPGammaU.z p := by
  rw [WPGammaU.delta, (theta p).map_sub, (theta p).map_one_eq_zero,
    WPGammaU.theta_z]
  ring

theorem theta_mem (a : K p) (ha : a ∈ coefficientRing p) :
    theta p a ∈ coefficientRing p := by
  refine Algebra.adjoin_induction (p := fun a _ => theta p a ∈ coefficientRing p)
    ?_ ?_ ?_ ?_ ha
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · rw [WPGammaU.theta_u]
      exact u_mem p
    · rw [(theta p).leibniz_inv, WPGammaU.theta_u]
      change -(WPGammaU.u p)⁻¹ ^ 2 * WPGammaU.u p ∈ coefficientRing p
      exact (coefficientRing p).mul_mem
        ((coefficientRing p).neg_mem ((coefficientRing p).pow_mem (u_inv_mem p) 2))
        (u_mem p)
    · rw [(theta p).leibniz_inv, theta_delta]
      change -(WPGammaU.delta p)⁻¹ ^ 2 * (-6*WPGammaU.z p) ∈ coefficientRing p
      exact (coefficientRing p).mul_mem
        ((coefficientRing p).neg_mem ((coefficientRing p).pow_mem (delta_inv_mem p) 2))
        ((coefficientRing p).mul_mem ((coefficientRing p).neg_mem (six_mem p)) (z_mem p))
  · intro a
    rw [(theta p).map_algebraMap]
    exact (coefficientRing p).zero_mem
  · intro a b _ _ ha hb
    rw [(theta p).map_add]
    exact (coefficientRing p).add_mem ha hb
  · intro a b ha hb hta htb
    rw [(theta p).leibniz]
    change a*theta p b+b*theta p a ∈ coefficientRing p
    exact (coefficientRing p).add_mem
      ((coefficientRing p).mul_mem ha htb) ((coefficientRing p).mul_mem hb hta)

def regularTheta : Derivation (ZMod p) (R p) (R p) where
  toFun a := ⟨theta p (a : K p), theta_mem p _ a.property⟩
  map_add' a b := by apply Subtype.ext; exact (theta p).map_add _ _
  map_smul' a b := by apply Subtype.ext; exact (theta p).map_smul _ _
  map_one_eq_zero' := by apply Subtype.ext; exact (theta p).map_one_eq_zero
  leibniz' a b := by apply Subtype.ext; exact (theta p).leibniz _ _

theorem regularTheta_val (a : R p) :
    (regularTheta p a : K p)=theta p (a : K p) := rfl

theorem regularTheta_iterate_val (n : ℕ) (a : R p) :
    ((regularTheta p)^[n] a : K p)=(theta p)^[n] (a : K p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', regularTheta_val, ih]

theorem regularTheta_prime (a : R p) : (regularTheta p)^[p] a=regularTheta p a := by
  apply Subtype.ext
  rw [regularTheta_iterate_val, regularTheta_val]
  exact theta_prime_field p _

end WPGammaURegular
