import WPState.FieldGauge
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Polynomial.Derivation

noncomputable section

namespace WPPsi

open Polynomial

variable (p : ℕ) [Fact p.Prime]

abbrev K := WPState.RationalField p

def polyMap : Polynomial (ZMod p) →+* K p := algebraMap _ _

def polyJet : Polynomial (ZMod p) →+* TrivSqZeroExt (K p) (K p) where
  toFun P := ⟨polyMap p P, polyMap p (WPRho.theta P)⟩
  map_one' := by apply TrivSqZeroExt.ext <;> simp [WPRho.theta, polyMap]
  map_zero' := by apply TrivSqZeroExt.ext <;> simp [WPRho.theta, polyMap]
  map_add' P Q := by
    apply TrivSqZeroExt.ext
    · change polyMap p (P + Q) = polyMap p P + polyMap p Q
      exact map_add _ _ _
    · change polyMap p (WPRho.theta (P + Q)) =
        polyMap p (WPRho.theta P) + polyMap p (WPRho.theta Q)
      simp [WPRho.theta, derivative_add, mul_add]
  map_mul' P Q := by
    apply TrivSqZeroExt.ext
    · change polyMap p (P * Q) = polyMap p P * polyMap p Q
      exact map_mul _ _ _
    · change polyMap p (WPRho.theta (P * Q)) =
        polyMap p P * polyMap p (WPRho.theta Q) + polyMap p (WPRho.theta P) * polyMap p Q
      simp [WPRho.theta, derivative_mul, mul_add]
      ring

theorem polyJet_unit (s : nonZeroDivisors (Polynomial (ZMod p))) :
    IsUnit (polyJet p s) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  apply isUnit_iff_ne_zero.mpr
  change polyMap p (s : Polynomial (ZMod p)) ≠ 0
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.property

def fieldJet : K p →+* TrivSqZeroExt (K p) (K p) :=
  IsLocalization.lift (S := K p) (polyJet_unit p)

theorem fieldJet_poly (P : Polynomial (ZMod p)) :
    fieldJet p (polyMap p P) = polyJet p P :=
  IsLocalization.lift_eq (polyJet_unit p) P

theorem fieldJet_fst (a : K p) : (fieldJet p a).fst = a := by
  have he : (TrivSqZeroExt.fstHom (K p) (K p) (K p)).toRingHom.comp (fieldJet p) =
      RingHom.id (K p) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial (ZMod p)))
    apply RingHom.ext
    intro P
    simp only [RingHom.comp_apply, RingHom.id_apply]
    change (fieldJet p (polyMap p P)).fst = polyMap p P
    rw [fieldJet_poly]
    rfl
  exact RingHom.congr_fun he a

def thetaFun (a : K p) : K p := (fieldJet p a).snd

theorem thetaFun_add (a b : K p) : thetaFun p (a + b) = thetaFun p a + thetaFun p b := by
  simp [thetaFun, map_add]

theorem thetaFun_mul (a b : K p) :
    thetaFun p (a * b) = a * thetaFun p b + b * thetaFun p a := by
  simp only [thetaFun, map_mul, TrivSqZeroExt.snd_mul, fieldJet_fst]
  change a * (fieldJet p b).snd + (fieldJet p a).snd * b = _
  rw [mul_comm ((fieldJet p a).snd) b]

theorem thetaFun_poly (P : Polynomial (ZMod p)) :
    thetaFun p (polyMap p P) = polyMap p (WPRho.theta P) := by
  rw [thetaFun, fieldJet_poly]
  rfl

theorem thetaFun_base (a : ZMod p) : thetaFun p (algebraMap (ZMod p) (K p) a) = 0 := by
  have he : algebraMap (ZMod p) (K p) a = polyMap p (C a) := by
    simp [polyMap, IsScalarTower.algebraMap_apply (ZMod p) (Polynomial (ZMod p)) (K p)]
  rw [he, thetaFun_poly]
  simp [WPRho.theta]

def theta : Derivation (ZMod p) (K p) (K p) where
  toFun := thetaFun p
  map_add' := thetaFun_add p
  map_smul' a b := by
    simp only [Algebra.smul_def]
    rw [thetaFun_mul, thetaFun_base]
    simp
  map_one_eq_zero' := by simp [thetaFun]
  leibniz' a b := by
    simp only [smul_eq_mul]
    exact thetaFun_mul p a b

theorem theta_poly (P : Polynomial (ZMod p)) :
    theta p (polyMap p P) = polyMap p (WPRho.theta P) := thetaFun_poly p P

theorem theta_pth_power (a : K p) : theta p (a ^ p) = 0 := by
  rw [(theta p).leibniz_pow]
  simp [nsmul_eq_mul, smul_eq_mul, CharP.cast_eq_zero]

theorem theta_iterate_div_poly (P Q : Polynomial (ZMod p)) (m : ℕ)
    (hQ : theta p (polyMap p Q) = 0) :
    (theta p)^[m] (polyMap p P / polyMap p Q) =
      polyMap p ((WPRho.theta)^[m] P) / polyMap p Q := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, (theta p).leibniz_div_const _ _ hQ,
      theta_poly, Function.iterate_succ_apply']
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem fraction_pth_denominator (P Q : Polynomial (ZMod p)) (hQ : Q ≠ 0) :
    polyMap p P / polyMap p Q =
      polyMap p (P * Q ^ (p - 1)) / polyMap p (Q ^ p) := by
  have hq : polyMap p Q ≠ 0 := by
    simpa only [polyMap, map_zero] using
      (IsFractionRing.injective (Polynomial (ZMod p)) (K p)).ne hQ
  have hp : p = (p - 1) + 1 := by have := (Fact.out : p.Prime).pos; omega
  simp only [map_mul, map_pow]
  apply (div_eq_div_iff hq (pow_ne_zero p hq)).mpr
  have hpow : (polyMap p Q) ^ p = (polyMap p Q) ^ (p - 1) * polyMap p Q :=
    (congrArg (fun n : ℕ => (polyMap p Q) ^ n) hp).trans (pow_succ _ _)
  rw [hpow]
  ring

theorem theta_prime_field (a : K p) : (theta p)^[p] a = theta p a := by
  obtain ⟨P, Q, hQ, rfl⟩ := IsFractionRing.div_surjective (Polynomial (ZMod p)) a
  have hq : Q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hQ
  change (theta p)^[p] (polyMap p P / polyMap p Q) =
    theta p (polyMap p P / polyMap p Q)
  rw [fraction_pth_denominator p P Q hq]
  have hpow : theta p (polyMap p (Q ^ p)) = 0 := by
    rw [map_pow]
    exact theta_pth_power p _
  rw [theta_iterate_div_poly p _ _ p hpow, WPState.theta_prime_polynomial,
    (theta p).leibniz_div_const _ _ hpow, theta_poly]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

end WPPsi
