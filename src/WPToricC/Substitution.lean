import WPToric
import Mathlib.Algebra.Polynomial.Degree.Lemmas

noncomputable section

namespace WPToricC

open Polynomial WPPsi

variable (p : ℕ) [Fact p.Prime]

def cubic : Polynomial (ZMod p) := C 27 * X ^ 3

def polySub : Polynomial (ZMod p) →+* Polynomial (ZMod p) := compRingHom (cubic p)

theorem twentySeven_nonzero (hp7 : 7 ≤ p) : (27 : ZMod p) ≠ 0 := by
  have h6 : (6 : ZMod p) ≠ 0 := (WPFiveFactor.six_unit p Fact.out hp7).ne_zero
  have h23 : (2 : ZMod p) * 3 ≠ 0 := by norm_num; exact h6
  have h3 : (3 : ZMod p) ≠ 0 := (mul_ne_zero_iff.mp h23).2
  convert pow_ne_zero 3 h3 using 1
  norm_num

theorem cubic_degree (hp7 : 7 ≤ p) : (cubic p).natDegree = 3 := by
  simp [cubic, twentySeven_nonzero p hp7]

theorem polySub_apply (P : Polynomial (ZMod p)) : polySub p P = P.comp (cubic p) := rfl

theorem polySub_C (a : ZMod p) : polySub p (C a) = C a := by
  simp [polySub]

theorem polySub_X : polySub p X = cubic p := by simp [polySub]

theorem polySub_injective (hp7 : 7 ≤ p) : Function.Injective (polySub p) := by
  have hz : ∀ P, polySub p P = 0 → P = 0 := by
    intro P hP
    have he := congrArg Polynomial.natDegree hP
    have hd : P.natDegree * 3 = 0 := by
      simpa [polySub_apply, natDegree_comp, cubic_degree p hp7] using he
    have hn : P.natDegree = 0 := by omega
    have hc : P = C (P.coeff 0) := eq_C_of_natDegree_eq_zero hn
    rw [hc, polySub_C] at hP
    exact hc.trans hP
  intro P Q h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, h, sub_self]

def sigma (hp7 : 7 ≤ p) : K p →+* K p :=
  IsFractionRing.lift (g := (polyMap p).comp (polySub p))
    ((IsFractionRing.injective (Polynomial (ZMod p)) (K p)).comp (polySub_injective p hp7))

theorem sigma_poly (hp7 : 7 ≤ p) (P : Polynomial (ZMod p)) :
    sigma p hp7 (polyMap p P) = polyMap p (polySub p P) :=
  IsFractionRing.lift_algebraMap
    (g := (polyMap p).comp (polySub p)) _ P

theorem sigma_injective (hp7 : 7 ≤ p) : Function.Injective (sigma p hp7) :=
  (sigma p hp7).injective

def c : K p := polyMap p X

theorem sigma_parameter (hp7 : 7 ≤ p) : sigma p hp7 (polyMap p X) = 27 * c p ^ 3 := by
  rw [sigma_poly, polySub_X]
  have hC : polyMap p (C 27) = 27 := by
    change polyMap p (27 : Polynomial (ZMod p)) = 27
    exact map_ofNat _ _
  simp [cubic, c, map_mul, map_pow, hC]

theorem sigma_base (hp7 : 7 ≤ p) (a : ZMod p) :
    sigma p hp7 (algebraMap (ZMod p) (K p) a) = algebraMap (ZMod p) (K p) a := by
  have he : algebraMap (ZMod p) (K p) a = polyMap p (C a) := rfl
  rw [he, sigma_poly, polySub_C]

theorem theta_cubic : WPRho.theta (cubic p) = 3 * cubic p := by
  simp only [WPRho.theta, cubic, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_pow, derivative_X, mul_one, C_eq_natCast]
  ring

theorem theta_polySub (P : Polynomial (ZMod p)) :
    WPRho.theta (polySub p P) = 3 * polySub p (WPRho.theta P) := by
  simp only [polySub_apply, WPRho.theta, derivative_comp, mul_comp, X_comp]
  rw [← mul_assoc]
  have he : X * (cubic p).derivative = 3 * cubic p := theta_cubic p
  rw [he]
  ring

theorem theta_sigma_poly (hp7 : 7 ≤ p) (P : Polynomial (ZMod p)) :
    theta p (sigma p hp7 (polyMap p P)) = 3 * sigma p hp7 (theta p (polyMap p P)) := by
  rw [sigma_poly, theta_poly, theta_poly, sigma_poly, theta_polySub, map_mul, map_ofNat]

theorem theta_sigma (hp7 : 7 ≤ p) (a : K p) :
    theta p (sigma p hp7 a) = 3 * sigma p hp7 (theta p a) := by
  obtain ⟨P, Q, _, rfl⟩ := IsFractionRing.div_surjective (Polynomial (ZMod p)) a
  change theta p (sigma p hp7 (polyMap p P / polyMap p Q)) =
    3 * sigma p hp7 (theta p (polyMap p P / polyMap p Q))
  rw [map_div₀, (theta p).leibniz_div, (theta p).leibniz_div,
    theta_sigma_poly, theta_sigma_poly]
  simp only [smul_eq_mul, map_mul, map_sub, map_inv₀, map_pow]
  ring

theorem sigma_oneMinus (hp7 : 7 ≤ p) :
    sigma p hp7 (WPToricPsi.oneMinus p) = 1 - 27 * c p ^ 3 := by
  change sigma p hp7 (polyMap p (1 - X)) = _
  rw [map_sub, map_one, map_sub, map_one, sigma_parameter]

theorem cubic_pole_nonzero (hp7 : 7 ≤ p) : (1 : K p) - 27 * c p ^ 3 ≠ 0 := by
  rw [← sigma_oneMinus p hp7]
  simpa only [map_zero] using
    (sigma_injective p hp7).ne (WPToricPsi.oneMinus_nonzero p)

end WPToricC
