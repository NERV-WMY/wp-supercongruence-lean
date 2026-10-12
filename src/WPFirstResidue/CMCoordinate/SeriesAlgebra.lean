import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic

open scoped Polynomial PowerSeries LaurentSeries
open Polynomial

namespace WPFirstResidue.CMCoordinate

variable {K : Type*} [Field K]

theorem coeff_two_mul (f g : K⟦X⟧) :
    PowerSeries.coeff 2 (f * g) =
      PowerSeries.constantCoeff f * PowerSeries.coeff 2 g +
      PowerSeries.coeff 1 f * PowerSeries.coeff 1 g +
      PowerSeries.coeff 2 f * PowerSeries.constantCoeff g := by
  have ha : Finset.HasAntidiagonal.antidiagonal (2 : ℕ) =
      {(0, 2), (1, 1), (2, 0)} := rfl
  rw [PowerSeries.coeff_mul, ha]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  ring

theorem coeff_two_cube (f : K⟦X⟧) :
    PowerSeries.coeff 2 (f ^ 3) =
      3 * PowerSeries.constantCoeff f ^ 2 * PowerSeries.coeff 2 f +
      3 * PowerSeries.constantCoeff f * PowerSeries.coeff 1 f ^ 2 := by
  rw [show f ^ 3 = (f * f) * f by ring, coeff_two_mul, coeff_two_mul,
    PowerSeries.coeff_one_mul]
  simp only [map_mul]
  ring

theorem coeff_two_fourth_of_origin_zero (f : K⟦X⟧)
    (hf : PowerSeries.constantCoeff f = 0) : PowerSeries.coeff 2 (f ^ 4) = 0 := by
  rw [show f ^ 4 = (f * f) * (f * f) by ring, coeff_two_mul]
  simp [PowerSeries.coeff_one_mul, hf]

noncomputable def shiftedUnit (f : K⟦X⟧) : K⟦X⟧ :=
  PowerSeries.mk (fun n ↦ PowerSeries.coeff (n + 1) f)

theorem shiftedUnit_factor (f : K⟦X⟧) (hf : PowerSeries.constantCoeff f = 0) :
    f = PowerSeries.X * shiftedUnit f := by
  simpa [shiftedUnit, hf] using PowerSeries.eq_X_mul_shift_add_const f

@[simp] theorem shiftedUnit_origin (f : K⟦X⟧) :
    PowerSeries.constantCoeff (shiftedUnit f) = PowerSeries.coeff 1 f := by
  simp [shiftedUnit, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

@[simp] theorem shiftedUnit_linear (f : K⟦X⟧) :
    PowerSeries.coeff 1 (shiftedUnit f) = PowerSeries.coeff 2 f := by
  simp [shiftedUnit]

noncomputable def centerEvalHom (c : K) (f : K⟦X⟧) : K[X] →+* K⟦X⟧ :=
  Polynomial.eval₂RingHom PowerSeries.C (PowerSeries.C c + f)

@[simp] theorem centerEvalHom_origin (c : K) (f : K⟦X⟧)
    (hf : PowerSeries.constantCoeff f = 0) (P : K[X]) :
    PowerSeries.constantCoeff (centerEvalHom c f P) = P.eval c := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, Polynomial.eval_add, hP, hQ]
  | monomial n a => simp [centerEvalHom, hf, Polynomial.eval₂_monomial]

@[simp] theorem centerEvalHom_linear (c : K) (f : K⟦X⟧)
    (hf : PowerSeries.constantCoeff f = 0) (P : K[X]) :
    PowerSeries.coeff 1 (centerEvalHom c f P) =
      P.derivative.eval c * PowerSeries.coeff 1 f := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [map_add, Polynomial.eval_add, hP, hQ, add_mul]
  | monomial n a =>
      simp [centerEvalHom, Polynomial.eval₂_monomial,
        PowerSeries.coeff_one_pow, hf, Polynomial.derivative_monomial]
      ring

/-- A coordinate with invertible linear coefficient gives an actual injective
polynomial substitution: substitute its compositional inverse and undo translation. -/
theorem centerEvalHom_injective (c : K) (f : K⟦X⟧)
    (hf : PowerSeries.constantCoeff f = 0) (hu : IsUnit (PowerSeries.coeff 1 f)) :
    Function.Injective (centerEvalHom c f) := by
  let g := f.substInvOfIsUnit hu
  have hg : PowerSeries.HasSubst g := PowerSeries.HasSubst.substInvOfIsUnit f hu
  have hfg : f.subst g = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_right f hf hu
  let S := PowerSeries.substAlgHom (R := K) hg
  have hS (t : K⟦X⟧) : S.toRingHom t = PowerSeries.subst g t :=
    congrFun (PowerSeries.coe_substAlgHom hg) t
  have hC : S.toRingHom.comp PowerSeries.C = PowerSeries.C := by
    ext1 a
    rw [RingHom.comp_apply, hS, PowerSeries.subst_C]
    rfl
  have htranslate (P : K[X]) :
      S (centerEvalHom c f P) = ((P.comp (C c + X) : K[X]) : K⟦X⟧) := by
    change S.toRingHom (P.eval₂ PowerSeries.C (PowerSeries.C c + f)) = _
    rw [Polynomial.hom_eval₂, hC]
    have harg : S.toRingHom (PowerSeries.C c + f) = PowerSeries.C c + PowerSeries.X := by
      rw [hS, PowerSeries.subst_add hg, PowerSeries.subst_C, hfg]
      rfl
    rw [harg]
    rw [← Polynomial.eval₂_C_X_eq_coe, Polynomial.eval₂_comp]
    simp
  intro P Q hPQ
  have ht := congrArg S hPQ
  rw [htranslate P, htranslate Q] at ht
  have hpq := Polynomial.coe_injective K ht
  have hinverse : (C c + X : K[X]).comp (C (-c) + X) = X := by
    simp
  have he := congrArg (fun P : K[X] ↦ P.comp (C (-c) + X)) hpq
  simpa only [Polynomial.comp_assoc, hinverse, Polynomial.comp_X] using he

noncomputable def centerLaurentHom (c : K) (f : K⟦X⟧) : K[X] →+* K⸨X⸩ :=
  (HahnSeries.ofPowerSeries ℤ K).comp (centerEvalHom c f)

@[simp] theorem centerLaurentHom_apply (c : K) (f : K⟦X⟧) (P : K[X]) :
    centerLaurentHom c f P = ((centerEvalHom c f P : K⟦X⟧) : K⸨X⸩) := rfl

theorem centerLaurentHom_injective (c : K) (f : K⟦X⟧)
    (hf : PowerSeries.constantCoeff f = 0) (hu : IsUnit (PowerSeries.coeff 1 f)) :
    Function.Injective (centerLaurentHom c f) :=
  HahnSeries.ofPowerSeries_injective.comp (centerEvalHom_injective c f hf hu)

/-- Extension to the fraction field is justified by the inverse-defined coordinate;
it transports rational identities, including an actual simple pole, without an
evaluation convention at a singular point. -/
noncomputable def centerRatFuncHom (c : K) (f : K⟦X⟧)
    (hf : PowerSeries.constantCoeff f = 0) (hu : IsUnit (PowerSeries.coeff 1 f)) :
    RatFunc K →+* K⸨X⸩ :=
  IsFractionRing.lift (centerLaurentHom_injective c f hf hu)

@[simp] theorem centerRatFuncHom_polynomial (c : K) (f : K⟦X⟧)
    (hf : PowerSeries.constantCoeff f = 0) (hu : IsUnit (PowerSeries.coeff 1 f))
    (P : K[X]) :
    centerRatFuncHom c f hf hu (algebraMap K[X] (RatFunc K) P) =
      ((centerEvalHom c f P : K⟦X⟧) : K⸨X⸩) :=
  IsFractionRing.lift_algebraMap _ P

@[simp] theorem centerRatFuncHom_C (c a : K) (f : K⟦X⟧)
    (hf : PowerSeries.constantCoeff f = 0) (hu : IsUnit (PowerSeries.coeff 1 f)) :
    centerRatFuncHom c f hf hu (RatFunc.C a) = HahnSeries.C a := by
  rw [← RatFunc.algebraMap_C, centerRatFuncHom_polynomial]
  change ((Polynomial.eval₂ PowerSeries.C (PowerSeries.C c + f) (C a) : K⟦X⟧) :
    K⸨X⸩) = _
  rw [Polynomial.eval₂_C]
  exact PowerSeries.coe_C a

end WPFirstResidue.CMCoordinate
