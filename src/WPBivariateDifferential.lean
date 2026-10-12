import WPRationalDifferential
import Mathlib.RingTheory.Derivation.MapCoeffs

open Polynomial

namespace WPForcedSourceStokes

noncomputable section

local instance canonicalRatFuncIntAlgebra {K : Type*} [Field K] : Algebra ℤ (RatFunc K) :=
  Ring.toIntAlgebra (RatFunc K)

section Lift

variable {K : Type*} [Field K]

/-- Extension to the actual reduced fraction, including a coefficient derivation. -/
noncomputable def rationalLift (D : Derivation ℤ K[X] K[X]) (f : RatFunc K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (D f.num * f.denom - f.num * D f.denom) /
    (algebraMap K[X] (RatFunc K) f.denom) ^ 2

theorem rationalLift_fraction (D : Derivation ℤ K[X] K[X]) (P Q : K[X]) (hQ : Q ≠ 0) :
    rationalLift D (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q) =
      algebraMap K[X] (RatFunc K) (D P * Q - P * D Q) /
        (algebraMap K[X] (RatFunc K) Q) ^ 2 := by
  let f : RatFunc K := algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q
  have hc : f.num * Q = P * f.denom := (RatFunc.num_mul_eq_mul_denom_iff hQ).mpr rfl
  have hd := congrArg D hc
  simp only [Derivation.leibniz, smul_eq_mul] at hd
  have hc' := congrArg (algebraMap K[X] (RatFunc K)) hc
  have hd' := congrArg (algebraMap K[X] (RatFunc K)) hd
  simp only [map_mul] at hc'
  simp only [map_add, map_mul] at hd'
  change rationalLift D f = _
  unfold rationalLift
  simp only [map_sub, map_mul]
  have hden := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)
  have hq := RatFunc.algebraMap_ne_zero hQ
  field_simp [hden, hq]
  linear_combination
    algebraMap K[X] (RatFunc K) f.denom * algebraMap K[X] (RatFunc K) Q * hd' -
      (algebraMap K[X] (RatFunc K) (D f.denom) * algebraMap K[X] (RatFunc K) Q +
        algebraMap K[X] (RatFunc K) f.denom * algebraMap K[X] (RatFunc K) (D Q)) * hc'

theorem rationalLift_polynomial (D : Derivation ℤ K[X] K[X]) (P : K[X]) :
    rationalLift D (algebraMap K[X] (RatFunc K) P) = algebraMap K[X] (RatFunc K) (D P) := by
  simpa using rationalLift_fraction D P 1 one_ne_zero

theorem rationalLift_add (D : Derivation ℤ K[X] K[X]) (f g : RatFunc K) :
    rationalLift D (f + g) = rationalLift D f + rationalLift D g := by
  refine RatFunc.induction_on (P := fun f =>
    rationalLift D (f + g) = rationalLift D f + rationalLift D g) f ?_
  intro P Q hQ
  refine RatFunc.induction_on (P := fun g =>
    rationalLift D (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q + g) =
      rationalLift D (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q) +
        rationalLift D g) g ?_
  intro R S hS
  have hq := RatFunc.algebraMap_ne_zero hQ
  have hs := RatFunc.algebraMap_ne_zero hS
  have heq : algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q +
      algebraMap K[X] (RatFunc K) R / algebraMap K[X] (RatFunc K) S =
        algebraMap K[X] (RatFunc K) (P * S + R * Q) / algebraMap K[X] (RatFunc K) (Q * S) := by
    simp only [map_add, map_mul]
    field_simp [hq, hs]
  rw [heq, rationalLift_fraction _ _ _ (mul_ne_zero hQ hS),
    rationalLift_fraction _ _ _ hQ, rationalLift_fraction _ _ _ hS]
  simp only [Derivation.leibniz, map_add, smul_eq_mul, map_sub, map_mul]
  field_simp [hq, hs]
  ring

theorem rationalLift_mul (D : Derivation ℤ K[X] K[X]) (f g : RatFunc K) :
    rationalLift D (f * g) = rationalLift D f * g + f * rationalLift D g := by
  refine RatFunc.induction_on (P := fun f =>
    rationalLift D (f * g) = rationalLift D f * g + f * rationalLift D g) f ?_
  intro P Q hQ
  refine RatFunc.induction_on (P := fun g =>
    rationalLift D ((algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q) * g) =
      rationalLift D (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q) * g +
        (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q) * rationalLift D g) g ?_
  intro R S hS
  have hq := RatFunc.algebraMap_ne_zero hQ
  have hs := RatFunc.algebraMap_ne_zero hS
  have heq : algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q *
      (algebraMap K[X] (RatFunc K) R / algebraMap K[X] (RatFunc K) S) =
        algebraMap K[X] (RatFunc K) (P * R) / algebraMap K[X] (RatFunc K) (Q * S) := by
    simp only [map_mul]
    field_simp [hq, hs]
  rw [heq, rationalLift_fraction _ _ _ (mul_ne_zero hQ hS),
    rationalLift_fraction _ _ _ hQ, rationalLift_fraction _ _ _ hS]
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_sub, map_mul]
  field_simp [hq, hs]
  ring

noncomputable def rationalLiftAddHom (D : Derivation ℤ K[X] K[X]) : RatFunc K →+ RatFunc K where
  toFun := rationalLift D
  map_zero' := by simpa using rationalLift_polynomial D 0
  map_add' := rationalLift_add D

noncomputable def rationalLiftDerivation (D : Derivation ℤ K[X] K[X]) :
    Derivation ℤ (RatFunc K) (RatFunc K) :=
  Derivation.mk' (rationalLiftAddHom D).toIntLinearMap (by
    intro a b
    change rationalLift D (a * b) = a * rationalLift D b + b * rationalLift D a
    rw [rationalLift_mul]
    ring)

end Lift

noncomputable def xDerivation : Derivation ℤ (RatFunc ℚ) (RatFunc ℚ) :=
  Derivation.mk' rationalDerivativeAddHom.toIntLinearMap (by
    intro a b
    change rationalDerivative (a * b) = a * rationalDerivative b + b * rationalDerivative a
    rw [rationalDerivative_mul]
    ring)

/-- The x derivative acts on coefficients and keeps the angular variable s fixed. -/
noncomputable def coefficientXDerivation :
    Derivation ℤ (Polynomial (RatFunc ℚ)) (Polynomial (RatFunc ℚ)) :=
  letI : Differential (RatFunc ℚ) := ⟨xDerivation⟩
  Differential.mapCoeffs

noncomputable def partialX : Derivation ℤ (RatFunc (RatFunc ℚ)) (RatFunc (RatFunc ℚ)) :=
  rationalLiftDerivation (K := RatFunc ℚ) coefficientXDerivation

/-- The s derivative keeps every rational coefficient in x fixed. -/
noncomputable def partialS : Derivation ℤ (RatFunc (RatFunc ℚ)) (RatFunc (RatFunc ℚ)) :=
  rationalLiftDerivation (K := RatFunc ℚ) (Polynomial.derivative'.restrictScalars ℤ)

theorem coefficientXDerivation_coeff (P : Polynomial (RatFunc ℚ)) (k : ℕ) :
    (coefficientXDerivation P).coeff k = rationalDerivative (P.coeff k) := rfl

theorem coefficientXDerivation_C (f : RatFunc ℚ) :
    coefficientXDerivation (C f) = C (rationalDerivative f) := by
  ext k
  rw [coefficientXDerivation_coeff, coeff_C, coeff_C]
  split_ifs <;> simp

theorem coefficientXDerivation_X : coefficientXDerivation X = 0 := by
  have h1 : rationalDerivative 1 = 0 := by simpa using rationalDerivative_constant 1
  ext k
  rw [coefficientXDerivation_coeff, coeff_X, coeff_zero]
  split_ifs <;> simp [h1]

@[simp] theorem partialX_coefficient (f : RatFunc ℚ) :
    partialX (RatFunc.C f) = RatFunc.C (rationalDerivative f) := by
  change rationalLift coefficientXDerivation
    (algebraMap (Polynomial (RatFunc ℚ)) (RatFunc (RatFunc ℚ)) (C f)) = _
  rw [rationalLift_polynomial, coefficientXDerivation_C, RatFunc.algebraMap_C]

@[simp] theorem partialX_s : partialX (RatFunc.X : RatFunc (RatFunc ℚ)) = 0 := by
  change rationalLift coefficientXDerivation
    (algebraMap (Polynomial (RatFunc ℚ)) (RatFunc (RatFunc ℚ)) X) = _
  rw [rationalLift_polynomial, coefficientXDerivation_X, map_zero]

@[simp] theorem partialS_coefficient (f : RatFunc ℚ) :
    partialS (RatFunc.C f) = 0 := by
  change rationalLift (Polynomial.derivative'.restrictScalars ℤ)
    (algebraMap (Polynomial (RatFunc ℚ)) (RatFunc (RatFunc ℚ)) (C f)) = _
  rw [rationalLift_polynomial]
  simp

@[simp] theorem partialS_s : partialS (RatFunc.X : RatFunc (RatFunc ℚ)) = 1 := by
  change rationalLift (Polynomial.derivative'.restrictScalars ℤ)
    (algebraMap (Polynomial (RatFunc ℚ)) (RatFunc (RatFunc ℚ)) X) = _
  rw [rationalLift_polynomial]
  simp

@[simp] theorem partialX_x : partialX (RatFunc.C symbol) = 1 := by
  rw [partialX_coefficient]
  have h : rationalDerivative symbol = 1 := by
    rw [symbol, rationalDerivative_polynomial, derivative_X, map_one]
  rw [h, map_one]

end

end WPForcedSourceStokes
