import WPForcedSourceStokes
import WPReview.NativeTruncation

open Polynomial

namespace WPForcedSourceStokes

/-- The reduced-numerator derivative agrees with every polynomial quotient presentation. -/
theorem rationalDerivative_fraction (P Q : ℚ[X]) (hQ : Q ≠ 0) :
    rationalDerivative (algebraMap ℚ[X] (RatFunc ℚ) P /
      algebraMap ℚ[X] (RatFunc ℚ) Q) =
      algebraMap ℚ[X] (RatFunc ℚ) (derivative P * Q - P * derivative Q) /
        (algebraMap ℚ[X] (RatFunc ℚ) Q) ^ 2 := by
  let f : RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ) P /
    algebraMap ℚ[X] (RatFunc ℚ) Q
  have hc : f.num * Q = P * f.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hQ).mpr rfl
  have hd := congrArg derivative hc
  simp only [derivative_mul] at hd
  have hc' := congrArg (algebraMap ℚ[X] (RatFunc ℚ)) hc
  have hd' := congrArg (algebraMap ℚ[X] (RatFunc ℚ)) hd
  simp only [map_mul] at hc'
  simp only [map_add, map_mul] at hd'
  change rationalDerivative f = _
  unfold rationalDerivative
  simp only [map_sub, map_mul]
  have hden : algebraMap ℚ[X] (RatFunc ℚ) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)
  have hq : algebraMap ℚ[X] (RatFunc ℚ) Q ≠ 0 := RatFunc.algebraMap_ne_zero hQ
  field_simp [hden, hq]
  linear_combination
    algebraMap ℚ[X] (RatFunc ℚ) f.denom * algebraMap ℚ[X] (RatFunc ℚ) Q * hd' -
      (algebraMap ℚ[X] (RatFunc ℚ) (derivative f.denom) * algebraMap ℚ[X] (RatFunc ℚ) Q +
        algebraMap ℚ[X] (RatFunc ℚ) f.denom *
          algebraMap ℚ[X] (RatFunc ℚ) (derivative Q)) * hc'

theorem rationalDerivative_polynomial (P : ℚ[X]) :
    rationalDerivative (algebraMap ℚ[X] (RatFunc ℚ) P) =
      algebraMap ℚ[X] (RatFunc ℚ) (derivative P) := by
  simpa using rationalDerivative_fraction P 1 one_ne_zero

theorem rationalDerivative_add (f g : RatFunc ℚ) :
    rationalDerivative (f+g) = rationalDerivative f + rationalDerivative g := by
  refine RatFunc.induction_on (P := fun f =>
    rationalDerivative (f+g) = rationalDerivative f + rationalDerivative g) f ?_
  intro P Q hQ
  refine RatFunc.induction_on (P := fun g =>
    rationalDerivative (algebraMap ℚ[X] (RatFunc ℚ) P /
      algebraMap ℚ[X] (RatFunc ℚ) Q + g) =
      rationalDerivative (algebraMap ℚ[X] (RatFunc ℚ) P /
        algebraMap ℚ[X] (RatFunc ℚ) Q) + rationalDerivative g) g ?_
  intro R S hS
  have hq := RatFunc.algebraMap_ne_zero hQ
  have hs := RatFunc.algebraMap_ne_zero hS
  have heq : algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q +
      algebraMap ℚ[X] (RatFunc ℚ) R / algebraMap ℚ[X] (RatFunc ℚ) S =
      algebraMap ℚ[X] (RatFunc ℚ) (P*S+R*Q) /
        algebraMap ℚ[X] (RatFunc ℚ) (Q*S) := by
    simp only [map_add, map_mul]
    field_simp [hq, hs]
  rw [heq, rationalDerivative_fraction _ _ (mul_ne_zero hQ hS),
    rationalDerivative_fraction _ _ hQ, rationalDerivative_fraction _ _ hS]
  simp only [derivative_mul, map_add, map_sub, map_mul]
  field_simp [hq, hs]
  ring

theorem rationalDerivative_mul (f g : RatFunc ℚ) :
    rationalDerivative (f*g) = rationalDerivative f * g + f * rationalDerivative g := by
  refine RatFunc.induction_on (P := fun f =>
    rationalDerivative (f*g) = rationalDerivative f*g + f*rationalDerivative g) f ?_
  intro P Q hQ
  refine RatFunc.induction_on (P := fun g =>
    rationalDerivative ((algebraMap ℚ[X] (RatFunc ℚ) P /
      algebraMap ℚ[X] (RatFunc ℚ) Q)*g) =
      rationalDerivative (algebraMap ℚ[X] (RatFunc ℚ) P /
        algebraMap ℚ[X] (RatFunc ℚ) Q)*g +
      (algebraMap ℚ[X] (RatFunc ℚ) P /
        algebraMap ℚ[X] (RatFunc ℚ) Q)*rationalDerivative g) g ?_
  intro R S hS
  have hq := RatFunc.algebraMap_ne_zero hQ
  have hs := RatFunc.algebraMap_ne_zero hS
  have heq : algebraMap ℚ[X] (RatFunc ℚ) P / algebraMap ℚ[X] (RatFunc ℚ) Q *
      (algebraMap ℚ[X] (RatFunc ℚ) R / algebraMap ℚ[X] (RatFunc ℚ) S) =
      algebraMap ℚ[X] (RatFunc ℚ) (P*R) /
        algebraMap ℚ[X] (RatFunc ℚ) (Q*S) := by
    simp only [map_mul]
    field_simp [hq, hs]
  rw [heq, rationalDerivative_fraction _ _ (mul_ne_zero hQ hS),
    rationalDerivative_fraction _ _ hQ, rationalDerivative_fraction _ _ hS]
  simp only [derivative_mul, map_add, map_sub, map_mul]
  field_simp [hq, hs]
  ring

@[simp] theorem rationalDerivative_zero : rationalDerivative 0 = 0 := by
  simpa using rationalDerivative_polynomial 0

@[simp] theorem rationalDerivative_constant (a : ℚ) :
    rationalDerivative (RatFunc.C a) = 0 := by
  simpa using rationalDerivative_polynomial (C a)

noncomputable def rationalDerivativeAddHom : RatFunc ℚ →+ RatFunc ℚ where
  toFun := rationalDerivative
  map_zero' := rationalDerivative_zero
  map_add' := rationalDerivative_add

theorem rationalDerivative_sum {ι : Type*} (s : Finset ι) (f : ι → RatFunc ℚ) :
    rationalDerivative (∑ i ∈ s, f i) = ∑ i ∈ s, rationalDerivative (f i) :=
  map_sum rationalDerivativeAddHom _ _

noncomputable def cubicPullback (P : ℚ[X]) : ℚ[X] := P.comp (C (729/15625)*X^3)

noncomputable def pullbackValue (P : ℚ[X]) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (cubicPullback P)

noncomputable def pullbackHom : ℚ[X] →+* RatFunc ℚ :=
  (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.compRingHom (C (729/15625)*X^3))

@[simp] theorem pullbackHom_apply (P : ℚ[X]) : pullbackHom P = pullbackValue P := rfl

@[simp] theorem pullbackValue_C (q : ℚ) : pullbackValue (C q) = RatFunc.C q := by
  simp [pullbackValue, cubicPullback]

@[simp] theorem pullbackValue_X : pullbackValue X = lambda := by
  simp [pullbackValue, cubicPullback, lambda, symbol]

/-- The literal lambda=729*x^3/15625 pullback intertwines Euler differentiation. -/
theorem rationalDerivative_cubic_pullback (P : ℚ[X]) :
    rationalDerivative (pullbackValue P) =
      (3/symbol) * pullbackValue (WPReview.nativeTheta P) := by
  have hx : symbol ≠ 0 := RatFunc.algebraMap_ne_zero X_ne_zero
  rw [pullbackValue, rationalDerivative_polynomial]
  simp [cubicPullback, WPReview.nativeTheta, derivative_comp, derivative_mul,
    derivative_pow, pullbackValue, symbol, _root_.map_ofNat, RatFunc.algebraMap_C]
  field_simp [show RatFunc.X ≠ (0 : RatFunc ℚ) from hx]

end WPForcedSourceStokes
