import WPHasseCubicSource

open scoped Polynomial
open Polynomial WPActualNativeHasse WPHasseCubicSource

namespace WPFiniteHasseUniqueness

noncomputable def endpointE3 {K : Type*} [CommRing K] : K[X] :=
  8 * (X + 5) * (4 * X + 15) ^ 2
noncomputable def endpointSecond {K : Type*} [CommRing K] : K[X] :=
  12 * X * (4 * X + 15) ^ 2 + 24 * (X + 5) * (4 * X + 15) * (8 * X + 15)
noncomputable def endpointE2 {K : Type*} [CommRing K] : K[X] := endpointSecond - 3 * endpointE3
noncomputable def endpointE1 {K : Type*} [CommRing K] : K[X] :=
  cubicA1.comp (X + 4) - endpointSecond + 2 * endpointE3
noncomputable def endpointE0 {K : Type*} [CommRing K] : K[X] := X * cubicA0.comp (X + 4)

/-- Exact translation at the actual endpoint x=4, with the full cubic operator retained. -/
theorem actual_endpoint_Euler_transport {K : Type*} [CommRing K] (P : K[X]) :
    X * (cubicOperator P).comp (X + 4) =
      regularEuler endpointE3 endpointE2 endpointE1 endpointE0 (P.comp (X + 4)) := by
  simp [regularEuler, theta, endpointE3, endpointE2, endpointSecond, endpointE1,
    endpointE0, cubicOperator, cubicA3, cubicA2, cubicA1, cubicA0,
    cubicDiscriminant, cubicNumerator, derivative_comp, derivative_mul]
  ring

theorem actual_endpoint_indicial_coefficients {K : Type*} [CommRing K] :
    (endpointE3 : K[X]).coeff 0 = 9000 ∧
    (endpointE2 : K[X]).coeff 0 = 0 ∧
    (endpointE1 : K[X]).coeff 0 = 0 ∧
    (endpointE0 : K[X]).coeff 0 = 0 := by
  simp [coeff_zero_eq_eval_zero, endpointE3, endpointE2, endpointSecond, endpointE1,
    endpointE0, cubicA1, cubicA0, cubicDiscriminant, cubicNumerator, derivative_mul,
    Polynomial.eval_comp]
  norm_num

theorem actual_endpoint_indicial_unit (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (9000 : ZMod p) ≠ 0 := by
  have hu (n : ℕ) (hn : 0 < n) (hnp : n < p) : (n : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd hn hd
    omega
  have hfactor : (9000 : ZMod p) = 2 ^ 3 * 3 ^ 2 * 5 ^ 3 := by norm_num
  rw [hfactor]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 3 (hu 2 (by omega) (by omega)))
    (pow_ne_zero 2 (hu 3 (by omega) (by omega))))
    (pow_ne_zero 3 (hu 5 (by omega) (by omega)))

/-- Actual cubic endpoint uniqueness for every polynomial of degree below p. -/
theorem actual_finite_cubic_zero (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (P : (ZMod p)[X]) (hdegree : P.natDegree < p) (hend : P.eval 4 = 0)
    (hODE : cubicOperator P = 0) : P = 0 := by
  let Y := P.comp (X + 4)
  have hYdegree : Y.natDegree < p := by
    have hd : Y.natDegree ≤ P.natDegree := by
      have hc := natDegree_comp_le (p := P) (q := (X + 4))
      have ha : (X + 4 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
      exact hc.trans (by nlinarith)
    exact hd.trans_lt hdegree
  have hYorigin : Y.eval 0 = 0 := by simpa [Y] using hend
  have hYODE : regularEuler endpointE3 endpointE2 endpointE1 endpointE0 Y = 0 := by
    rw [← actual_endpoint_Euler_transport, hODE, zero_comp, mul_zero]
  have he := actual_endpoint_indicial_coefficients (K := ZMod p)
  have hz := finite_regularEuler_uniqueness p _ _ _ _ Y 9000
    (actual_endpoint_indicial_unit p hp) he.1 he.2.1 he.2.2.1 he.2.2.2 hYdegree hYorigin hYODE
  have hcomp := congrArg (fun Q : (ZMod p)[X] => Q.comp (X - 4)) hz
  have hId : (X + 4 : (ZMod p)[X]).comp (X - 4) = X := by
    simp only [add_comp, X_comp, ofNat_comp]
    ring
  simpa only [Y, comp_assoc, hId, comp_X, zero_comp] using hcomp

theorem cubicOperator_sub {K : Type*} [CommRing K] (P Q : K[X]) :
    cubicOperator (P - Q) = cubicOperator P - cubicOperator Q := by
  simp only [cubicOperator, derivative_sub]
  ring

theorem actual_finite_cubic_unique (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (P Q : (ZMod p)[X]) (hPdegree : P.natDegree < p) (hQdegree : Q.natDegree < p)
    (hend : P.eval 4 = Q.eval 4) (hP : cubicOperator P = 0) (hQ : cubicOperator Q = 0) :
    P = Q := by
  apply sub_eq_zero.mp
  apply actual_finite_cubic_zero p hp (P - Q)
  · exact (natDegree_sub_le P Q).trans_lt (max_lt hPdegree hQdegree)
  · simpa only [eval_sub, sub_eq_zero] using hend
  · rw [cubicOperator_sub, hP, hQ, sub_self]

end WPFiniteHasseUniqueness
