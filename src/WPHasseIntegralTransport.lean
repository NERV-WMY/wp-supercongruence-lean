import WPFiniteHasseUniqueness
import WPFiniteConductorIntegrality

open scoped BigOperators Polynomial
open Polynomial WPActualNativeHasse WPHasseCubicSource WPPIntegralReduction

namespace WPHasseIntegralTransport

theorem one_over_125_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    0 ≤ padicValRat p (1 / 125 : ℚ) := by
  have h5 : 0 ≤ padicValRat p (1 / 5 : ℚ) :=
    WPFiniteConductorPolynomial.small_inverse_integral p 5 (by omega) (by omega)
  let q5 : integralRationals p := ⟨1 / 5, h5⟩
  have h := (q5 ^ 3).property
  change 0 ≤ padicValRat p ((1 / 5 : ℚ) ^ 3) at h
  simpa only [show (1 / 5 : ℚ) ^ 3 = 1 / 125 by norm_num] using h

/-- Every original coefficient is lifted to the actual p-integral subring. -/
noncomputable def nativeIntegral (p e : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (he : e < p) :
    (integralRationals p)[X] :=
  ∑ n : Fin (e + 1), monomial n.val
    ⟨WPReview.nativeCoefficient n.val, actual_native_coefficient_integral p n.val hp (by
      have hn := n.isLt
      omega)⟩

theorem nativeIntegral_map_rational (p e : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (he : e < p) :
    (nativeIntegral p e hp he).map (integralRationals p).subtype =
      WPReview.nativePolynomial (e + 1) := by
  simp only [nativeIntegral, Polynomial.map_sum, map_monomial, Subring.coe_subtype]
  exact Fin.sum_univ_eq_sum_range (fun n => monomial n (WPReview.nativeCoefficient n)) (e + 1)

theorem nativeIntegral_map_field (p e : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (he : e < p) :
    (nativeIntegral p e hp he).map (residueHom p) = nativeField p e := by
  simp only [nativeIntegral, Polynomial.map_sum, map_monomial]
  change (∑ n : Fin (e + 1), monomial n.val (WPReview.nativeCoefficient n.val : ZMod p)) = _
  exact Fin.sum_univ_eq_sum_range (fun n => monomial n (WPReview.nativeCoefficient n : ZMod p)) (e + 1)

noncomputable def integralV (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) : (integralRationals p)[X] :=
  C ⟨1 / 125, one_over_125_integral p hp⟩ * (4 * X - 1) ^ 2 * (4 - X)

noncomputable def fieldV (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  C ((1 / 125 : ℚ) : ZMod p) * (4 * X - 1) ^ 2 * (4 - X)

theorem integralV_map_rational (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralV p hp).map (integralRationals p).subtype = WPActualPullbackSource.Vpolynomial := by
  simp only [integralV, WPActualPullbackSource.Vpolynomial, Polynomial.map_mul, map_C,
    Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat, Polynomial.map_one, Subring.coe_subtype]

theorem integralV_map_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralV p hp).map (residueHom p) = fieldV p := by
  simp only [integralV, fieldV, Polynomial.map_mul, map_C, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, Polynomial.map_one]
  rfl

theorem map_regularNative {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : R[X]) : (regularNative P).map f = regularNative (P.map f) := by
  simp only [regularNative, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, Polynomial.map_one, ← derivative_map]

theorem map_cubicOperator {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : R[X]) : (cubicOperator P).map f = cubicOperator (P.map f) := by
  simp only [cubicOperator, cubicA3, cubicA2, cubicA1, cubicA0, cubicDiscriminant,
    cubicNumerator, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, Polynomial.map_one, Polynomial.map_neg, ← derivative_map]

/-- The rational universal source is transported by an injective coefficient map, not asserted. -/
theorem actual_integral_cubic_source (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (P : (integralRationals p)[X]) :
    cubicOperator (P.comp (integralV p hp)) =
      3 * (4 * X - 1) * (11 - 4 * X) * (regularNative P).comp (integralV p hp) := by
  apply Polynomial.map_injective (integralRationals p).subtype
    (Subring.subtype_injective (integralRationals p))
  rw [map_cubicOperator, Polynomial.map_comp, integralV_map_rational]
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_ofNat, Polynomial.map_one, Polynomial.map_comp,
    map_regularNative, integralV_map_rational]
  exact actual_cubic_pullback_source (P.map (integralRationals p).subtype)

/-- The actual native field source after the original cubic V pullback. -/
theorem actual_native_V_cubic_ODE (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    cubicOperator ((nativeField p (p / 6)).comp (fieldV p)) = 0 := by
  have hd : p / 6 < p := by omega
  have h := actual_integral_cubic_source p hp (nativeIntegral p (p / 6) hp hd)
  have hf := congrArg (Polynomial.map (residueHom p)) h
  simp only [map_cubicOperator, Polynomial.map_comp, nativeIntegral_map_field,
    integralV_map_field, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_ofNat, Polynomial.map_one,
    map_regularNative] at hf
  rw [actual_native_field_regular_ODE p hp, zero_comp, mul_zero] at hf
  exact hf

theorem actual_native_V_endpoint (p : ℕ) [Fact p.Prime] :
    ((nativeField p (p / 6)).comp (fieldV p)).eval 4 = 1 := by
  rw [Polynomial.eval_comp]
  have hV : (fieldV p).eval 4 = 0 := by simp [fieldV]
  rw [hV, actual_native_field_origin]

theorem actual_native_V_degree (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    ((nativeField p (p / 6)).comp (fieldV p)).natDegree ≤ (p - 1) / 2 := by
  have hV : (fieldV p).natDegree ≤ 3 := by unfold fieldV; compute_degree
  have h := natDegree_comp_le (p := nativeField p (p / 6)) (q := fieldV p)
  have hdeg := actual_native_field_degree p
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rcases hpodd with ⟨k, hk⟩
  calc
    _ ≤ (p / 6) * 3 := h.trans (Nat.mul_le_mul hdeg hV)
    _ ≤ (p - 1) / 2 := by have h6 := Nat.div_mul_le_self p 6; omega

end WPHasseIntegralTransport
