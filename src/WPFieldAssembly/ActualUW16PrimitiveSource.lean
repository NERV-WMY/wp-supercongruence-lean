import WPFieldAssembly.ActualSigmaClearedSource

open scoped Polynomial
open Polynomial WPFieldAssembly.ActualSigmaFiniteEvenSource WPFieldAssembly.ActualSigmaClearedSource
  WPPIntegralReduction WPActualRankTwoHatLift

namespace WPFieldAssembly.ActualUW16PrimitiveSource

set_option maxHeartbeats 1400000

/- UW16a/h uses A=4^N=2^(p-1), rather than 4^(p-1). The actual
division primitive and its comparison retain the whole finite logarithm;
the latter has the final degree-N term before its divided carry is taken. -/

noncomputable def originalE4CenteredQ (p : ℕ) [Fact p.Prime] : ℚ[X] :=
  (finiteEvenSquaredQ p).comp (4 * WPFiniteWSource.squaredCoordinate) -
    Polynomial.C ((finiteEvenSquaredQ p).eval (4 / 5))

noncomputable def originalE1CenteredQ (p : ℕ) [Fact p.Prime] : ℚ[X] :=
  (finiteEvenSquaredQ p).comp WPFiniteWSource.squaredCoordinate -
    Polynomial.C ((finiteEvenSquaredQ p).eval (1 / 5))

noncomputable def originalWactQ (p : ℕ) [Fact p.Prime] : ℚ[X] :=
  Polynomial.C (2 * (5 : ℚ) ^ ((p - 1) / 2) / 15) *
    (Polynomial.C (((4 : ℚ) ^ ((p - 1) / 2))⁻¹) * originalE4CenteredQ p -
      originalE1CenteredQ p)

noncomputable def originalWbarQ (p : ℕ) [Fact p.Prime] : ℚ[X] :=
  Polynomial.C (2 * (5 : ℚ) ^ ((p - 1) / 2) / 15) *
    (originalE4CenteredQ p - originalE1CenteredQ p)

noncomputable def originalW1Q (p : ℕ) [Fact p.Prime] : ℚ[X] :=
  Polynomial.C (-2 * (5 : ℚ) ^ ((p - 1) / 2) * originalFourCarryQ p /
    (15 * (4 : ℚ) ^ ((p - 1) / 2))) * originalE4CenteredQ p

noncomputable def originalSquaredCoordinateI (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[X] := Polynomial.C (smallIntegralInverse p 5) * (X + 1)

noncomputable def originalE4CenteredI (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[X] :=
  (finiteEvenSquaredIntegral p).comp (4 * originalSquaredCoordinateI p) -
    Polynomial.C ((finiteEvenSquaredIntegral p).eval (4 * smallIntegralInverse p 5))

noncomputable def originalW1Integral (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[X] :=
  Polynomial.C (-2 * (5 : integralRationals p) ^ ((p - 1) / 2) *
    (WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) *
    smallIntegralInverse p 15 * (smallIntegralInverse p 4) ^ ((p - 1) / 2)) *
      originalE4CenteredI p

noncomputable def originalE4CenteredField (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (WPFiniteLVSource.evenSquared p).comp
    (4 * (WPFiniteWSource.squaredCoordinate : (ZMod p)[X])) -
    Polynomial.C ((WPFiniteLVSource.evenSquared p).eval (4 / 5))

theorem originalFourCarryQ_integer (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originalFourCarryQ p = (WPFiniteInversion.integerFermatQuotient p 2 : ℚ) := by
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hq := WPFiniteInversion.integerFermatQuotient_mul p 2 (by simpa using h2)
  have hqQ : (WPFiniteInversion.integerFermatQuotient p 2 : ℚ) * (p : ℚ) =
      (2 : ℚ) ^ (p - 1) - 1 := by exact_mod_cast hq
  have hn : 2 * ((p - 1) / 2) = p - 1 := by
    have ht := WPFiniteWSource.half_exponent p hp
    omega
  have hfour : (4 : ℚ) ^ ((p - 1) / 2) = (2 : ℚ) ^ (p - 1) := by
    rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, hn]
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [originalFourCarryQ, hfour]
  exact (div_eq_iff hpq).mpr hqQ.symm

theorem originalE4CenteredI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (originalE4CenteredI p).map (integralRationals p).subtype = originalE4CenteredQ p := by
  have h5 : (integralRationals p).subtype (smallIntegralInverse p 5) = (1 / 5 : ℚ) :=
    smallIntegralInverse_value p 5 (by omega) (by omega)
  have hs : (originalSquaredCoordinateI p).map (integralRationals p).subtype =
      (WPFiniteWSource.squaredCoordinate : ℚ[X]) := by
    simp only [originalSquaredCoordinateI, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_one]
    rw [h5]
    simp only [WPFiniteWSource.squaredCoordinate, one_div]
  have he : (integralRationals p).subtype
      ((finiteEvenSquaredIntegral p).eval (4 * smallIntegralInverse p 5)) =
        (finiteEvenSquaredQ p).eval (4 / 5) := by
    rw [← eval_map_apply, finiteEvenSquaredIntegral_value p hp,
      map_mul, map_ofNat, h5]
    congr 1
    ring
  simp only [originalE4CenteredI, Polynomial.map_sub, Polynomial.map_comp,
    Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_C,
    finiteEvenSquaredIntegral_value p hp, hs, he, originalE4CenteredQ]

theorem originalE4CenteredI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (originalE4CenteredI p).map (residueHom p) = originalE4CenteredField p := by
  have hs : (originalSquaredCoordinateI p).map (residueHom p) =
      (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]) := by
    simp only [originalSquaredCoordinateI, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_one]
    rw [smallIntegralInverse_field p 5 (by omega) (by omega)]
    rfl
  have he : residueHom p
      ((finiteEvenSquaredIntegral p).eval (4 * smallIntegralInverse p 5)) =
        (WPFiniteLVSource.evenSquared p).eval (4 / 5) := by
    rw [← eval_map_apply, finiteEvenSquaredIntegral_field p hp,
      map_mul, map_ofNat, smallIntegralInverse_field p 5 (by omega) (by omega)]
    congr 1
  simp only [originalE4CenteredI, Polynomial.map_sub, Polynomial.map_comp,
    Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_C,
    finiteEvenSquaredIntegral_field p hp, hs, he, originalE4CenteredField]

/-- W1 is carried in the original integral subring with no p-denominator relift. -/
theorem originalW1Integral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (originalW1Integral p).map (integralRationals p).subtype = originalW1Q p := by
  have h15 : (integralRationals p).subtype (smallIntegralInverse p 15) = (1 / 15 : ℚ) :=
    smallIntegralInverse_value p 15 (by omega) (by omega)
  have h4 : (integralRationals p).subtype (smallIntegralInverse p 4) = (1 / 4 : ℚ) :=
    smallIntegralInverse_value p 4 (by omega) (by omega)
  have hc : (integralRationals p).subtype
      (-2 * (5 : integralRationals p) ^ ((p - 1) / 2) *
        (WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) *
        smallIntegralInverse p 15 * (smallIntegralInverse p 4) ^ ((p - 1) / 2)) =
      -2 * (5 : ℚ) ^ ((p - 1) / 2) * originalFourCarryQ p /
        (15 * (4 : ℚ) ^ ((p - 1) / 2)) := by
    simp only [_root_.map_mul, _root_.map_neg, _root_.map_ofNat,
      _root_.map_pow, _root_.map_intCast]
    rw [h15, h4, ← originalFourCarryQ_integer p hp]
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev, inv_pow]
    ring
  rw [originalW1Integral, Polynomial.map_mul, Polynomial.map_C, hc,
    originalE4CenteredI_value p hp]
  rfl

/-- The honest whole first carry reduces to UW16h's literal W1, including degree N. -/
theorem originalW1Integral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (originalW1Integral p).map (residueHom p) =
      Polynomial.C (-2 * (5 : ZMod p) ^ ((p - 1) / 2) *
        (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) / 15) *
          originalE4CenteredField p := by
  have hc : residueHom p
      (-2 * (5 : integralRationals p) ^ ((p - 1) / 2) *
        (WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) *
        smallIntegralInverse p 15 * (smallIntegralInverse p 4) ^ ((p - 1) / 2)) =
      -2 * (5 : ZMod p) ^ ((p - 1) / 2) *
        (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) / 15 := by
    simp only [_root_.map_mul, _root_.map_neg, _root_.map_ofNat,
      _root_.map_pow, _root_.map_intCast]
    rw [smallIntegralInverse_field p 15 (by omega) (by omega),
      smallIntegralInverse_field p 4 (by omega) (by omega),
      Nat.cast_ofNat, Nat.cast_ofNat, inv_pow, WPFiniteWSource.four_half_power p hp,
      inv_one, mul_one]
    rw [div_eq_mul_inv]
  rw [originalW1Integral, Polynomial.map_mul, Polynomial.map_C, hc,
    originalE4CenteredI_field p hp]

theorem originalWactQ_origin (p : ℕ) [Fact p.Prime] :
    (originalWactQ p).eval 0 = 0 := by
  simp only [originalWactQ, eval_mul, eval_sub, eval_C,
    originalE4CenteredQ, originalE1CenteredQ, eval_comp,
    WPFiniteWSource.squaredCoordinate, eval_add, eval_X, eval_one]
  norm_num

theorem originalWbarQ_origin (p : ℕ) [Fact p.Prime] :
    (originalWbarQ p).eval 0 = 0 := by
  simp only [originalWbarQ, eval_mul, eval_sub, eval_C,
    originalE4CenteredQ, originalE1CenteredQ, eval_comp,
    WPFiniteWSource.squaredCoordinate, eval_add, eval_X, eval_one]
  norm_num

/-- The full rational first difference keeps W1's final band before reduction. -/
theorem originalWactQ_first_difference (p : ℕ) [Fact p.Prime] :
    originalWactQ p - originalWbarQ p = Polynomial.C (p : ℚ) * originalW1Q p := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hfour : (4 : ℚ) ^ ((p - 1) / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hc : (2 * (5 : ℚ) ^ ((p - 1) / 2) / 15) *
        (((4 : ℚ) ^ ((p - 1) / 2))⁻¹ - 1) =
      (p : ℚ) * (-2 * (5 : ℚ) ^ ((p - 1) / 2) * originalFourCarryQ p /
        (15 * (4 : ℚ) ^ ((p - 1) / 2))) := by
    rw [originalFourCarryQ]
    field_simp [hpq, hfour]
    ring
  have hC := congrArg Polynomial.C hc
  simp only [map_mul, map_sub, map_one] at hC
  unfold originalWactQ originalWbarQ originalW1Q
  linear_combination originalE4CenteredQ p * hC

theorem originalWactQ_coordinate_derivative :
    (WPFiniteWSource.squaredCoordinate : ℚ[X]).derivative = Polynomial.C (1 / 5 : ℚ) := by
  norm_num [WPFiniteWSource.squaredCoordinate, derivative_mul,
    derivative_add, derivative_C, derivative_X, derivative_one]

theorem originalWactQ_coordinate_four :
    (WPFiniteZSource.Abar : ℚ[X]) * Polynomial.C (4 / 5 : ℚ) =
      -2 * (4 - X) * (2 * (1 - 4 * WPFiniteWSource.squaredCoordinate)) := by
  have h5 : (5 : ℚ[X]) * Polynomial.C (1 / 5 : ℚ) = 1 := by
    rw [show (5 : ℚ[X]) = Polynomial.C (5 : ℚ) from rfl, ← map_mul]
    norm_num
  have hc4 : (Polynomial.C (4 / 5 : ℚ) : ℚ[X]) = 4 * Polynomial.C (1 / 5 : ℚ) := by
    rw [show (4 : ℚ[X]) = Polynomial.C (4 : ℚ) from rfl, ← map_mul]
    congr 1
    norm_num
  rw [hc4, WPFiniteWSource.squaredCoordinate, WPFiniteZSource.Abar]
  simp only [one_div] at h5 ⊢
  linear_combination -4 * (4 - X) * h5

theorem originalWactQ_coordinate_one :
    (WPFiniteZSource.Abar : ℚ[X]) * Polynomial.C (1 / 5 : ℚ) =
      Polynomial.C (1 / 2 : ℚ) * (4 * X - 1) *
        (2 * (1 - WPFiniteWSource.squaredCoordinate)) := by
  have h5 : (5 : ℚ[X]) * Polynomial.C (1 / 5 : ℚ) = 1 := by
    rw [show (5 : ℚ[X]) = Polynomial.C (5 : ℚ) from rfl, ← map_mul]
    norm_num
  have h2 : (2 : ℚ[X]) * Polynomial.C (1 / 2 : ℚ) = 1 := by
    rw [show (2 : ℚ[X]) = Polynomial.C (2 : ℚ) from rfl, ← map_mul]
    norm_num
  rw [WPFiniteWSource.squaredCoordinate, WPFiniteZSource.Abar]
  simp only [one_div] at h5 h2 ⊢
  linear_combination (4 * X - 1) * h5 -
    (4 * X - 1) * (1 - Polynomial.C ((5 : ℚ)⁻¹) * (X + 1)) * h2

theorem originalWactQ_coordinate_power (N : ℕ) :
    Polynomial.C ((5 : ℚ) ^ N) * WPFiniteWSource.squaredCoordinate ^ N =
      (X + 1 : ℚ[X]) ^ N := by
  rw [WPFiniteWSource.squaredCoordinate, mul_pow, ← map_pow, ← mul_assoc,
    ← map_mul, ← mul_pow]
  norm_num

/-- Collect the two division sources in an arbitrary commutative ring. -/
theorem originalWactQ_derivative_collection {R : Type*} [CommRing R]
    (A L v s x d4 d1 c4 c1 c2 : R)
    (hfour : A * c4 = -2 * (4 - x) * (2 * (1 - 4 * s)))
    (hone : A * c1 = c2 * (4 * x - 1) * (2 * (1 - s))) :
    A * (L * (v * (d4 * c4) - d1 * c1)) =
      L * (v * (-2 * (4 - x) * (2 * (1 - 4 * s) * d4)) -
        c2 * (4 * x - 1) * (2 * (1 - s) * d1)) := by
  linear_combination L * v * d4 * hfour - L * d1 * hone

/-- The affine scalar collection uses only the original factor of two. -/
theorem originalWactQ_affine_collection {R : Type*} [CommRing R]
    (L x c2 cN : R) (h2 : 2 * c2 = 1) (hL : L * (15 * c2) = cN) :
    L * (2 * (4 - x) + c2 * (4 * x - 1)) = cN := by
  linear_combination -2 * L * (4 - x) * h2 + hL

/-- Collect the whole power contribution before any polynomial is substituted. -/
theorem originalWactQ_power_collection {R : Type*} [CommRing R]
    (L v c4 c2 x t : R) (hscaled : v * c4 = 1) :
    L * (v * (-2 * (4 - x) * (1 - c4 * t)) -
      c2 * (4 * x - 1) * (1 - t)) =
      t * (L * (2 * (4 - x) + c2 * (4 * x - 1))) -
        (4 - x) * (L * v * 2) - (4 * x - 1) * (L * c2) := by
  linear_combination L * 2 * (4 - x) * t * hscaled

/-- Preserve the scalar order when the complete power source is substituted. -/
theorem originalWactQ_final_collection {R : Type*} [CommRing R]
    (L v c2 x t cN cv cr y : R)
    (hL : L * (2 * (4 - x) + c2 * (4 * x - 1)) = cN)
    (hv : L * v * 2 = cv) (hr : L * c2 = cr) (hN : cN * t = y) :
    t * (L * (2 * (4 - x) + c2 * (4 * x - 1))) -
      (4 - x) * (L * v * 2) - (4 * x - 1) * (L * c2) =
        y - cv * (4 - x) - cr * (4 * x - 1) := by
  rw [hL, hv, hr]
  linear_combination hN

theorem originalWactQ_coordinate_generic_derivative {K : Type*} [Field K] [CharZero K] :
    (WPFiniteWSource.squaredCoordinate : K[X]).derivative = Polynomial.C (1 / 5 : K) := by
  norm_num [WPFiniteWSource.squaredCoordinate, derivative_mul,
    derivative_add, derivative_C, derivative_X, derivative_one]

theorem originalWactQ_coordinate_generic_four {K : Type*} [Field K] [CharZero K] :
    (WPFiniteZSource.Abar : K[X]) * Polynomial.C (4 / 5 : K) =
      -2 * (4 - X) * (2 * (1 - 4 * WPFiniteWSource.squaredCoordinate)) := by
  have h5 : (5 : K[X]) * Polynomial.C (1 / 5 : K) = 1 := by
    rw [show (5 : K[X]) = Polynomial.C (5 : K) from rfl, ← map_mul]
    norm_num
  have hc4 : (Polynomial.C (4 / 5 : K) : K[X]) = 4 * Polynomial.C (1 / 5 : K) := by
    rw [show (4 : K[X]) = Polynomial.C (4 : K) from rfl, ← map_mul]
    congr 1
    norm_num
  rw [hc4, WPFiniteWSource.squaredCoordinate, WPFiniteZSource.Abar]
  simp only [one_div] at h5 ⊢
  linear_combination -4 * (4 - X) * h5

theorem originalWactQ_coordinate_generic_one {K : Type*} [Field K] [CharZero K] :
    (WPFiniteZSource.Abar : K[X]) * Polynomial.C (1 / 5 : K) =
      Polynomial.C (1 / 2 : K) * (4 * X - 1) *
        (2 * (1 - WPFiniteWSource.squaredCoordinate)) := by
  have h5 : (5 : K[X]) * Polynomial.C (1 / 5 : K) = 1 := by
    rw [show (5 : K[X]) = Polynomial.C (5 : K) from rfl, ← map_mul]
    norm_num
  have h2 : (2 : K[X]) * Polynomial.C (1 / 2 : K) = 1 := by
    rw [show (2 : K[X]) = Polynomial.C (2 : K) from rfl, ← map_mul]
    norm_num
  rw [WPFiniteWSource.squaredCoordinate, WPFiniteZSource.Abar]
  simp only [one_div] at h5 h2 ⊢
  linear_combination (4 * X - 1) * h5 -
    (4 * X - 1) * (1 - Polynomial.C ((5 : K)⁻¹) * (X + 1)) * h2

theorem originalWactQ_coordinate_generic_power {K : Type*} [Field K] [CharZero K] (N : ℕ) :
    Polynomial.C ((5 : K) ^ N) * WPFiniteWSource.squaredCoordinate ^ N =
      (X + 1 : K[X]) ^ N := by
  rw [WPFiniteWSource.squaredCoordinate, mul_pow, ← map_pow, ← mul_assoc,
    ← map_mul, ← mul_pow]
  norm_num

/- Separate the calculus from the finite source before substituting the
original coordinates and scalar powers. Both endpoint constants remain. -/
theorem originalWactQ_centered_difference_derivative {K : Type*} [CommRing K]
    (L v a b c4 c1 : K) (s4 s1 E : K[X])
    (hd4 : s4.derivative = Polynomial.C c4)
    (hd1 : s1.derivative = Polynomial.C c1) :
    (Polynomial.C L *
      (Polynomial.C v * (E.comp s4 - Polynomial.C a) -
        (E.comp s1 - Polynomial.C b))).derivative =
      Polynomial.C L *
        (Polynomial.C v * ((E.derivative.comp s4) * Polynomial.C c4) -
          (E.derivative.comp s1) * Polynomial.C c1) := by
  rw [derivative_C_mul, derivative_sub, derivative_C_mul, derivative_sub,
    derivative_sub, derivative_C, derivative_C, sub_zero, sub_zero,
    derivative_comp, derivative_comp, hd4, hd1]
  ring

/- The full algebra is collected over a ring before any polynomial is
substituted. The nine multipliers retain all original scalar/source terms. -/
theorem originalWactQ_full_collection {R : Type*} [CommRing R]
    (A L v s x d4 d1 cs4 cs1 c2 cp4 t cN cv cr y : R)
    (hfour : A * cs4 = -2 * (4 - x) * (2 * (1 - 4 * s)))
    (hone : A * cs1 = c2 * (4 * x - 1) * (2 * (1 - s)))
    (h4 : 2 * (1 - 4 * s) * d4 = 1 - cp4 * t)
    (h1 : 2 * (1 - s) * d1 = 1 - t)
    (hscaled : v * cp4 = 1)
    (hL : L * (2 * (4 - x) + c2 * (4 * x - 1)) = cN)
    (hv : L * v * 2 = cv) (hr : L * c2 = cr) (hN : cN * t = y) :
    A * (L * (v * (d4 * cs4) - d1 * cs1)) =
      y - cv * (4 - x) - cr * (4 * x - 1) := by
  linear_combination
    L * v * d4 * hfour - L * d1 * hone -
      2 * L * v * (4 - x) * h4 - L * c2 * (4 * x - 1) * h1 +
      2 * L * t * (4 - x) * hscaled + t * hL -
      (4 - x) * hv - (4 * x - 1) * hr + hN

set_option diagnostics true in
/-- The division calculation keeps the finite source as an arbitrary polynomial. -/
theorem originalWactQ_division_generic {K : Type*} [Field K] [CharZero K] (N : ℕ) (E : K[X])
    (hsource : 2 * (1 - X) * E.derivative = 1 - X ^ N) :
    (WPFiniteZSource.Abar : K[X]) *
      (Polynomial.C (2 * (5 : K) ^ N / 15) *
        (Polynomial.C (((4 : K) ^ N)⁻¹) *
          (E.comp (4 * WPFiniteWSource.squaredCoordinate) - Polynomial.C (E.eval (4 / 5))) -
          (E.comp WPFiniteWSource.squaredCoordinate - Polynomial.C (E.eval (1 / 5))))).derivative =
      (X + 1) ^ N - Polynomial.C (4 * (5 : K) ^ N / (15 * (4 : K) ^ N)) * (4 - X) -
        Polynomial.C ((5 : K) ^ N / 15) * (4 * X - 1) := by
  let s : K[X] := WPFiniteWSource.squaredCoordinate
  have h4 := congrArg (fun F : K[X] => F.comp (4 * s)) hsource
  have h1 := congrArg (fun F : K[X] => F.comp s) hsource
  simp only [mul_comp, ofNat_comp, sub_comp, one_comp, X_comp, pow_comp] at h4 h1
  simp only [Nat.cast_ofNat] at h4 h1
  have hd : s.derivative = Polynomial.C (1 / 5 : K) := originalWactQ_coordinate_generic_derivative
  have hd4 : (4 * s).derivative = Polynomial.C (4 / 5 : K) := by
    rw [show (4 : K[X]) = Polynomial.C (4 : K) from rfl, derivative_C_mul, hd,
      ← Polynomial.C_mul]
    congr 1
    norm_num
  have hfour : (4 : K) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  have hscaled : Polynomial.C (((4 : K) ^ N)⁻¹) *
      Polynomial.C ((4 : K) ^ N) = (1 : K[X]) := by
    rw [← map_mul, inv_mul_cancel₀ hfour, map_one]
  have hp4 : (4 * s) ^ N = Polynomial.C ((4 : K) ^ N) * s ^ N := by
    rw [mul_pow, Polynomial.C_pow, map_ofNat]
  have h2 : 2 * Polynomial.C (1 / 2 : K) = (1 : K[X]) := by
    rw [show (2 : K[X]) = Polynomial.C (2 : K) from rfl, ← map_mul]
    norm_num
  have hf4 : (WPFiniteZSource.Abar : K[X]) * Polynomial.C (4 / 5 : K) =
      -2 * (4 - X) * (2 * (1 - 4 * s)) := originalWactQ_coordinate_generic_four
  have hf1 : (WPFiniteZSource.Abar : K[X]) * Polynomial.C (1 / 5 : K) =
      Polynomial.C (1 / 2 : K) * (4 * X - 1) * (2 * (1 - s)) :=
    originalWactQ_coordinate_generic_one
  let L : K[X] := Polynomial.C (2 * (5 : K) ^ N / 15)
  have hcLr : L * Polynomial.C (1 / 2 : K) = Polynomial.C ((5 : K) ^ N / 15) := by
    dsimp only [L]
    rw [← map_mul]
    congr 1
    ring
  have hcLv : L * Polynomial.C (((4 : K) ^ N)⁻¹) * 2 =
      Polynomial.C (4 * (5 : K) ^ N / (15 * (4 : K) ^ N)) := by
    dsimp only [L]
    rw [show (2 : K[X]) = Polynomial.C (2 : K) from rfl, ← map_mul, ← map_mul]
    congr 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hcL : L * (15 * Polynomial.C (1 / 2 : K)) = Polynomial.C ((5 : K) ^ N) := by
    dsimp only [L]
    rw [show (15 : K[X]) = Polynomial.C (15 : K) from rfl, ← map_mul, ← map_mul]
    congr 1
    ring
  have huL : L * (2 * (4 - X) + Polynomial.C (1 / 2 : K) * (4 * X - 1)) =
      Polynomial.C ((5 : K) ^ N) := by
    exact originalWactQ_affine_collection L X (Polynomial.C (1 / 2 : K))
      (Polynomial.C ((5 : K) ^ N)) h2 hcL
  have hsN : Polynomial.C ((5 : K) ^ N) * s ^ N = (X + 1) ^ N :=
    originalWactQ_coordinate_generic_power N
  rw [originalWactQ_centered_difference_derivative
    (2 * (5 : K) ^ N / 15) (((4 : K) ^ N)⁻¹) (E.eval (4 / 5)) (E.eval (1 / 5))
    (4 / 5) (1 / 5) (4 * s) s E hd4 hd]
  change (WPFiniteZSource.Abar : K[X]) *
    (L *
      (Polynomial.C (((4 : K) ^ N)⁻¹) *
        ((E.derivative.comp (4 * s)) * Polynomial.C (4 / 5 : K)) -
        (E.derivative.comp s) * Polynomial.C (1 / 5 : K))) = _
  change 2 * (1 - 4 * s) * E.derivative.comp (4 * s) = 1 - (4 * s) ^ N at h4
  change 2 * (1 - s) * E.derivative.comp s = 1 - s ^ N at h1
  rw [hp4] at h4
  exact originalWactQ_full_collection WPFiniteZSource.Abar L
    (Polynomial.C (((4 : K) ^ N)⁻¹)) s X (E.derivative.comp (4 * s))
    (E.derivative.comp s) (Polynomial.C (4 / 5 : K))
    (Polynomial.C (1 / 5 : K)) (Polynomial.C (1 / 2 : K))
    (Polynomial.C ((4 : K) ^ N)) (s ^ N) (Polynomial.C ((5 : K) ^ N))
    (Polynomial.C (4 * (5 : K) ^ N / (15 * (4 : K) ^ N)))
    (Polynomial.C ((5 : K) ^ N / 15)) ((X + 1) ^ N)
    hf4 hf1 h4 h1 hscaled huL hcLv hcLr hsN

/-- The same actual rational identity is the characteristic-zero specialization. -/
theorem originalWactQ_division_core (N : ℕ) (E : ℚ[X])
    (hsource : 2 * (1 - X) * E.derivative = 1 - X ^ N) :
    (WPFiniteZSource.Abar : ℚ[X]) *
      (Polynomial.C (2 * (5 : ℚ) ^ N / 15) *
        (Polynomial.C (((4 : ℚ) ^ N)⁻¹) *
          (E.comp (4 * WPFiniteWSource.squaredCoordinate) - Polynomial.C (E.eval (4 / 5))) -
          (E.comp WPFiniteWSource.squaredCoordinate - Polynomial.C (E.eval (1 / 5))))).derivative =
      (X + 1) ^ N - Polynomial.C (4 * (5 : ℚ) ^ N / (15 * (4 : ℚ) ^ N)) * (4 - X) -
        Polynomial.C ((5 : ℚ) ^ N / 15) * (4 * X - 1) := by
  exact originalWactQ_division_generic (K := ℚ) N E hsource

/-- UW16a's actual rational division quotient, proved from the complete finite source. -/
theorem originalWactQ_division (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : ℚ[X]) * (originalWactQ p).derivative =
      (X + 1) ^ ((p - 1) / 2) -
      Polynomial.C (4 * (5 : ℚ) ^ ((p - 1) / 2) /
        (15 * (4 : ℚ) ^ ((p - 1) / 2))) * (4 - X) -
      Polynomial.C ((5 : ℚ) ^ ((p - 1) / 2) / 15) * (4 * X - 1) := by
  exact originalWactQ_division_core ((p - 1) / 2) (finiteEvenSquaredQ p)
    (finiteEvenSquaredQ_source p hp)

/-- The division identity and its original zero origin specify Wact over Q. -/
theorem originalWactQ_unique (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (F : ℚ[X]) (h0 : F.eval 0 = 0)
    (hF : (WPFiniteZSource.Abar : ℚ[X]) * F.derivative =
      (X + 1) ^ ((p - 1) / 2) -
      Polynomial.C (4 * (5 : ℚ) ^ ((p - 1) / 2) /
        (15 * (4 : ℚ) ^ ((p - 1) / 2))) * (4 - X) -
      Polynomial.C ((5 : ℚ) ^ ((p - 1) / 2) / 15) * (4 * X - 1)) :
    F = originalWactQ p := by
  let G := F - originalWactQ p
  have hA : (WPFiniteZSource.Abar : ℚ[X]) ≠ 0 := by
    intro hz
    have he := congrArg (fun P : ℚ[X] => P.eval 0) hz
    norm_num [WPFiniteZSource.Abar] at he
  have hD : (WPFiniteZSource.Abar : ℚ[X]) * G.derivative = 0 := by
    dsimp only [G]
    rw [derivative_sub, mul_sub, hF, originalWactQ_division p hp, sub_self]
  have hd : G.derivative = 0 := (mul_eq_zero.mp hD).resolve_left hA
  have hc := eq_C_of_derivative_eq_zero hd
  have hg : G.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    dsimp only [G]
    rw [eval_sub, h0, originalWactQ_origin, sub_self]
  rw [hg, Polynomial.C_0] at hc
  exact sub_eq_zero.mp hc

end WPFieldAssembly.ActualUW16PrimitiveSource
