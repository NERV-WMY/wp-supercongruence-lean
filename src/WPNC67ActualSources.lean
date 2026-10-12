import WPQuadraticRationalCartier
import WPNC67ProjectionIntegrals
import WPCartierPoleProjection

open scoped Polynomial LaurentPolynomial
open LaurentPolynomial WPRationalCartier WPQuadraticRationalCartier
open WPPIntegralReduction WPNC67ProjectionIntegrals

namespace WPNC67ActualSources

variable (p : ℕ) [Fact p.Prime]

/-- Literal V after x=y², over the residue field. -/
noncomputable def actualV : (ZMod p)[T;T⁻¹] :=
  C (1 / 125) * (4 * T 2 - 1) ^ 2 * (4 - T 2)

noncomputable def actualS : (ZMod p)[T;T⁻¹] := actualV p * T (-1)

private theorem pole_ne_zero (a : ZMod p) :
    (RatFunc.X - RatFunc.C a : RatFunc (ZMod p)) ≠ 0 := by
  have h := RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero a)
  simpa using h

private theorem field_units (hp : 19 ≤ p) :
    (2 : RatFunc (ZMod p)) ≠ 0 ∧ (4 : RatFunc (ZMod p)) ≠ 0 ∧
      (125 : RatFunc (ZMod p)) ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have := Nat.le_of_dvd (by omega : 0 < 2) hd
    omega
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 5 p).mp h
    have := Nat.le_of_dvd (by omega : 0 < 5) hd
    omega
  have hc2 : (2 : RatFunc (ZMod p)) ≠ 0 := by
    have h : RatFunc.C (2 : ZMod p) ≠ 0 := (map_ne_zero RatFunc.C).mpr h2
    simpa only [map_ofNat] using h
  have hc5 : (5 : RatFunc (ZMod p)) ≠ 0 := by
    have h : RatFunc.C (5 : ZMod p) ≠ 0 := (map_ne_zero RatFunc.C).mpr h5
    simpa only [map_ofNat] using h
  have hc4 : (4 : RatFunc (ZMod p)) ≠ 0 := by
    convert pow_ne_zero 2 hc2 using 1; norm_num
  have hc125 : (125 : RatFunc (ZMod p)) ≠ 0 := by
    convert pow_ne_zero 3 hc5 using 1; norm_num
  exact ⟨hc2, hc4, hc125⟩

private theorem substituted_denominator_ne_zero (Q : (ZMod p)[T;T⁻¹])
    (hQ : evaluate p Q ≠ 0) : evaluate p (squareSubstitute p Q) ≠ 0 := by
  intro h
  have hQ0 : Q = 0 := squareSubstitute_injective p
    (evaluate_injective p (by simpa using h))
  exact hQ (by rw [hQ0, map_zero])

theorem actualV_evaluate : evaluate p (actualV p) =
    (4 * RatFunc.X ^ (2 : ℕ) - 1) ^ 2 * (4 - RatFunc.X ^ (2 : ℕ)) / 125 := by
  simp only [actualV, map_mul, map_sub, map_pow, map_ofNat, map_one,
    evaluate_C, evaluate_T, map_div₀]
  norm_num only [zpow_ofNat]
  ring

theorem actualS_evaluate : evaluate p (actualS p) = evaluate p (actualV p) / RatFunc.X := by
  rw [actualS, map_mul, evaluate_T, zpow_neg_one, div_eq_mul_inv]

/-- Exact cancellation against x-1/4 retains the whole numerator. -/
theorem poleA_actual_source (hp : 19 ≤ p) :
    evaluate p (poleA p) = 2 * evaluate p (actualV p) /
      (RatFunc.X ^ (2 : ℕ) - RatFunc.C (1 / 4 : ZMod p)) := by
  obtain ⟨h2, h4, h125⟩ := field_units p hp
  have hd : (RatFunc.X ^ (2 : ℕ) - RatFunc.C (1 / 4 : ZMod p) : RatFunc (ZMod p)) ≠ 0 := by
    have h := substituted_denominator_ne_zero p (T 1 - C (1 / 4)) (by
      simpa only [map_sub, evaluate_T, evaluate_C, zpow_one] using pole_ne_zero p (1 / 4))
    simpa only [map_sub, squareSubstitute_T, squareSubstitute_C,
      evaluate_T, evaluate_C, Int.reduceMul, zpow_ofNat] using h
  simp only [poleA, map_add, map_mul, evaluate_C, evaluate_T, map_neg,
    map_div₀, map_ofNat, map_one, zpow_zero, mul_one]
  norm_num only [zpow_ofNat]
  rw [actualV_evaluate]
  field_simp [h2, h4, h125, hd]
  ring

theorem poleB_actual_source (hp : 19 ≤ p) :
    evaluate p (poleB p) = 2 * evaluate p (actualV p) / (RatFunc.X ^ (2 : ℕ) - 4) := by
  obtain ⟨h2, h4, h125⟩ := field_units p hp
  have hd : (RatFunc.X ^ (2 : ℕ) - 4 : RatFunc (ZMod p)) ≠ 0 := by
    have h := substituted_denominator_ne_zero p (T 1 - C 4) (by
      simpa only [map_sub, evaluate_T, evaluate_C, zpow_one, map_ofNat] using pole_ne_zero p 4)
    simpa only [map_sub, squareSubstitute_T, squareSubstitute_C,
      evaluate_T, evaluate_C, map_ofNat, Int.reduceMul, zpow_ofNat] using h
  simp only [poleB, map_add, map_mul, evaluate_C, evaluate_T, map_neg,
    map_div₀, map_ofNat, zpow_zero, mul_one]
  norm_num only [zpow_ofNat]
  rw [actualV_evaluate]
  field_simp [h2, h4, h125, hd]
  ring

theorem logPole_actual_source (hp : 19 ≤ p) :
    evaluate p (logPole p) = 2 * evaluate p (actualV p) / RatFunc.X ^ (2 : ℕ) := by
  obtain ⟨h2, h4, h125⟩ := field_units p hp
  have hx : (RatFunc.X : RatFunc (ZMod p)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  simp only [logPole, map_add, map_mul, evaluate_C, evaluate_T, map_neg,
    map_div₀, map_ofNat, zpow_neg, zpow_zero, mul_one]
  norm_num only [zpow_ofNat]
  rw [actualV_evaluate]
  field_simp [h2, h4, h125, hx]
  ring

theorem constantPole_actual_source (hp : 19 ≤ p) :
    evaluate p (constantPole p) = 2 * evaluate p (actualV p) := by
  obtain ⟨h2, h4, h125⟩ := field_units p hp
  simp only [constantPole, map_add, map_mul, evaluate_C, evaluate_T, map_neg,
    map_div₀, map_ofNat, zpow_zero, mul_one]
  norm_num only [zpow_ofNat]
  rw [actualV_evaluate]
  field_simp [h2, h4, h125]
  ring

theorem quadraticRational_pole (a : ZMod p) :
    quadraticRational p (1 / (RatFunc.X - RatFunc.C a)) =
      2 * RatFunc.X / (RatFunc.X ^ (2 : ℕ) - RatFunc.C a) := by
  have hQ : evaluate p (T 1 - C a) ≠ 0 := by
    simpa only [map_sub, evaluate_T, evaluate_C, zpow_one] using pole_ne_zero p a
  have h := quadraticRational_fraction p 1 (T 1 - C a) hQ
  simpa only [map_one, map_sub, map_mul, squareSubstitute_T, squareSubstitute_C,
    evaluate_C, evaluate_T, zpow_one, Int.reduceMul, zpow_ofNat, pow_one,
    map_ofNat, mul_one] using h

private theorem source_pole_cancellation (a : ZMod p) :
    evaluate p (actualS p) * quadraticRational p (1 / (RatFunc.X - RatFunc.C a)) =
      2 * evaluate p (actualV p) / (RatFunc.X ^ (2 : ℕ) - RatFunc.C a) := by
  have hx : (RatFunc.X : RatFunc (ZMod p)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  rw [actualS_evaluate, quadraticRational_pole]
  field_simp [hx]

theorem poleA_square_source (hp : 19 ≤ p) :
    evaluate p (poleA p) = evaluate p (actualS p) *
      quadraticRational p (1 / (RatFunc.X - RatFunc.C (1 / 4 : ZMod p))) := by
  rw [source_pole_cancellation, poleA_actual_source p hp]

theorem poleB_square_source (hp : 19 ≤ p) :
    evaluate p (poleB p) = evaluate p (actualS p) *
      quadraticRational p (1 / (RatFunc.X - RatFunc.C (4 : ZMod p))) := by
  rw [source_pole_cancellation, poleB_actual_source p hp, map_ofNat]

theorem logPole_square_source (hp : 19 ≤ p) :
    evaluate p (logPole p) = evaluate p (actualS p) *
      quadraticRational p (1 / RatFunc.X) := by
  have h := source_pole_cancellation p 0
  simp only [map_zero, sub_zero] at h
  exact (logPole_actual_source p hp).trans h.symm

theorem constantPole_square_source (hp : 19 ≤ p) :
    evaluate p (constantPole p) = evaluate p (actualS p) * quadraticRational p 1 := by
  have hx : (RatFunc.X : RatFunc (ZMod p)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have hq : quadraticRational p 1 = 2 * RatFunc.X := by
    have h := quadraticRational_evaluate p 1
    simpa only [map_one, quadraticPullback_eq, map_mul, evaluate_C, evaluate_T,
      zpow_one, map_ofNat, mul_one] using h
  rw [constantPole_actual_source p hp, actualS_evaluate, hq]
  field_simp [hx]

/-- The full four-component canceled differential, before primitive evaluation. -/
noncomputable def fourSource (α β c d : ZMod p) : (ZMod p)[T;T⁻¹] :=
  α • poleA p + β • poleB p + c • logPole p + d • constantPole p

theorem fourSource_integral (hp : 19 ≤ p) (α β c d : ZMod p) :
    fieldPrimitive p (fourSource p α β c d) =
      α * (522 / 625) + β * (-828 / 625) + c * (432 / 625) + d * (6102 / 4375) := by
  simp only [fourSource, map_add, map_smul, poleA_integral p hp,
    poleB_integral p hp, logPole_integral p hp, constantPole_integral p hp]
  rfl

private theorem quadratic_common_add (P R Q : (ZMod p)[T;T⁻¹])
    (hQ : evaluate p Q ≠ 0) :
    quadraticRational p (evaluate p (P + R) / evaluate p Q) =
      quadraticRational p (evaluate p P / evaluate p Q) +
        quadraticRational p (evaluate p R / evaluate p Q) := by
  rw [quadraticRational_fraction p (P + R) Q hQ,
    quadraticRational_fraction p P Q hQ, quadraticRational_fraction p R Q hQ]
  simp only [map_add, mul_add, add_div]

theorem quadraticRational_add (f g : RatFunc (ZMod p)) :
    quadraticRational p (f + g) = quadraticRational p f + quadraticRational p g := by
  let A : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent f.num
  let B : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent f.denom
  let P : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent g.num
  let Q : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent g.denom
  have hB : evaluate p B ≠ 0 := by
    rw [show B = Polynomial.toLaurent f.denom by rfl, evaluate_toLaurent]
    exact RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)
  have hQ : evaluate p Q ≠ 0 := by
    rw [show Q = Polynomial.toLaurent g.denom by rfl, evaluate_toLaurent]
    exact RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero g)
  have hf : f = evaluate p A / evaluate p B := by
    rw [show A = Polynomial.toLaurent f.num by rfl,
      show B = Polynomial.toLaurent f.denom by rfl, evaluate_toLaurent,
      evaluate_toLaurent, RatFunc.num_div_denom]
  have hg : g = evaluate p P / evaluate p Q := by
    rw [show P = Polynomial.toLaurent g.num by rfl,
      show Q = Polynomial.toLaurent g.denom by rfl, evaluate_toLaurent,
      evaluate_toLaurent, RatFunc.num_div_denom]
  have hf' : f = evaluate p (A * Q) / evaluate p (B * Q) := by
    rw [hf, map_mul, map_mul]
    field_simp
  have hg' : g = evaluate p (P * B) / evaluate p (B * Q) := by
    rw [hg, map_mul, map_mul]
    field_simp
  rw [hf', hg', ← add_div, ← map_add]
  exact quadratic_common_add p (A * Q) (P * B) (B * Q)
    (by rw [map_mul]; exact mul_ne_zero hB hQ)

theorem quadraticRational_const_mul (a : ZMod p) (f : RatFunc (ZMod p)) :
    quadraticRational p (RatFunc.C a * f) = RatFunc.C a * quadraticRational p f := by
  let A : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent f.num
  let B : (ZMod p)[T;T⁻¹] := Polynomial.toLaurent f.denom
  have hB : evaluate p B ≠ 0 := by
    rw [show B = Polynomial.toLaurent f.denom by rfl, evaluate_toLaurent]
    exact RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)
  have hf : f = evaluate p A / evaluate p B := by
    rw [show A = Polynomial.toLaurent f.num by rfl,
      show B = Polynomial.toLaurent f.denom by rfl, evaluate_toLaurent,
      evaluate_toLaurent, RatFunc.num_div_denom]
  rw [hf, ← mul_div_assoc, ← evaluate_C p a, ← map_mul,
    quadraticRational_fraction p (C a * A) B hB, quadraticRational_fraction p A B hB]
  simp only [map_mul, squareSubstitute_C, evaluate_C]
  ring

theorem fourSource_evaluate (hp : 19 ≤ p) (α β c d : ZMod p) :
    evaluate p (fourSource p α β c d) = evaluate p (actualS p) *
      quadraticRational p (RatFunc.C α / (RatFunc.X - RatFunc.C (1 / 4 : ZMod p)) +
        RatFunc.C β / (RatFunc.X - RatFunc.C (4 : ZMod p)) +
          RatFunc.C c / RatFunc.X + RatFunc.C d) := by
  have hc (a : ZMod p) (f : RatFunc (ZMod p)) :
      quadraticRational p (RatFunc.C a / f) =
        RatFunc.C a * quadraticRational p (1 / f) := by
    simpa only [← mul_div_assoc, mul_one] using quadraticRational_const_mul p a (1 / f)
  have hd : quadraticRational p (RatFunc.C d) =
      RatFunc.C d * quadraticRational p 1 := by
    simpa only [mul_one] using quadraticRational_const_mul p d 1
  simp only [fourSource, smul_eq_C_mul, map_add, map_mul, evaluate_C,
    quadraticRational_add, hc, hd]
  rw [poleA_square_source p hp, poleB_square_source p hp,
    logPole_square_source p hp, constantPole_square_source p hp]
  ring

theorem resonanceMinus_actual_source (hp : 19 ≤ p) :
    evaluate p (resonanceMinus p) = 2 * evaluate p (actualV p) / RatFunc.X ^ (4 : ℕ) := by
  obtain ⟨h2, h4, h125⟩ := field_units p hp
  have hx : (RatFunc.X : RatFunc (ZMod p)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  simp only [resonanceMinus, map_add, map_mul, evaluate_C, evaluate_T, map_neg,
    map_div₀, map_ofNat, zpow_neg, zpow_zero, mul_one]
  norm_num only [zpow_ofNat]
  rw [actualV_evaluate]
  field_simp [h2, h4, h125, hx]
  ring

theorem resonancePlus_actual_source (hp : 19 ≤ p) :
    evaluate p (resonancePlus p) = 2 * evaluate p (actualV p) := by
  exact constantPole_actual_source p hp

theorem resonanceTwo_actual_source (hp : 19 ≤ p) :
    evaluate p (resonanceTwo p) = 2 * evaluate p (actualV p) * RatFunc.X ^ (2 : ℕ) := by
  obtain ⟨h2, h4, h125⟩ := field_units p hp
  simp only [resonanceTwo, map_add, map_mul, evaluate_C, evaluate_T, map_neg,
    map_div₀, map_ofNat]
  norm_num only [zpow_ofNat]
  rw [actualV_evaluate]
  field_simp [h2, h4, h125]
  ring

open WPCartierPoleProjection

/-- The entire NC65 output, with its negative and high-half sums unchanged. -/
noncomputable def projectedSource (A : (ZMod p)[T;T⁻¹]) : (ZMod p)[T;T⁻¹] :=
  fourSource p (2 * valueAt p A (1 / 4)) (valueAt p A 4)
    (-2 * negativeValue p A (1 / 4) - negativeValue p A 4)
    (8 * highValue p A (1 / 4) + highValue p A 4 / 4)

noncomputable def logarithmicX : RatFunc (ZMod p) :=
  2 / (RatFunc.X - RatFunc.C (1 / 4 : ZMod p)) +
    1 / (RatFunc.X - RatFunc.C (4 : ZMod p)) - 1 / (2 * RatFunc.X)

theorem projectedSource_cartier (hp : 19 ≤ p) (A : (ZMod p)[T;T⁻¹])
    (hband : ∀ j ∈ A.coeff.support, -(p : ℤ) < j ∧ j < 2 * (p : ℤ))
    (h0 : A.coeff 0 = 0) (hslot : A.coeff (p : ℤ) = 0) :
    rationalCartier p (evaluate p (actualS p) ^ p *
      quadraticRational p (evaluate p A * logarithmicX p)) =
        evaluate p (projectedSource p A) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rw [rationalCartier_laurent_frobenius, rationalCartier_quadratic p hodd,
    logarithmicX, literal_two_pole_projection p (by omega) A hband h0 hslot,
    projectedSource, fourSource_evaluate p hp]
  simp only [map_mul, map_ofNat]

theorem projectedSource_integral (hp : 19 ≤ p) (A : (ZMod p)[T;T⁻¹]) :
    fieldPrimitive p (projectedSource p A) =
      (1044 / 625) * valueAt p A (1 / 4) - (828 / 625) * valueAt p A 4 +
        (432 / 625) * (-2 * negativeValue p A (1 / 4) - negativeValue p A 4) +
          (6102 / 4375) * (8 * highValue p A (1 / 4) + highValue p A 4 / 4) := by
  rw [projectedSource, fourSource_integral p hp]
  ring

/-- Exact full-band coefficient transport, with the original source equality explicit. -/
theorem full_band_primitive_evaluation (hp : 19 ≤ p) (A P : (ZMod p)[T;T⁻¹])
    (hband : ∀ j ∈ A.coeff.support, -(p : ℤ) < j ∧ j < 2 * (p : ℤ))
    (h0 : A.coeff 0 = 0) (hslot : A.coeff (p : ℤ) = 0)
    (hsource : evaluate p P = evaluate p (actualS p) ^ p *
      quadraticRational p (evaluate p A * logarithmicX p)) :
    fieldPrimitive p (WPFiniteCartier.cartier p (Fact.out : p.Prime).pos P) =
      (1044 / 625) * valueAt p A (1 / 4) - (828 / 625) * valueAt p A 4 +
        (432 / 625) * (-2 * negativeValue p A (1 / 4) - negativeValue p A 4) +
          (6102 / 4375) * (8 * highValue p A (1 / 4) + highValue p A 4 / 4) := by
  have he : WPFiniteCartier.cartier p (Fact.out : p.Prime).pos P = projectedSource p A := by
    apply evaluate_injective p
    rw [← rationalCartier_evaluate, hsource, projectedSource_cartier p hp A hband h0 hslot]
  rw [he, projectedSource_integral p hp]

theorem rational_full_band_primitive_evaluation (hp : 19 ≤ p)
    (A : (ZMod p)[T;T⁻¹]) (P : ℚ[T;T⁻¹])
    (hcoeff : ∀ j, 0 ≤ padicValRat p (P.coeff j))
    (hzero : ∀ j ∈ P.coeff.support, j + 1 ≠ 0)
    (hbound : ∀ j ∈ P.coeff.support, (j + 1).natAbs < p ^ 2)
    (hband : ∀ j ∈ A.coeff.support, -(p : ℤ) < j ∧ j < 2 * (p : ℤ))
    (h0 : A.coeff 0 = 0) (hslot : A.coeff (p : ℤ) = 0)
    (hsource : evaluate p (reduceLaurent p P) = evaluate p (actualS p) ^ p *
      quadraticRational p (evaluate p A * logarithmicX p)) :
    (rationalPrimitive p P : ZMod p) =
      (1044 / 625) * valueAt p A (1 / 4) - (828 / 625) * valueAt p A 4 +
        (432 / 625) * (-2 * negativeValue p A (1 / 4) - negativeValue p A 4) +
          (6102 / 4375) * (8 * highValue p A (1 / 4) + highValue p A 4 / 4) := by
  rw [rationalPrimitive_residue_cartier p (by omega) P hcoeff hzero hbound]
  exact full_band_primitive_evaluation p hp A (reduceLaurent p P) hband h0 hslot hsource

theorem resonanceMinus_square_source (hp : 19 ≤ p) :
    evaluate p (resonanceMinus p) = evaluate p (actualS p) *
      quadraticRational p (RatFunc.X ^ (-2 : ℤ)) := by
  have hx : (RatFunc.X : RatFunc (ZMod p)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have hq : quadraticRational p (RatFunc.X ^ (-2 : ℤ)) =
      2 * RatFunc.X ^ (-3 : ℤ) := by
    have h := quadraticRational_evaluate p (T (-2))
    calc
      _ = 2 * RatFunc.X * RatFunc.X ^ (-4 : ℤ) := by
        simpa only [evaluate_T, quadraticPullback_eq, map_mul, squareSubstitute_T,
          evaluate_C, map_ofNat, Int.reduceMul, zpow_one] using h
      _ = _ := by
        calc
          (2 : RatFunc (ZMod p)) * RatFunc.X * RatFunc.X ^ (-4 : ℤ) =
              2 * (RatFunc.X ^ (1 : ℤ) * RatFunc.X ^ (-4 : ℤ)) := by rw [zpow_one]; ring
          _ = 2 * RatFunc.X ^ (-3 : ℤ) := by rw [← zpow_add₀ hx]; norm_num
  rw [resonanceMinus_actual_source p hp, actualS_evaluate, hq]
  norm_num only [zpow_neg, zpow_ofNat]
  field_simp [hx]

theorem resonancePlus_square_source (hp : 19 ≤ p) :
    evaluate p (resonancePlus p) = evaluate p (actualS p) * quadraticRational p 1 :=
  constantPole_square_source p hp

theorem resonanceTwo_square_source (hp : 19 ≤ p) :
    evaluate p (resonanceTwo p) = evaluate p (actualS p) * quadraticRational p RatFunc.X := by
  have hx : (RatFunc.X : RatFunc (ZMod p)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have hq : quadraticRational p RatFunc.X = 2 * RatFunc.X ^ (3 : ℕ) := by
    have h := quadraticRational_evaluate p (T 1)
    calc
      _ = 2 * RatFunc.X * RatFunc.X ^ (2 : ℕ) := by
        simpa only [evaluate_T, quadraticPullback_eq, map_mul, squareSubstitute_T,
          evaluate_C, map_ofNat, Int.reduceMul, zpow_ofNat, pow_one] using h
      _ = _ := by ring
  rw [resonanceTwo_actual_source p hp, actualS_evaluate, hq]
  field_simp [hx]

end WPNC67ActualSources
