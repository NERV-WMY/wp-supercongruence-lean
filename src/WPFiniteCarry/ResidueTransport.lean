import WPFiniteCarry.InfinityExpansion
import WPActualPullbackSource
import WPActualEvenLogCarry
import WPActualRankTwoHatLift
import WPFiniteConductorPolynomial
import WPHasseIntegralTransport
import WPActualPositiveResidueSource

open scoped Polynomial LaurentSeries LaurentPolynomial
open Polynomial HahnSeries WPForcedSourceStokes WPActualPullbackSource
  WPPIntegralReduction WPActualRankTwoHatLift WPFiniteConductorPolynomial

namespace WPFiniteCarry

set_option maxHeartbeats 800000

noncomputable section

local instance originCharZero : CharZero (LaurentSeries ℚ) where
  cast_injective m n h := by
    have hc := congrArg (fun P : LaurentSeries ℚ => P.coeff 0) h
    rw [← single_zero_natCast (Γ := ℤ) (R := ℚ) m,
      ← single_zero_natCast (Γ := ℤ) (R := ℚ) n,
      coeff_single_same, coeff_single_same] at hc
    exact_mod_cast hc

local instance originAlgebra : Algebra ℚ (LaurentSeries ℚ) := powerSeriesAlgebra ℤ ℚ

/-- The original origin coordinate, as an honest formal Laurent series. -/
def originLaurentX : LaurentSeries ℚ := single (1 : ℤ) (1 : ℚ)

/-- Literal Q(x)=V(1/x), using the retained canonical V polynomial. -/
def originQ : LaurentSeries ℚ := infinityPolynomialHom Vpolynomial

/-- The original rational denominator 2A(x), before reduced-fraction cancellation. -/
def residueDenominator : ℚ[X] := 2 * ((4 - X) * (4 * X - 1))

/-- The actual NC81 K_x, before any polynomial-part extraction. -/
def residueKernel (p : ℕ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (X ^ ((p - 1) / 2) * (4 - 11 * X)) /
    algebraMap ℚ[X] (RatFunc ℚ) residueDenominator

/-- Full original-coordinate product K_x J(x), before extracting its polynomial part. -/
def originalRationalProduct (p : ℕ) (J : ℚ[X]) : RatFunc ℚ :=
  residueKernel p * algebraMap ℚ[X] (RatFunc ℚ) J

def originalPolynomialPart (p : ℕ) (J : ℚ[X]) : ℚ[X] :=
  rationalPolynomialPart (originalRationalProduct p J)

/-- The original density with the literal reciprocal J(1/x). -/
def originalOriginDensity (p : ℕ) (J : ℚ[X]) : LaurentSeries ℚ :=
  originLaurentX ^ ((p - 1) / 2) * infinityPolynomialHom J *
    (3 * (11 - 4 * originLaurentX)) /
      ((4 - originLaurentX) * (4 * originLaurentX - 1))

def originalOriginResidue (p : ℕ) (J : ℚ[X]) : ℚ :=
  (originalOriginDensity p J).coeff (-1 : ℤ)

/-- The full rational product K_x G(V(x)). -/
def residueRationalProduct (p : ℕ) (G : ℚ[X]) : RatFunc ℚ :=
  residueKernel p * algebraMap ℚ[X] (RatFunc ℚ) (G.comp Vpolynomial)

/-- The canonical full polynomial part, including every nonnegative infinity slot. -/
def residuePolynomialPart (p : ℕ) (G : ℚ[X]) : ℚ[X] :=
  rationalPolynomialPart (residueRationalProduct p G)

/-- Literal x^N G(Q(x)) 3(11-4x)/A(x) at the original origin. -/
def originDensity (p : ℕ) (G : ℚ[X]) : LaurentSeries ℚ :=
  originLaurentX ^ ((p - 1) / 2) * aeval originQ G *
    (3 * (11 - 4 * originLaurentX)) /
      ((4 - originLaurentX) * (4 * originLaurentX - 1))

/-- The actual original formal residue, with no zero-end assumption. -/
def actualOriginResidue (p : ℕ) (G : ℚ[X]) : ℚ :=
  (originDensity p G).coeff (-1 : ℤ)

theorem originLaurentX_ne_zero : originLaurentX ≠ 0 :=
  single_ne_zero one_ne_zero

theorem originLaurentX_inv : originLaurentX⁻¹ = single (-1 : ℤ) (1 : ℚ) := by
  simp [originLaurentX, inv_single]

theorem infinityPolynomialHom_X : infinityPolynomialHom X = originLaurentX⁻¹ := by
  change aeval (single (-1 : ℤ) (1 : ℚ) : LaurentSeries ℚ) X = _
  rw [aeval_X, originLaurentX_inv]

theorem infinityPolynomialHom_C (a : ℚ) :
    infinityPolynomialHom (Polynomial.C a) = single 0 a := by
  change aeval (single (-1 : ℤ) (1 : ℚ) : LaurentSeries ℚ) (Polynomial.C a) = _
  rw [aeval_C, LaurentSeries.algebraMap_apply, HahnSeries.C_apply]

theorem residueDenominator_ne_zero : residueDenominator ≠ 0 := by
  intro h
  have hc := congrArg (fun P : ℚ[X] => P.coeff 0) h
  norm_num [residueDenominator, Polynomial.coeff_mul] at hc

theorem residueDenominator_degree : residueDenominator.natDegree = 2 := by
  unfold residueDenominator
  compute_degree <;> norm_num

theorem residueDenominator_leadingCoeff : residueDenominator.leadingCoeff = -8 := by
  rw [← coeff_natDegree, residueDenominator_degree]
  have he : residueDenominator = -8 * X ^ 2 + 34 * X - 8 := by
    unfold residueDenominator
    ring
  rw [he]
  norm_num [Polynomial.coeff_X]

theorem origin_denominator_reciprocal :
    (4 - originLaurentX⁻¹) * (4 * originLaurentX⁻¹ - 1) =
      ((4 - originLaurentX) * (4 * originLaurentX - 1)) / originLaurentX ^ 2 := by
  field_simp [originLaurentX_ne_zero]

theorem origin_denominator_ne_zero :
    (4 - originLaurentX) * (4 * originLaurentX - 1) ≠ 0 := by
  have hP : ((4 - X) * (4 * X - 1) : ℚ[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun P : ℚ[X] => P.coeff 0) h
    norm_num [Polynomial.coeff_mul] at hc
  have hi := infinity_polynomial_nonzero _ hP
  have his : (4 - originLaurentX⁻¹) * (4 * originLaurentX⁻¹ - 1) ≠ 0 := by
    simpa only [map_mul, map_sub, map_ofNat, map_one, infinityPolynomialHom_X] using hi
  intro h
  apply his
  rw [origin_denominator_reciprocal, h, zero_div]

theorem rational_infinity_residueKernel (p : ℕ) :
    rationalInfinityHom (residueKernel p) =
      (originLaurentX⁻¹) ^ ((p - 1) / 2) * (4 - 11 * originLaurentX⁻¹) /
        (2 * ((4 - originLaurentX⁻¹) * (4 * originLaurentX⁻¹ - 1))) := by
  rw [residueKernel, rational_infinity_fraction]
  simp only [residueDenominator, map_mul, map_pow, map_sub, map_ofNat, map_one,
    infinityPolynomialHom_X]

theorem rational_infinity_residueProduct (p : ℕ) (G : ℚ[X]) :
    rationalInfinityHom (residueRationalProduct p G) =
      rationalInfinityHom (residueKernel p) * aeval originQ G := by
  rw [residueRationalProduct, map_mul, rational_infinity_polynomial]
  congr 1
  exact aeval_comp _

theorem residue_reciprocal_kernel (p : ℕ) :
    rationalInfinityHom (residueKernel p) =
      (originLaurentX⁻¹) ^ ((p - 1) / 2) * originLaurentX *
        (4 * originLaurentX - 11) /
          (2 * ((4 - originLaurentX) * (4 * originLaurentX - 1))) := by
  rw [rational_infinity_residueKernel, origin_denominator_reciprocal]
  field_simp [originLaurentX_ne_zero, origin_denominator_ne_zero]

theorem origin_reciprocal_power (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originLaurentX ^ (p - 2) * (originLaurentX⁻¹) ^ ((p - 1) / 2) *
      originLaurentX = originLaurentX ^ ((p - 1) / 2) := by
  have hN := WPActualEvenLogCarry.prime_half_identity p (by omega)
  have hPow : (p - 2) + 1 = (p - 1) / 2 + (p - 1) / 2 := by omega
  calc
    _ = originLaurentX ^ ((p - 2) + 1) * (originLaurentX ^ ((p - 1) / 2))⁻¹ := by
      rw [pow_succ, inv_pow]
      ring
    _ = _ := by
      rw [hPow, pow_add, mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ originLaurentX_ne_zero), mul_one]

/-- The identical reciprocal bridge for every original-coordinate polynomial. -/
theorem original_density_infinity (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (J : ℚ[X]) :
    originalOriginDensity p J = -6 * originLaurentX ^ (p - 2) *
      rationalInfinityHom (originalRationalProduct p J) := by
  rw [originalRationalProduct, map_mul, rational_infinity_polynomial, residue_reciprocal_kernel]
  calc
    originalOriginDensity p J =
        -3 * originLaurentX ^ ((p - 1) / 2) * infinityPolynomialHom J *
          (4 * originLaurentX - 11) /
            ((4 - originLaurentX) * (4 * originLaurentX - 1)) := by
      unfold originalOriginDensity
      ring
    _ = -3 * (originLaurentX ^ (p - 2) *
          (originLaurentX⁻¹) ^ ((p - 1) / 2) * originLaurentX) * infinityPolynomialHom J *
          (4 * originLaurentX - 11) /
            ((4 - originLaurentX) * (4 * originLaurentX - 1)) := by
      rw [origin_reciprocal_power p hp]
    _ = _ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      norm_num
      ring

theorem original_origin_residue_polynomialPart (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (J : ℚ[X]) :
    originalOriginResidue p J = -6 * (originalPolynomialPart p J).coeff (p - 1) := by
  have hscale : (-6 : LaurentSeries ℚ) * originLaurentX ^ (p - 2) =
      single ((p - 2 : ℕ) : ℤ) (-6 : ℚ) := by
    rw [show (-6 : LaurentSeries ℚ) = single 0 (-6 : ℚ) from
      (by change -HahnSeries.C (6 : ℚ) = HahnSeries.C (-6 : ℚ); rw [map_neg])]
    simp [originLaurentX, single_pow, single_mul_single]
  rw [originalOriginResidue, original_density_infinity p hp J, hscale, coeff_single_mul]
  have hs : (-1 : ℤ) - ((p - 2 : ℕ) : ℤ) = -((p - 1 : ℕ) : ℤ) := by omega
  rw [hs, rational_infinity_polynomialPart_coeff]
  rfl

theorem originDensity_original_specialization (p : ℕ) (G : ℚ[X]) :
    originDensity p G = originalOriginDensity p (G.comp Vpolynomial) := by
  have hcomp : infinityPolynomialHom (G.comp Vpolynomial) = aeval originQ G :=
    aeval_comp _
  simp only [originDensity, originalOriginDensity, hcomp]

theorem actualOriginResidue_original_specialization (p : ℕ) (G : ℚ[X]) :
    actualOriginResidue p G = originalOriginResidue p (G.comp Vpolynomial) := by
  rw [actualOriginResidue, originalOriginResidue, originDensity_original_specialization]

theorem originalRationalProduct_fraction (p : ℕ) (J : ℚ[X]) :
    originalRationalProduct p J =
      algebraMap ℚ[X] (RatFunc ℚ) (X ^ ((p - 1) / 2) * (4 - 11 * X) * J) /
        algebraMap ℚ[X] (RatFunc ℚ) residueDenominator := by
  simp only [originalRationalProduct, residueKernel, map_mul]
  ring

theorem originalPolynomialPart_add (p : ℕ) (J H : ℚ[X]) :
    originalPolynomialPart p (J + H) = originalPolynomialPart p J + originalPolynomialPart p H := by
  have he : originalRationalProduct p (J + H) =
      originalRationalProduct p J + originalRationalProduct p H := by
    simp [originalRationalProduct, mul_add]
  unfold originalPolynomialPart
  rw [he, rationalPolynomialPart_add]

theorem originalPolynomialPart_C_mul (p : ℕ) (a : ℚ) (J : ℚ[X]) :
    originalPolynomialPart p (C a * J) = C a * originalPolynomialPart p J := by
  have he : originalRationalProduct p (C a * J) = RatFunc.C a * originalRationalProduct p J := by
    simp only [originalRationalProduct, map_mul, RatFunc.algebraMap_C]
    ring
  change rationalPolynomialPart _ = _
  rw [he, rationalPolynomialPart_scalar]
  rfl

theorem originalOriginResidue_add (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (J H : ℚ[X]) :
    originalOriginResidue p (J + H) = originalOriginResidue p J + originalOriginResidue p H := by
  rw [original_origin_residue_polynomialPart p hp, originalPolynomialPart_add, Polynomial.coeff_add,
    original_origin_residue_polynomialPart p hp, original_origin_residue_polynomialPart p hp]
  ring

theorem originalOriginResidue_C_mul (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (a : ℚ) (J : ℚ[X]) :
    originalOriginResidue p (C a * J) = a * originalOriginResidue p J := by
  rw [original_origin_residue_polynomialPart p hp, originalPolynomialPart_C_mul, coeff_C_mul,
    original_origin_residue_polynomialPart p hp]
  ring

theorem originalPolynomialPart_low_coeff_zero (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (J : ℚ[X]) (hJ : J.natDegree ≤ (p - 1) / 2) :
    (originalPolynomialPart p J).coeff (p - 1) = 0 := by
  have hN := WPActualEvenLogCarry.prime_half_identity p (by omega)
  have hlin : (4 - 11 * X : ℚ[X]).natDegree ≤ 1 := by compute_degree
  have hn : (X ^ ((p - 1) / 2) * (4 - 11 * X) * J).natDegree ≤
      (p - 1) / 2 + 1 + J.natDegree := by
    exact natDegree_mul_le.trans (Nat.add_le_add_right
      (natDegree_mul_le.trans (by simpa only [natDegree_X_pow] using Nat.add_le_add_left hlin _)) _)
  unfold originalPolynomialPart
  rw [originalRationalProduct_fraction]
  apply rationalPolynomialPart_fraction_coeff_zero _ _ residueDenominator_ne_zero
    (p - 1) (by omega)
  rw [residueDenominator_degree]
  omega

theorem originalOriginResidue_low_zero (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (J : ℚ[X]) (hJ : J.natDegree ≤ (p - 1) / 2) :
    originalOriginResidue p J = 0 := by
  rw [original_origin_residue_polynomialPart p hp, originalPolynomialPart_low_coeff_zero p hp J hJ,
    mul_zero]

/-- Exact reciprocal density transport; no endpoint condition is used. -/
theorem origin_density_infinity (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (G : ℚ[X]) :
    originDensity p G = -6 * originLaurentX ^ (p - 2) *
      rationalInfinityHom (residueRationalProduct p G) := by
  rw [originDensity_original_specialization, original_density_infinity p hp]
  rfl

/-- NC81b, for every prime class, with the complete canonical polynomial part. -/
theorem actual_origin_residue_polynomialPart (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (G : ℚ[X]) :
    actualOriginResidue p G = -6 * (residuePolynomialPart p G).coeff (p - 1) := by
  rw [actualOriginResidue_original_specialization]
  exact original_origin_residue_polynomialPart p hp (G.comp Vpolynomial)

theorem residueRationalProduct_fraction (p : ℕ) (G : ℚ[X]) :
    residueRationalProduct p G =
      algebraMap ℚ[X] (RatFunc ℚ)
        (X ^ ((p - 1) / 2) * (4 - 11 * X) * G.comp Vpolynomial) /
          algebraMap ℚ[X] (RatFunc ℚ) residueDenominator := by
  simp only [residueRationalProduct, residueKernel, map_mul]
  ring

theorem residuePolynomialPart_add (p : ℕ) (G H : ℚ[X]) :
    residuePolynomialPart p (G + H) = residuePolynomialPart p G + residuePolynomialPart p H := by
  have he : residueRationalProduct p (G + H) =
      residueRationalProduct p G + residueRationalProduct p H := by
    simp [residueRationalProduct, add_comp, mul_add]
  unfold residuePolynomialPart
  rw [he, rationalPolynomialPart_add]

theorem residuePolynomialPart_C_mul (p : ℕ) (a : ℚ) (G : ℚ[X]) :
    residuePolynomialPart p (C a * G) = C a * residuePolynomialPart p G := by
  have he : residueRationalProduct p (C a * G) = RatFunc.C a * residueRationalProduct p G := by
    simp only [residueRationalProduct, mul_comp, C_comp, map_mul, RatFunc.algebraMap_C]
    ring
  change rationalPolynomialPart _ = _
  rw [he, rationalPolynomialPart_scalar]
  rfl

theorem actualOriginResidue_add (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (G H : ℚ[X]) :
    actualOriginResidue p (G + H) = actualOriginResidue p G + actualOriginResidue p H := by
  rw [actual_origin_residue_polynomialPart p hp, residuePolynomialPart_add, Polynomial.coeff_add,
    actual_origin_residue_polynomialPart p hp, actual_origin_residue_polynomialPart p hp]
  ring

theorem actualOriginResidue_C_mul (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (a : ℚ) (G : ℚ[X]) :
    actualOriginResidue p (C a * G) = a * actualOriginResidue p G := by
  rw [actual_origin_residue_polynomialPart p hp, residuePolynomialPart_C_mul, coeff_C_mul,
    actual_origin_residue_polynomialPart p hp]
  ring

theorem residuePolynomialPart_low_coeff_zero (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (G : ℚ[X]) (hG : 3 * G.natDegree ≤ (p - 1) / 2) :
    (residuePolynomialPart p G).coeff (p - 1) = 0 := by
  have hV : Vpolynomial.natDegree ≤ 3 := by unfold Vpolynomial; compute_degree
  have hcomp : (G.comp Vpolynomial).natDegree ≤ 3 * G.natDegree :=
    Polynomial.natDegree_comp_le.trans (by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left G.natDegree hV)
  exact originalPolynomialPart_low_coeff_zero p hp (G.comp Vpolynomial) (hcomp.trans hG)

theorem actualOriginResidue_low_zero (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (G : ℚ[X]) (hG : 3 * G.natDegree ≤ (p - 1) / 2) :
    actualOriginResidue p G = 0 := by
  rw [actual_origin_residue_polynomialPart p hp, residuePolynomialPart_low_coeff_zero p hp G hG,
    mul_zero]

/-- Integrality of the full original-coordinate quotient is discharged coefficientwise. -/
theorem originalPolynomialPart_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (J : (integralRationals p)[X]) (k : ℕ) :
    (originalPolynomialPart p (J.map (integralRationals p).subtype)).coeff k ∈ integralRationals p := by
  let R := integralRationals p
  let P : R[X] := X ^ ((p - 1) / 2) * (4 - 11 * X) * J
  have he : P.map R.subtype = X ^ ((p - 1) / 2) * (4 - 11 * X) * J.map R.subtype := by
    simp [P, R]
  have hP : ∀ j, (X ^ ((p - 1) / 2) * (4 - 11 * X) *
      J.map R.subtype).coeff j ∈ R := by
    intro j
    rw [← he, coeff_map]
    exact (P.coeff j).property
  have hD : ∀ j, residueDenominator.coeff j ∈ R := by
    intro j
    have hd : (2 * ((4 - X) * (4 * X - 1)) : R[X]).map R.subtype =
        residueDenominator := by simp [residueDenominator]
    rw [← hd, coeff_map]
    exact ((2 * ((4 - X) * (4 * X - 1)) : R[X]).coeff j).property
  have h8 : (1 / 8 : ℚ) ∈ R := by
    exact small_inverse_integral p 8 (by norm_num) (by omega)
  have hu : residueDenominator.leadingCoeff⁻¹ ∈ R := by
    rw [residueDenominator_leadingCoeff]
    convert R.neg_mem h8 using 1
    norm_num
  unfold originalPolynomialPart
  rw [originalRationalProduct_fraction,
    rationalPolynomialPart_fraction _ _ residueDenominator_ne_zero]
  exact ordinary_quotient_coeff_mem R _ _ residueDenominator_ne_zero hP hD hu k

/-- The literal finite coefficient lift of the proved rational polynomial quotient. -/
def integralOriginalPolynomialPart (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (J : (integralRationals p)[X]) : (integralRationals p)[X] :=
  ∑ k ∈ Finset.range ((originalPolynomialPart p (J.map (integralRationals p).subtype)).natDegree + 1),
    monomial k ⟨(originalPolynomialPart p (J.map (integralRationals p).subtype)).coeff k,
      originalPolynomialPart_integral p hp J k⟩

theorem integralOriginalPolynomialPart_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (J : (integralRationals p)[X]) :
    (integralOriginalPolynomialPart p hp J).map (integralRationals p).subtype =
      originalPolynomialPart p (J.map (integralRationals p).subtype) := by
  simp only [integralOriginalPolynomialPart, Polynomial.map_sum, map_monomial,
    Subring.coe_subtype]
  exact (originalPolynomialPart p (J.map (integralRationals p).subtype)).as_sum_range.symm

theorem originalOriginResidue_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (J : (integralRationals p)[X]) :
    originalOriginResidue p (J.map (integralRationals p).subtype) ∈ integralRationals p := by
  rw [original_origin_residue_polynomialPart p hp]
  exact (integralRationals p).mul_mem (intCast_mem _ (-6))
    (originalPolynomialPart_integral p hp J (p - 1))

theorem integralOriginalPolynomialPart_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (J : (integralRationals p)[X]) (k : ℕ) :
    ((originalPolynomialPart p (J.map (integralRationals p).subtype)).coeff k : ZMod p) =
      ((integralOriginalPolynomialPart p hp J).map (residueHom p)).coeff k := by
  rw [← integralOriginalPolynomialPart_value p hp J, coeff_map, coeff_map]
  rfl

/-- Normalization of the actual integral denominator makes monic division transport literal. -/
theorem integralResidueDenominator_monic (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((2 * ((4 - X) * (4 * X - 1)) : (integralRationals p)[X]) *
      C (-smallIntegralInverse p 8)).Monic := by
  have hu : ((-smallIntegralInverse p 8 : integralRationals p) : ℚ) =
      residueDenominator.leadingCoeff⁻¹ := by
    change -(smallIntegralInverse p 8).val = residueDenominator.leadingCoeff⁻¹
    rw [smallIntegralInverse_value p 8 (by norm_num) (by omega),
      residueDenominator_leadingCoeff]
    norm_num
  have hmap : (((2 * ((4 - X) * (4 * X - 1)) : (integralRationals p)[X]) *
      C (-smallIntegralInverse p 8)).map (integralRationals p).subtype) =
        residueDenominator * C residueDenominator.leadingCoeff⁻¹ := by
    have hu' : (integralRationals p).subtype (-smallIntegralInverse p 8) =
        residueDenominator.leadingCoeff⁻¹ := hu
    rw [Polynomial.map_mul, Polynomial.map_C, hu']
    congr 1
    simp [residueDenominator]
  apply Polynomial.monic_of_injective (f := (integralRationals p).subtype) Subtype.val_injective
  rw [hmap]
  exact monic_mul_leadingCoeff_inv residueDenominator_ne_zero

/-- The coefficient lift is the actual normalized monic quotient over the integral subring. -/
theorem integralOriginalPolynomialPart_monic_model (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (J : (integralRationals p)[X]) :
    integralOriginalPolynomialPart p hp J = Polynomial.C (-smallIntegralInverse p 8) *
      ((X ^ ((p - 1) / 2) * (4 - 11 * X) * J) /ₘ
        ((2 * ((4 - X) * (4 * X - 1)) : (integralRationals p)[X]) *
          Polynomial.C (-smallIntegralInverse p 8))) := by
  have hu : ((-smallIntegralInverse p 8 : integralRationals p) : ℚ) =
      residueDenominator.leadingCoeff⁻¹ := by
    change -(smallIntegralInverse p 8).val = residueDenominator.leadingCoeff⁻¹
    rw [smallIntegralInverse_value p 8 (by norm_num) (by omega),
      residueDenominator_leadingCoeff]
    norm_num
  have hu' : (integralRationals p).subtype (-smallIntegralInverse p 8) =
      residueDenominator.leadingCoeff⁻¹ := hu
  have hnum : (X ^ ((p - 1) / 2) * (4 - 11 * X) * J).map (integralRationals p).subtype =
      X ^ ((p - 1) / 2) * (4 - 11 * X) * J.map (integralRationals p).subtype := by simp
  have hden : (((2 * ((4 - X) * (4 * X - 1)) : (integralRationals p)[X]) *
      Polynomial.C (-smallIntegralInverse p 8)).map (integralRationals p).subtype) =
        residueDenominator * Polynomial.C residueDenominator.leadingCoeff⁻¹ := by
    rw [Polynomial.map_mul, Polynomial.map_C, hu']
    congr 1
    simp [residueDenominator]
  apply Polynomial.map_injective (integralRationals p).subtype Subtype.val_injective
  rw [integralOriginalPolynomialPart_value, Polynomial.map_mul, Polynomial.map_C,
    map_divByMonic (integralRationals p).subtype (integralResidueDenominator_monic p hp)]
  rw [hu', hnum, hden]
  unfold originalPolynomialPart
  rw [originalRationalProduct_fraction, rationalPolynomialPart_fraction _ _ residueDenominator_ne_zero,
    Polynomial.div_def]

/-- Whole polynomial residue equality transports through the actual monic quotient. -/
theorem integralOriginalPolynomialPart_field_congr (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (J K : (integralRationals p)[X])
    (hJK : J.map (residueHom p) = K.map (residueHom p)) :
    (integralOriginalPolynomialPart p hp J).map (residueHom p) =
      (integralOriginalPolynomialPart p hp K).map (residueHom p) := by
  rw [integralOriginalPolynomialPart_monic_model p hp J,
    integralOriginalPolynomialPart_monic_model p hp K]
  simp only [Polynomial.map_mul, Polynomial.map_C,
    map_divByMonic (residueHom p) (integralResidueDenominator_monic p hp)]
  rw [hJK]

/-- An actual integral witness for the rational residue, constructed before reduction. -/
def integralOriginalResidue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (J : (integralRationals p)[X]) : integralRationals p :=
  -6 * (integralOriginalPolynomialPart p hp J).coeff (p - 1)

theorem integralOriginalResidue_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (J : (integralRationals p)[X]) :
    (integralOriginalResidue p hp J).val =
      originalOriginResidue p (J.map (integralRationals p).subtype) := by
  rw [original_origin_residue_polynomialPart p hp,
    ← integralOriginalPolynomialPart_value p hp J, coeff_map]
  rfl

theorem integralOriginalResidue_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (J : (integralRationals p)[X]) :
    residueHom p (integralOriginalResidue p hp J) =
      -6 * ((integralOriginalPolynomialPart p hp J).map (residueHom p)).coeff (p - 1) := by
  simp only [integralOriginalResidue, map_mul, map_neg, map_ofNat, Polynomial.coeff_map]

/-- Equality of integral original sources modulo p determines their actual rational residues modulo p. -/
theorem originalOriginResidue_field_congr (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (J K : (integralRationals p)[X])
    (hJK : J.map (residueHom p) = K.map (residueHom p)) :
    (originalOriginResidue p (J.map (integralRationals p).subtype) : ZMod p) =
      (originalOriginResidue p (K.map (integralRationals p).subtype) : ZMod p) := by
  rw [← integralOriginalResidue_value p hp J, ← integralOriginalResidue_value p hp K]
  change residueHom p (integralOriginalResidue p hp J) =
    residueHom p (integralOriginalResidue p hp K)
  rw [integralOriginalResidue_field, integralOriginalResidue_field,
    integralOriginalPolynomialPart_field_congr p hp J K hJK]

/-- Canonical G(V) specialization of the full original quotient. -/
theorem residuePolynomialPart_original_specialization (p : ℕ) (G : ℚ[X]) :
    residuePolynomialPart p G = originalPolynomialPart p (G.comp Vpolynomial) := rfl

theorem residuePolynomialPart_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (G : (integralRationals p)[X]) (k : ℕ) :
    (residuePolynomialPart p (G.map (integralRationals p).subtype)).coeff k ∈ integralRationals p := by
  have h := originalPolynomialPart_integral p hp
    (G.comp (WPHasseIntegralTransport.integralV p (by omega))) k
  rw [Polynomial.map_comp, WPHasseIntegralTransport.integralV_map_rational] at h
  exact h

def integralResiduePolynomialPart (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (G : (integralRationals p)[X]) : (integralRationals p)[X] :=
  integralOriginalPolynomialPart p hp (G.comp (WPHasseIntegralTransport.integralV p (by omega)))

theorem integralResiduePolynomialPart_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (G : (integralRationals p)[X]) :
    (integralResiduePolynomialPart p hp G).map (integralRationals p).subtype =
      residuePolynomialPart p (G.map (integralRationals p).subtype) := by
  rw [integralResiduePolynomialPart, integralOriginalPolynomialPart_value,
    Polynomial.map_comp, WPHasseIntegralTransport.integralV_map_rational]
  rfl

theorem actualOriginResidue_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (G : (integralRationals p)[X]) :
    actualOriginResidue p (G.map (integralRationals p).subtype) ∈ integralRationals p := by
  rw [actual_origin_residue_polynomialPart p hp]
  exact (integralRationals p).mul_mem (intCast_mem _ (-6))
    (residuePolynomialPart_integral p hp G (p - 1))

theorem integralResiduePolynomialPart_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (G : (integralRationals p)[X]) (k : ℕ) :
    ((residuePolynomialPart p (G.map (integralRationals p).subtype)).coeff k : ZMod p) =
      ((integralResiduePolynomialPart p hp G).map (residueHom p)).coeff k := by
  rw [← integralResiduePolynomialPart_value p hp G, coeff_map, coeff_map]
  rfl

/-- Honest evaluation of the finite Laurent variable at the original origin coordinate. -/
def finiteLaurentOriginHom : ℚ[T;T⁻¹] →+* LaurentSeries ℚ :=
  LaurentPolynomial.eval₂ HahnSeries.C (Units.mk0 originLaurentX originLaurentX_ne_zero)

theorem finiteLaurentOriginHom_C (a : ℚ) :
    finiteLaurentOriginHom (LaurentPolynomial.C a) = HahnSeries.single 0 a := by
  rw [finiteLaurentOriginHom, LaurentPolynomial.eval₂_C, HahnSeries.C_apply]

theorem finiteLaurentOriginHom_T (n : ℤ) :
    finiteLaurentOriginHom (LaurentPolynomial.T n) = HahnSeries.single n (1 : ℚ) := by
  simp only [finiteLaurentOriginHom, LaurentPolynomial.eval₂_T,
    Units.val_zpow_eq_zpow_val, Units.val_mk0]
  exact (RatFunc.single_zpow n).symm

theorem finiteLaurentOriginHom_monomial (n : ℤ) (a : ℚ) :
    finiteLaurentOriginHom (LaurentPolynomial.C a * LaurentPolynomial.T n) =
      HahnSeries.single n a := by
  rw [map_mul, finiteLaurentOriginHom_C, finiteLaurentOriginHom_T, single_mul_single]
  simp

theorem finiteLaurentOriginHom_coeff (P : ℚ[T;T⁻¹]) (n : ℤ) :
    (finiteLaurentOriginHom P).coeff n = P.coeff n := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, HahnSeries.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]
  | C_mul_T k a =>
    rw [finiteLaurentOriginHom_monomial, ← LaurentPolynomial.single_eq_C_mul_T]
    simp only [HahnSeries.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm]
    split_ifs <;> rfl

theorem origin_linearPole_coeff_zero (a : ℚ) :
    (originLaurentX - HahnSeries.single 0 a).coeff 0 = -a := by
  simp [originLaurentX, HahnSeries.coeff_sub]

theorem origin_linearPole_ne_zero (a : ℚ) (ha : a ≠ 0) :
    originLaurentX - HahnSeries.single 0 a ≠ 0 := by
  intro h
  have hc := congrArg (fun P : LaurentSeries ℚ => P.coeff 0) h
  rw [origin_linearPole_coeff_zero, HahnSeries.coeff_zero] at hc
  exact ha (neg_eq_zero.mp hc)

theorem origin_linearPole_order (a : ℚ) (ha : a ≠ 0) :
    (originLaurentX - HahnSeries.single 0 a).order = 0 := by
  apply le_antisymm
  · apply order_le_of_coeff_ne_zero
    rw [origin_linearPole_coeff_zero]
    exact neg_ne_zero.mpr ha
  · apply (le_order_iff_forall (origin_linearPole_ne_zero a ha)).mpr
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    simp [originLaurentX, HahnSeries.coeff_sub, hn0, hn1]

/-- A nonzero original linear pole is regular at the origin, so contributes no residue. -/
theorem origin_regular_linearPole_residue (a c : ℚ) (ha : a ≠ 0) :
    (HahnSeries.single 0 c / (originLaurentX - HahnSeries.single 0 a)).coeff (-1 : ℤ) = 0 := by
  rw [div_eq_mul_inv, coeff_single_zero_mul]
  have hi : ((originLaurentX - HahnSeries.single 0 a)⁻¹).coeff (-1 : ℤ) = 0 := by
    apply coeff_eq_zero_of_lt_order
    rw [laurent_inverse_order _ (origin_linearPole_ne_zero a ha), origin_linearPole_order a ha]
    norm_num
  rw [hi, mul_zero]

theorem origin_dividedDifference_fraction (a : ℚ) (ha : a ≠ 0) (P : ℚ[T;T⁻¹]) :
    finiteLaurentOriginHom P / (originLaurentX - HahnSeries.single 0 a) =
      finiteLaurentOriginHom (WPActualEtaPole.dividedDifference a P) +
        HahnSeries.single 0 (WPFiniteLaurentIntegral.evaluate a ha P) /
          (originLaurentX - HahnSeries.single 0 a) := by
  have h := congrArg finiteLaurentOriginHom (WPActualEtaPole.dividedDifference_identity a ha P)
  simp only [map_mul, map_sub, finiteLaurentOriginHom_T, finiteLaurentOriginHom_C] at h
  change (originLaurentX - HahnSeries.single 0 a) *
      finiteLaurentOriginHom (WPActualEtaPole.dividedDifference a P) =
        finiteLaurentOriginHom P - HahnSeries.single 0 (WPFiniteLaurentIntegral.evaluate a ha P) at h
  field_simp [origin_linearPole_ne_zero a ha]
  linear_combination -h

theorem origin_dividedDifference_residue (a : ℚ) (ha : a ≠ 0) (P : ℚ[T;T⁻¹]) :
    (finiteLaurentOriginHom P / (originLaurentX - HahnSeries.single 0 a)).coeff (-1 : ℤ) =
      (WPActualEtaPole.dividedDifference a P).coeff (-1 : ℤ) := by
  rw [origin_dividedDifference_fraction a ha P, HahnSeries.coeff_add,
    finiteLaurentOriginHom_coeff, origin_regular_linearPole_residue a _ ha, add_zero]

theorem origin_dlogV_partialFractions :
    3 * (11 - 4 * originLaurentX) /
      ((4 - originLaurentX) * (4 * originLaurentX - 1)) =
        2 / (originLaurentX - HahnSeries.single 0 (1 / 4 : ℚ)) +
          1 / (originLaurentX - HahnSeries.single 0 (4 : ℚ)) := by
  have hquarter : (HahnSeries.single 0 (1 / 4 : ℚ) : LaurentSeries ℚ) = 1 / 4 := by
    change HahnSeries.C (1 / 4 : ℚ) = _
    rw [map_div₀, map_one, map_ofNat]
  have hfour : (HahnSeries.single 0 (4 : ℚ) : LaurentSeries ℚ) = 4 := rfl
  rw [hquarter, hfour]
  have ha := origin_linearPole_ne_zero (1 / 4) (by norm_num)
  have hb := origin_linearPole_ne_zero 4 (by norm_num)
  rw [hquarter] at ha
  rw [hfour] at hb
  have hfactor : (4 - originLaurentX) * (4 * originLaurentX - 1) =
      -4 * (originLaurentX - 1 / 4) * (originLaurentX - 4) := by ring
  rw [hfactor]
  have hc : 4 * originLaurentX - 1 ≠ 0 := (mul_ne_zero_iff.mp origin_denominator_ne_zero).2
  field_simp [ha, hb, hc]
  ring

theorem origin_weightedDifference_residue (P : ℚ[T;T⁻¹]) :
    (finiteLaurentOriginHom P *
      (3 * (11 - 4 * originLaurentX) /
        ((4 - originLaurentX) * (4 * originLaurentX - 1)))).coeff (-1 : ℤ) =
      (WPActualPositiveResidueSource.weightedDifference P).coeff (-1 : ℤ) := by
  have he : finiteLaurentOriginHom P *
      (3 * (11 - 4 * originLaurentX) /
        ((4 - originLaurentX) * (4 * originLaurentX - 1))) =
        2 * (finiteLaurentOriginHom P / (originLaurentX - HahnSeries.single 0 (1 / 4 : ℚ))) +
          finiteLaurentOriginHom P / (originLaurentX - HahnSeries.single 0 (4 : ℚ)) := by
    rw [origin_dlogV_partialFractions]
    ring
  rw [he, HahnSeries.coeff_add,
    show (2 : LaurentSeries ℚ) = HahnSeries.single 0 (2 : ℚ) from rfl,
    coeff_single_zero_mul, origin_dividedDifference_residue _ (by norm_num),
    origin_dividedDifference_residue _ (by norm_num),
    WPActualPositiveResidueSource.weightedDifference_apply, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply]
  rw [← LaurentPolynomial.single_eq_C (2 : ℚ), AddMonoidAlgebra.coeff_single_zero_mul]

theorem finiteLaurentOriginHom_Qx : finiteLaurentOriginHom WPActualEtaPole.Qx = originQ := by
  rw [WPActualEtaPole.Qx]
  simp only [map_mul, map_pow, map_sub, map_ofNat, map_one,
    finiteLaurentOriginHom_C, finiteLaurentOriginHom_T]
  rw [show (HahnSeries.single 1 (1 : ℚ) : LaurentSeries ℚ) = originLaurentX from rfl,
    show (HahnSeries.single (-3) (1 : ℚ) : LaurentSeries ℚ) = originLaurentX⁻¹ ^ 3 by
      rw [originLaurentX_inv]; simp [single_pow]]
  simp only [originQ, Vpolynomial, map_mul, map_pow, map_sub, map_ofNat, map_one,
    infinityPolynomialHom_C, infinityPolynomialHom_X]
  field_simp [originLaurentX_ne_zero]

theorem finiteLaurentOriginHom_substitute (G : ℚ[X]) (L : ℚ[T;T⁻¹]) :
    finiteLaurentOriginHom (WPFiniteLaurentIntegral.substitute G L) =
      aeval (finiteLaurentOriginHom L) G := by
  induction G using Polynomial.induction_on' with
  | add G H hG hH =>
    simp only [WPFiniteLaurentIntegral.substitute,
      Polynomial.coe_eval₂RingHom, map_add] at *
    rw [hG, hH]
  | monomial n a =>
    simp only [WPFiniteLaurentIntegral.substitute, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_monomial, map_mul, map_pow, finiteLaurentOriginHom_C, aeval_monomial,
      LaurentSeries.algebraMap_apply, HahnSeries.C_apply]

/-- Exact normalization attachment to the canonical finite weighted difference. -/
theorem actualOriginResidue_finite_weightedDifference (p : ℕ) (G : ℚ[X]) :
    actualOriginResidue p G =
      (WPActualPositiveResidueSource.weightedDifference
        (LaurentPolynomial.T (((p - 1) / 2 : ℕ) : ℤ) *
          WPFiniteLaurentIntegral.substitute G WPActualEtaPole.Qx)).coeff (-1 : ℤ) := by
  rw [← origin_weightedDifference_residue]
  simp only [map_mul, finiteLaurentOriginHom_T, finiteLaurentOriginHom_substitute,
    finiteLaurentOriginHom_Qx, RatFunc.single_one_eq_pow]
  unfold actualOriginResidue originDensity originLaurentX
  congr 1
  ring

/-- The same finite attachment for every original polynomial before specialization. -/
theorem originalOriginResidue_finite_weightedDifference (p : ℕ) (J : ℚ[X]) :
    originalOriginResidue p J =
      (WPActualPositiveResidueSource.weightedDifference
        (LaurentPolynomial.T (((p - 1) / 2 : ℕ) : ℤ) *
          WPFiniteLaurentIntegral.substitute J (LaurentPolynomial.T (-1)))).coeff (-1 : ℤ) := by
  rw [← origin_weightedDifference_residue]
  simp only [map_mul, finiteLaurentOriginHom_T, finiteLaurentOriginHom_substitute,
    RatFunc.single_one_eq_pow]
  unfold originalOriginResidue originalOriginDensity
  change ((originLaurentX ^ ((p - 1) / 2) *
    aeval (single (-1 : ℤ) (1 : ℚ) : LaurentSeries ℚ) J * (3 * (11 - 4 * originLaurentX)) /
      ((4 - originLaurentX) * (4 * originLaurentX - 1))) : LaurentSeries ℚ).coeff (-1 : ℤ) = _
  simp only [originLaurentX]
  congr 1
  ring

end

end WPFiniteCarry
