import WPFieldAssembly.SourceClosureSigmaWholePrimitive

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.SourceClosureSigmaProperJ
  WPFieldAssembly.SourceClosureSigmaProperEndpoint
  WPFieldAssembly.SourceClosureSigmaWholePrimitive
  WPFieldAssembly.ActualSigmaClearedSource

namespace WPFieldAssembly.SourceClosureSigmaActualCounterterm

set_option maxHeartbeats 1500000

/- SB86's characteristic-zero primitive and its actual two resonant
slots are retained before the whole counterterm is divided by p. -/

noncomputable def ordinaryJQ : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ[T;T⁻¹] :=
  primitiveWith (fun j : ℤ => (j : ℚ)⁻¹)

theorem ordinaryJQ_coeff (F : ℚ[T;T⁻¹]) (j : ℤ) :
    (ordinaryJQ F).coeff j = (j : ℚ)⁻¹ * F.coeff (j - 1) :=
  primitiveWith_coeff _ _ _

theorem ordinaryJQ_source (F : ℚ[T;T⁻¹]) :
    D (ordinaryJQ F) = F - LaurentPolynomial.C (F.coeff (-1)) * T (-1) := by
  ext j
  rw [D_coeff, ordinaryJQ_coeff]
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_unit_monomial]
  by_cases hj : j = -1
  · subst j
    norm_num
  · have hjq : ((j + 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : j + 1 ≠ 0)
    rw [if_neg (by omega : (-1 : ℤ) ≠ j)]
    simp only [add_sub_cancel_right]
    rw [← mul_assoc, mul_inv_cancel₀ hjq]
    ring

theorem ordinaryJQ_zero (F : ℚ[T;T⁻¹]) : (ordinaryJQ F).coeff 0 = 0 := by
  rw [ordinaryJQ_coeff]
  norm_num

theorem ordinaryJQ_canonical (p : ℕ) (F : ℚ[T;T⁻¹]) :
    ordinaryJQ F = originalJQ p F +
      LaurentPolynomial.C (F.coeff ((p : ℤ) - 1) / (p : ℚ)) * T (p : ℤ) := by
  ext j
  rw [ordinaryJQ_coeff]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, originalJQ_coeff,
    coeff_unit_monomial]
  by_cases hjp : j = (p : ℤ)
  · subst j
    simp only [canonicalInverseQ, if_true,
      Int.cast_natCast, div_eq_mul_inv]
    ring
  · rw [canonicalInverseQ, if_neg hjp, if_neg (by omega : (p : ℤ) ≠ j), add_zero]

noncomputable def actualKappaQ (p : ℕ) : ℚ :=
  (originalRactQ p).coeff ((p : ℤ) - 1) / (p : ℚ)

noncomputable def actualPactQ (p : ℕ) : ℚ[T;T⁻¹] := ordinaryJQ (originalRactQ p)

noncomputable def actualBprimQ (p : ℕ) : ℚ[T;T⁻¹] :=
  actualPactQ p + invert (actualPactQ p)

noncomputable def actualAlphaQ (p : ℕ) (literalC : ℚ) : ℚ :=
  actualKappaQ p + 8 * literalC / 15

noncomputable def actualSB86CountertermQ (p : ℕ) (literalC : ℚ) : ℚ[T;T⁻¹] :=
  actualBprimQ p -
    LaurentPolynomial.C (LaurentPolynomial.eval₂ (RingHom.id ℚ) fourUnitQ⁻¹
      (actualBprimQ p)) - LaurentPolynomial.C (actualAlphaQ p literalC) * originalZpQ p

theorem actualPactQ_unit_decomposition (p : ℕ) [Fact p.Prime] :
    actualPactQ p = originalPunitQ p + LaurentPolynomial.C (actualKappaQ p) * T (p : ℤ) :=
  ordinaryJQ_canonical p (originalRactQ p)

theorem symmetric_primitive_centered (F : ℚ[T;T⁻¹]) :
    F + invert F - LaurentPolynomial.C
      (LaurentPolynomial.eval₂ (RingHom.id ℚ) fourUnitQ⁻¹ (F + invert F)) =
      endSym fourUnitQ F := by
  rw [_root_.map_add, WPFiniteJWeightedResidue.inversion_eval, inv_inv, _root_.map_add]
  unfold endSym
  ring

/-- The named UW16 carrier is exactly the fixed original SB86 counterterm. -/
theorem actualSB86CountertermQ_identification (p : ℕ) [Fact p.Prime] (literalC : ℚ) :
    actualSB86CountertermQ p literalC = originalSactQ p literalC := by
  rw [actualSB86CountertermQ, actualBprimQ, symmetric_primitive_centered,
    actualPactQ_unit_decomposition, endSym_add, endSym_C_mul]
  simp only [originalZpQ, originalSactQ, actualAlphaQ, _root_.map_add]
  ring

theorem endSym_inversion (F : ℚ[T;T⁻¹]) :
    invert (endSym fourUnitQ F) = endSym fourUnitQ F := by
  simp only [endSym, _root_.map_sub, _root_.map_add, invert_C]
  rw [LaurentPolynomial.involutive_invert F]
  ring

theorem endSym_endpoints (F : ℚ[T;T⁻¹]) :
    LaurentPolynomial.eval₂ (RingHom.id ℚ) fourUnitQ (endSym fourUnitQ F) = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id ℚ) fourUnitQ⁻¹ (endSym fourUnitQ F) = 0 := by
  constructor <;>
    simp only [endSym, _root_.map_sub, _root_.map_add,
      LaurentPolynomial.eval₂_C, RingHom.id_apply,
      WPFiniteJWeightedResidue.inversion_eval, inv_inv] <;> ring

/-- Both actual endpoints and exact reflection survive before p-division. -/
theorem actualSB86CountertermQ_reflection_endpoints (p : ℕ) [Fact p.Prime] (literalC : ℚ) :
    invert (actualSB86CountertermQ p literalC) = actualSB86CountertermQ p literalC ∧
      LaurentPolynomial.eval₂ (RingHom.id ℚ) fourUnitQ
        (actualSB86CountertermQ p literalC) = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id ℚ) fourUnitQ⁻¹
        (actualSB86CountertermQ p literalC) = 0 := by
  rw [actualSB86CountertermQ_identification, originalSactQ]
  have hP := endSym_endpoints (originalPunitQ p)
  have hZ := endSym_endpoints (T (p : ℤ) : ℚ[T;T⁻¹])
  constructor
  · rw [_root_.map_sub, _root_.map_mul, invert_C, endSym_inversion,
      originalZpQ, endSym_inversion]
  · simp only [_root_.map_sub, _root_.map_mul, LaurentPolynomial.eval₂_C,
      RingHom.id_apply, originalZpQ, hP.1, hP.2, hZ.1, hZ.2, mul_zero, sub_zero,
      and_self]

theorem originalRactQ_reflection (p : ℕ) [Fact p.Prime] :
    T (-2) * invert (originalRactQ p) =
      T (-(((p - 1) / 2 : ℕ) : ℤ)) * originalRactQ p := by
  have hplus : invert (X + 1 : ℚ[X]).toLaurent = T (-1) * (X + 1 : ℚ[X]).toLaurent := by
    have ht : (T (-1) : ℚ[T;T⁻¹]) * T 1 = 1 := by rw [← T_add]; norm_num
    simp only [_root_.map_add, Polynomial.toLaurent_X, _root_.map_one, invert_T]
    linear_combination -ht
  have hT : (T (-2) : ℚ[T;T⁻¹]) * T (p : ℤ) *
      T (-1) ^ ((p - 1) / 2) * T (-2) ^ (p - 1) =
      T (-(((p - 1) / 2 : ℕ) : ℤ)) * T (-(p : ℤ)) := by
    rw [T_pow, T_pow, ← T_add, ← T_add, ← T_add, ← T_add]
    congr 1
    have := (Fact.out : p.Prime).pos
    omega
  simp only [originalRactQ, _root_.map_mul, _root_.map_pow, invert_C, invert_T,
    neg_neg, hplus, WPFiniteZSource.invert_Abar, mul_pow]
  linear_combination
    LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
      (X + 1 : ℚ[X]).toLaurent ^ ((p - 1) / 2) *
      (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1) * hT

theorem originalRactQ_Bsource (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originalRactQ p - T (-2) * invert (originalRactQ p) = originalBQ p := by
  have hn : 5 * ((p - 1) / 2) = 2 * (p - 1) + (p - 1) / 2 := by
    have := WPFiniteWSource.half_exponent p hp
    omega
  have hc : (1 / 2 : ℚ) * (1 / 5 : ℚ) ^ (2 * (p - 1)) *
      (1 / 5 : ℚ) ^ ((p - 1) / 2) = 1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2))) := by
    rw [mul_assoc, ← pow_add, ← hn]
    simp only [one_div, inv_pow, mul_inv_rev]
    ring
  have hC := congrArg (fun c : ℚ => (LaurentPolynomial.C c : ℚ[T;T⁻¹])) hc
  simp only [_root_.map_mul, _root_.map_pow, one_div] at hC
  rw [originalRactQ_reflection]
  simp only [originalBQ, WPFiniteWSource.squaredCoordinate,
    _root_.map_mul, _root_.map_add, _root_.map_pow, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, _root_.map_one, mul_pow, one_div]
  unfold originalRactQ
  simp only [one_div, _root_.map_add, Polynomial.toLaurent_X, _root_.map_one]
  linear_combination -T (-(p : ℤ)) * (T 1 + 1) ^ ((p - 1) / 2) *
    (1 - T (-(((p - 1) / 2 : ℕ) : ℤ))) *
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1) * hC

/-- SB86a's exact characteristic-zero derivative includes the divided resonant scalar. -/
theorem actualSB86CountertermQ_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (literalC : ℚ) :
    D (actualSB86CountertermQ p literalC) = originalBQ p -
      LaurentPolynomial.C ((p : ℚ) * actualAlphaQ p literalC) *
        (T ((p : ℤ) - 1) - T (-(p : ℤ) - 1)) := by
  have hP := ordinaryJQ_source (originalRactQ p)
  have ht : (T (-2) : ℚ[T;T⁻¹]) * T 1 = T (-1) := by rw [← T_add]; norm_num
  have hTp : (T (-2) : ℚ[T;T⁻¹]) * T (1 - (p : ℤ)) = T (-(p : ℤ) - 1) := by
    rw [← T_add]
    congr 1
    omega
  have hDtp : D (T (p : ℤ) : ℚ[T;T⁻¹]) =
      LaurentPolynomial.C (p : ℚ) * T ((p : ℤ) - 1) := by
    simpa only [_root_.map_one, one_mul, Int.cast_natCast] using D_monomial (1 : ℚ) (p : ℤ)
  rw [actualSB86CountertermQ, _root_.map_sub, _root_.map_sub, D_C, sub_zero,
    D_C_mul, actualBprimQ, _root_.map_add, D_invert]
  simp only [actualPactQ, ← sub_eq_add_neg]
  rw [hP, originalZpQ, endSym_derivative, hDtp]
  simp only [_root_.map_sub, _root_.map_mul, invert_C, invert_T,
    neg_sub, neg_neg]
  linear_combination originalRactQ_Bsource p hp +
    LaurentPolynomial.C ((originalRactQ p).coeff (-1)) * ht +
      (LaurentPolynomial.C (p : ℚ) *
        LaurentPolynomial.C (actualAlphaQ p literalC)) * hTp

end WPFieldAssembly.SourceClosureSigmaActualCounterterm
