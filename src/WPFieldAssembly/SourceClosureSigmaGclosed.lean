import WPFieldAssembly.SourceClosureSigmaLogCarry
import WPFieldAssembly.SourceClosureSigmaWholeCarry
import WPFieldAssembly.SourceClosureSigmaWholeSupport
import WPFieldAssembly.SourceClosureLogInversion
import WPFieldAssembly.SourceClosureUVPrimitiveSource
import WPFieldAssembly.SourceClosureUVCanonicalHoles

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPFieldAssembly.SourceClosureSigmaProperJ WPFieldAssembly.SourceClosureSigmaProperEndpoint
  WPFieldAssembly.SourceClosureSigmaCanonicalTransport WPFieldAssembly.SourceClosureSigmaKCarry
  WPFieldAssembly.SourceClosureSigmaLogCarry WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.SourceClosureSigmaWholeCarry WPFieldAssembly.SourceClosureSigmaProductCarry
  WPFieldAssembly.SourceClosureSigmaWholeSupport
  WPFieldAssembly.ActualUW16PrimitiveSource
  WPFieldAssembly.ActualSigmaNormCarrySource
  WPFieldAssembly.SourceClosureUniversalLog WPFieldAssembly.SourceClosureUVPrimitiveSource
  WPFieldAssembly.SourceClosureUVCanonicalHoles

namespace WPFieldAssembly.SourceClosureSigmaGclosed

set_option maxHeartbeats 1500000

theorem nonresonantPrimitiveField_derivative (p : ℕ) [Fact p.Prime]
    (F : (ZMod p)[T;T⁻¹]) (hF : ∀ j : ℤ, (p : ℤ) ∣ j → F.coeff j = 0) :
    nonresonantPrimitiveField p (D F) = F := by
  ext j
  rw [nonresonantPrimitiveField, primitiveWith_coeff, D_coeff, sub_add_cancel]
  by_cases hj : (p : ℤ) ∣ j
  · rw [nonresonantInverse, if_pos hj, zero_mul, hF j hj]
  · have hj0 : (j : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hj
    rw [nonresonantInverse, if_neg hj, ← mul_assoc, inv_mul_cancel₀ hj0, one_mul]

theorem nonresonantPrimitiveField_resonance (p : ℕ) [Fact p.Prime]
    (c : ZMod p) (j : ℤ) (hj : (p : ℤ) ∣ j) :
    nonresonantPrimitiveField p (LaurentPolynomial.C c * T (j - 1)) = 0 := by
  rw [nonresonantPrimitiveField, primitiveWith_monomial, sub_add_cancel,
    nonresonantInverse, if_pos hj, mul_zero, _root_.map_zero, zero_mul]

theorem low_polynomial_nonunit_zero (p : ℕ) [Fact p.Prime] (P : (ZMod p)[X])
    (hdeg : P.natDegree < p) (h0 : P.eval 0 = 0) (j : ℤ) (hj : (p : ℤ) ∣ j) :
    P.toLaurent.coeff j = 0 := by
  by_cases hj0 : j = 0
  · subst j
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, WPFiniteJCarrier.toLaurent_coeff_nat,
      coeff_zero_eq_eval_zero, h0]
  · by_cases hband : 0 < j ∧ j < (p : ℤ)
    · have hu := WPFiniteLaurentDifferential.integer_unit_in_band
        (K := ZMod p) p j hband
      have hz : (j : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hj
      exact False.elim (hu hz)
    · apply WPFiniteJCarrier.toLaurent_coeff_outside
      rcases lt_or_ge j 0 with hneg | hpos
      · exact Or.inl hneg
      · exact Or.inr (by omega)

theorem scaledLog_nonunit_zero (p : ℕ) [Fact p.Prime] (c : ZMod p)
    (j : ℤ) (hj : (p : ℤ) ∣ j) : (scaledLog p c).coeff j = 0 := by
  apply scaledLog_coeff_outside
  by_contra h
  have hband : 0 < j ∧ j < (p : ℤ) := by omega
  have hu := WPFiniteLaurentDifferential.integer_unit_in_band
    (K := ZMod p) p j hband
  exact hu ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hj)

noncomputable def polePrimitive (p : ℕ) [Fact p.Prime] (c d : ZMod p) : (ZMod p)[T;T⁻¹] :=
  LaurentPolynomial.C (2 / WPFiniteABSourceTail.epsilon p : ZMod p) *
    (T (-(p : ℤ)) - LaurentPolynomial.C c) * scaledLog p d

noncomputable def poleDensity (p : ℕ) [Fact p.Prime] (d : ZMod p) : (ZMod p)[T;T⁻¹] :=
  LaurentPolynomial.C (2 / WPFiniteABSourceTail.epsilon p : ZMod p) *
    (LaurentPolynomial.C d * T (-(p : ℤ)) - 1) *
      (1 - LaurentPolynomial.C d * T 1) ^ (p - 1)

theorem polePrimitive_nonunit_zero (p : ℕ) [Fact p.Prime] (c d : ZMod p)
    (j : ℤ) (hj : (p : ℤ) ∣ j) : (polePrimitive p c d).coeff j = 0 := by
  have hjp : (p : ℤ) ∣ j + p := dvd_add hj (dvd_refl _)
  simp only [polePrimitive, mul_assoc, C_mul_coeff, sub_mul, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, shift_mul_coeff, sub_neg_eq_add,
    scaledLog_nonunit_zero p d j hj, scaledLog_nonunit_zero p d (j + p) hjp,
    mul_zero, sub_self]

theorem scaledLog_derivative_closed (p : ℕ) [Fact p.Prime] (d : ZMod p) (hd : d ≠ 0) :
    D (scaledLog p d) = LaurentPolynomial.C d *
      ((1 - LaurentPolynomial.C d * T 1) ^ (p - 1) - T ((p : ℤ) - 1)) := by
  have hpw : (LaurentPolynomial.C d * T 1 : (ZMod p)[T;T⁻¹]) ^ (p - 1) =
      T ((p : ℤ) - 1) := by
    rw [mul_pow, ← _root_.map_pow, ZMod.pow_card_sub_one_eq_one hd, _root_.map_one,
      one_mul, T_pow]
    congr 1
    have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
    omega
  rw [scaledLog, D_toLaurent, derivative_comp, WPFiniteAffineLog.LP_derivative_closed_eq]
  have hder : (Polynomial.C d * X).derivative = Polynomial.C d := by
    rw [derivative_C_mul, derivative_X, mul_one]
  rw [hder]
  simp only [sub_comp, pow_comp, one_comp, X_comp, _root_.map_mul, _root_.map_sub,
    _root_.map_pow, _root_.map_one, Polynomial.toLaurent_C, Polynomial.toLaurent_X]
  rw [hpw]

theorem polePrimitive_derivative (p : ℕ) [Fact p.Prime] (c d : ZMod p)
    (hd : d ≠ 0) (hcd : c * d = 1) :
    D (polePrimitive p c d) = poleDensity p d -
      LaurentPolynomial.C (2 * d / WPFiniteABSourceTail.epsilon p) * T (-1) +
      LaurentPolynomial.C (2 / WPFiniteABSourceTail.epsilon p) * T ((p : ℤ) - 1) := by
  have hCd : (LaurentPolynomial.C c : (ZMod p)[T;T⁻¹]) * LaurentPolynomial.C d = 1 := by
    rw [← _root_.map_mul, hcd, _root_.map_one]
  have hc : (LaurentPolynomial.C (2 / WPFiniteABSourceTail.epsilon p) : (ZMod p)[T;T⁻¹]) *
      LaurentPolynomial.C d = LaurentPolynomial.C (2 * d / WPFiniteABSourceTail.epsilon p) := by
    rw [← _root_.map_mul]
    congr 1
    ring
  have ht : (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹]) * T ((p : ℤ) - 1) = T (-1) := by
    rw [← T_add]
    congr 1
    omega
  have hD : D (T (-(p : ℤ)) - LaurentPolynomial.C c : (ZMod p)[T;T⁻¹]) = 0 := by
    have h1 : D (1 : (ZMod p)[T;T⁻¹]) = 0 := by
      simpa only [_root_.map_one] using D_C (1 : ZMod p)
    have h := D_frobenius_shift p (1 : (ZMod p)[T;T⁻¹]) (-(p : ℤ))
      (dvd_neg.mpr (dvd_refl _))
    simp only [mul_one, h1, mul_zero] at h
    rw [_root_.map_sub, h, D_C, sub_self]
  rw [polePrimitive, mul_assoc, D_C_mul, D_mul, hD, zero_mul, zero_add,
    scaledLog_derivative_closed p d hd, poleDensity]
  linear_combination
    -LaurentPolynomial.C (2 / WPFiniteABSourceTail.epsilon p) *
      ((1 - LaurentPolynomial.C d * T 1) ^ (p - 1) - T ((p : ℤ) - 1)) * hCd -
    LaurentPolynomial.C (2 / WPFiniteABSourceTail.epsilon p) * LaurentPolynomial.C d * ht -
    T (-1) * hc

theorem poleDensity_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (c d : ZMod p) (hcd : c * d = 1) (hends : c + d = 17 / 4) :
    (T 1 - LaurentPolynomial.C c) * poleDensity p d = originalK0 p := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p) ≠ 0 :=
    pow_ne_zero _ (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega))
  have hCd : (LaurentPolynomial.C c : (ZMod p)[T;T⁻¹]) * LaurentPolynomial.C d = 1 := by
    rw [← _root_.map_mul, hcd, _root_.map_one]
  have hC : Function.Injective
      (LaurentPolynomial.C : ZMod p →+* (ZMod p)[T;T⁻¹]) := by
    intro a b hab
    have he := congrArg (fun F : (ZMod p)[T;T⁻¹] => F.coeff 0) hab
    simpa only [LaurentPolynomial.C_apply, if_true] using he
  have : CharP (ZMod p)[T;T⁻¹] p :=
    charP_of_injective_ringHom (f := LaurentPolynomial.C) hC p
  have hpow : (1 - LaurentPolynomial.C d * T 1 : (ZMod p)[T;T⁻¹]) ^ p =
      1 - LaurentPolynomial.C d * T (p : ℤ) := by
    rw [sub_pow_char, one_pow, mul_pow, ← _root_.map_pow, ZMod.pow_card,
      T_pow, mul_one]
  have ht : (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹]) * T (p : ℤ) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  have hcends : (LaurentPolynomial.C (2 / WPFiniteABSourceTail.epsilon p) : (ZMod p)[T;T⁻¹]) *
      (LaurentPolynomial.C c + LaurentPolynomial.C d) =
        LaurentPolynomial.C (17 / (2 * WPFiniteABSourceTail.epsilon p)) := by
    rw [← _root_.map_add, ← _root_.map_mul, hends]
    congr 1
    field_simp [h2, h4, heps]
    ring
  have hfactor : (T 1 - LaurentPolynomial.C c : (ZMod p)[T;T⁻¹]) *
      (LaurentPolynomial.C d * T (-(p : ℤ)) - 1) =
      -(T (-(p : ℤ)) - LaurentPolynomial.C c) * (1 - LaurentPolynomial.C d * T 1) := by
    linear_combination (T 1 - T (-(p : ℤ))) * hCd
  rw [poleDensity]
  calc
    _ = -LaurentPolynomial.C (2 / WPFiniteABSourceTail.epsilon p) *
        (T (-(p : ℤ)) - LaurentPolynomial.C c) *
          ((1 - LaurentPolynomial.C d * T 1) ^ (p - 1) *
            (1 - LaurentPolynomial.C d * T 1)) := by
      linear_combination LaurentPolynomial.C (2 / WPFiniteABSourceTail.epsilon p) *
        (1 - LaurentPolynomial.C d * T 1) ^ (p - 1) * hfactor
    _ = _ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p), hpow, originalK0]
      linear_combination
        LaurentPolynomial.C (2 / WPFiniteABSourceTail.epsilon p) * LaurentPolynomial.C d * ht -
        LaurentPolynomial.C (2 / WPFiniteABSourceTail.epsilon p) * T (p : ℤ) * hCd + hcends

noncomputable def Gclosed (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  (originalK0 p : (ZMod p)[T;T⁻¹]) *
    ((originalHa p : (ZMod p)[X]).toLaurent + (originalHb p : (ZMod p)[X]).toLaurent -
      (originalHx p : (ZMod p)[X]).toLaurent) +
    LaurentPolynomial.C ((WPFiniteWSource.W p : (ZMod p)[X]).eval (1 / 4)) *
      (originalJa p : (ZMod p)[T;T⁻¹]) +
    LaurentPolynomial.C ((WPFiniteWSource.W p : (ZMod p)[X]).eval 4) *
      (originalJb p : (ZMod p)[T;T⁻¹])

theorem originalK0Field_identification (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originalK0Field p = (originalK0 p : (ZMod p)[T;T⁻¹]) := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p) ≠ 0 :=
    pow_ne_zero _ (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega))
  have hc4 : (1 / (2 * WPFiniteABSourceTail.epsilon p) : ZMod p) * 4 =
      2 / WPFiniteABSourceTail.epsilon p := by field_simp [h2, heps]; ring
  have hc17 : (1 / (2 * WPFiniteABSourceTail.epsilon p) : ZMod p) * 17 =
      17 / (2 * WPFiniteABSourceTail.epsilon p) := by ring
  have hC4 := congrArg (fun c : ZMod p => (LaurentPolynomial.C c : (ZMod p)[T;T⁻¹])) hc4
  have hC17 := congrArg (fun c : ZMod p => (LaurentPolynomial.C c : (ZMod p)[T;T⁻¹])) hc17
  simp only [_root_.map_mul, _root_.map_ofNat] at hC4 hC17
  unfold originalK0Field normPhase originalK0
  change LaurentPolynomial.C (1 / (2 * WPFiniteABSourceTail.epsilon p)) *
    (17 - 4 * T (p : ℤ) - 4 * T (-(p : ℤ))) = _
  linear_combination hC17 - (T (p : ℤ) + T (-(p : ℤ))) * hC4

theorem Gclosed_nonunit_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℤ) (hj : (p : ℤ) ∣ j) : (Gclosed p).coeff j = 0 := by
  have hdeg := originalH_degree (K := ZMod p) p hp
  have hH (k : ℤ) (hk : (p : ℤ) ∣ k) :
      ((originalHa p).toLaurent + (originalHb p).toLaurent -
        (originalHx p : (ZMod p)[X]).toLaurent).coeff k = 0 := by
    have ha := low_polynomial_nonunit_zero p (originalHa p) (by omega)
      (WPFiniteProductTail.unitPrimitiveP_zero p _ _) k hk
    have hb := low_polynomial_nonunit_zero p (originalHb p) (by omega)
      (WPFiniteProductTail.unitPrimitiveP_zero p _ _) k hk
    have hx := low_polynomial_nonunit_zero p (originalHx p) (by omega)
      (WPFiniteProductTail.unitPrimitiveP_zero p _ _) k hk
    simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
      Finsupp.add_apply, Finsupp.sub_apply, ha, hb, hx, add_zero, sub_zero]
  have h0 := hH j hj
  have hplus := hH (j + p) (dvd_add hj (dvd_refl _))
  have hminus := hH (j - p) (dvd_sub hj (dvd_refl _))
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply, Finsupp.sub_apply] at h0 hplus hminus
  have ha : (originalJa p : (ZMod p)[T;T⁻¹]).coeff j = 0 := by
    simpa only [polePrimitive, originalJa] using
      polePrimitive_nonunit_zero p (1 / 4) 4 j hj
  have hb : (originalJb p : (ZMod p)[T;T⁻¹]).coeff j = 0 := by
    simpa only [polePrimitive, originalJb] using
      polePrimitive_nonunit_zero p 4 (1 / 4) j hj
  simp only [Gclosed, originalK0, sub_mul, add_mul, mul_assoc,
    AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub, Finsupp.add_apply,
    Finsupp.sub_apply, C_mul_coeff, shift_mul_coeff, sub_neg_eq_add,
    h0, hplus, hminus, ha, hb, mul_zero, add_zero, sub_self]

theorem logarithmic_density_decomposition (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originalLogProductField p =
      (poleDensity p 4 + poleDensity p (1 / 4)) * (WPFiniteWSource.W p).toLaurent -
      originalK0 p * (WPFiniteWSource.W p).toLaurent * T (-1) := by
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have hquarter : (1 / 4 : ZMod p) * 4 = 1 := div_mul_cancel₀ 1 h4
  have hsum : (1 / 4 : ZMod p) + 4 = 17 / 4 := by field_simp [h4]; ring
  have ha := poleDensity_source p hp (1 / 4) 4 hquarter hsum
  have hb := poleDensity_source p hp 4 (1 / 4) (by simpa [mul_comm] using hquarter)
    (by simpa [add_comm] using hsum)
  let P : (ZMod p)[T;T⁻¹] := T 1 - LaurentPolynomial.C (1 / 4)
  let Q : (ZMod p)[T;T⁻¹] := T 1 - 4
  have hcquarter : (LaurentPolynomial.C (4 : ZMod p) : (ZMod p)[T;T⁻¹]) *
      LaurentPolynomial.C (1 / 4) = 1 := by
    rw [← _root_.map_mul, mul_comm, hquarter, _root_.map_one]
  simp only [_root_.map_ofNat] at hcquarter
  have hA : (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent = -4 * P * Q := by
    simp only [WPFiniteZSource.Abar, _root_.map_mul, _root_.map_sub,
      _root_.map_ofNat, _root_.map_one, Polynomial.toLaurent_X]
    dsimp only [P, Q]
    linear_combination -(T 1 - 4) * hcquarter
  have hAD : (WPFiniteZSource.Abar : (ZMod p)[X]).derivative.toLaurent = -4 * (P + Q) := by
    simp only [WPFiniteZSource.Abar, derivative_mul, derivative_X, derivative_one,
      zero_sub, zero_mul, derivative_ofNat, mul_one, sub_zero,
      _root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_neg, _root_.map_one,
      _root_.map_ofNat, _root_.map_zero, Polynomial.toLaurent_X]
    dsimp only [P, Q]
    linear_combination -hcquarter
  have hK : (LaurentPolynomial.C (1 / (2 * (5 : ZMod p) ^ ((p - 1) / 2))) *
      T (-(p : ℤ)) * (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent ^ p) = originalK0Field p := by
    have ht : (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹]) * T (p : ℤ) = 1 := by
      rw [← T_add, neg_add_cancel, T_zero]
    rw [WPFiniteZSource.phase_factorization p hp]
    unfold originalK0Field normPhase WPFiniteZSource.phase
    linear_combination
      LaurentPolynomial.C (1 / (2 * (5 : ZMod p) ^ ((p - 1) / 2))) *
        (17 - 4 * T (p : ℤ) - 4 * T (-(p : ℤ))) * ht
  have hclear : (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent * originalLogProductField p =
      originalK0Field p * (WPFiniteWSource.W p).toLaurent *
        (WPFiniteZSource.Abar : (ZMod p)[X]).derivative.toLaurent -
      (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent * originalK0Field p *
        (WPFiniteWSource.W p).toLaurent * T (-1) := by
    have hpw : (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent ^ (p - 1) *
        (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent =
        (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent ^ p := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    unfold originalLogProductField
    linear_combination
      LaurentPolynomial.C (1 / (2 * (5 : ZMod p) ^ ((p - 1) / 2))) * T (-(p : ℤ)) *
        (WPFiniteWSource.W p).toLaurent * (WPFiniteZSource.Abar : (ZMod p)[X]).derivative.toLaurent * hpw +
      (WPFiniteWSource.W p).toLaurent * (WPFiniteZSource.Abar : (ZMod p)[X]).derivative.toLaurent * hK
  apply mul_left_cancel₀ (WPFiniteZSource.Abar_nonzero (K := ZMod p) p hp)
  rw [hclear, originalK0Field_identification p hp, hA, hAD]
  change P * poleDensity p 4 = originalK0 p at ha
  simp only [_root_.map_ofNat] at hb
  change Q * poleDensity p (1 / 4) = originalK0 p at hb
  linear_combination
    4 * Q * (WPFiniteWSource.W p).toLaurent * ha +
    4 * P * (WPFiniteWSource.W p).toLaurent * hb

theorem Gclosed_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    D (Gclosed p) = originalLogProductField p -
      LaurentPolynomial.C
        (2 * (4 * (WPFiniteWSource.W p).eval (1 / 4) +
          (1 / 4 : ZMod p) * (WPFiniteWSource.W p).eval 4) / WPFiniteABSourceTail.epsilon p) * T (-1) +
      LaurentPolynomial.C
        (2 * ((WPFiniteWSource.W p).eval (1 / 4) + (WPFiniteWSource.W p).eval 4) /
          WPFiniteABSourceTail.epsilon p) * T ((p : ℤ) - 1) := by
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h1 : D (1 : (ZMod p)[T;T⁻¹]) = 0 := by
    simpa only [_root_.map_one] using D_C (1 : ZMod p)
  have hT (j : ℤ) (hj : (p : ℤ) ∣ j) : D (T j : (ZMod p)[T;T⁻¹]) = 0 := by
    have h := D_frobenius_shift p (1 : (ZMod p)[T;T⁻¹]) j hj
    simpa only [mul_one, h1, mul_zero] using h
  have hDK : D (originalK0 p : (ZMod p)[T;T⁻¹]) = 0 := by
    simp only [originalK0, _root_.map_sub, _root_.map_add, D_C, D_C_mul,
      hT (p : ℤ) (dvd_refl _), hT (-(p : ℤ)) (dvd_neg.mpr (dvd_refl _)),
      add_zero, mul_zero, sub_self]
  have ha := poleDensity_source p hp (1 / 4) 4 (div_mul_cancel₀ 1 h4)
    (by field_simp [h4]; ring)
  have hb := poleDensity_source p hp 4 (1 / 4) (mul_one_div_cancel h4)
    (by field_simp [h4]; ring)
  simp only [_root_.map_ofNat] at hb
  have hHa := (originalH_laurent_sources (K := ZMod p) p hp).1
  have hHb := (originalH_laurent_sources (K := ZMod p) p hp).2.1
  have hHx := originalHx_laurent_source (K := ZMod p) p hp
  have hJa := polePrimitive_derivative p (1 / 4) 4 h4 (div_mul_cancel₀ 1 h4)
  have hJb := polePrimitive_derivative p 4 (1 / 4) (one_div_ne_zero h4) (mul_one_div_cancel h4)
  simp only [polePrimitive] at hJa hJb
  change D (originalJa p : (ZMod p)[T;T⁻¹]) = _ at hJa
  change D (originalJb p : (ZMod p)[T;T⁻¹]) = _ at hJb
  have ht : (T 1 : (ZMod p)[T;T⁻¹]) * T (-1) = 1 := by rw [← T_add]; norm_num
  have hrho : (LaurentPolynomial.C ((WPFiniteWSource.W p : (ZMod p)[X]).eval (1 / 4)) *
      LaurentPolynomial.C (2 * 4 / WPFiniteABSourceTail.epsilon p) +
      LaurentPolynomial.C ((WPFiniteWSource.W p).eval 4) *
        LaurentPolynomial.C (2 * (1 / 4) / WPFiniteABSourceTail.epsilon p)) =
      LaurentPolynomial.C
        (2 * (4 * (WPFiniteWSource.W p).eval (1 / 4) +
          (1 / 4 : ZMod p) * (WPFiniteWSource.W p).eval 4) / WPFiniteABSourceTail.epsilon p) := by
    rw [← _root_.map_mul, ← _root_.map_mul, ← _root_.map_add]
    congr 1
    ring
  have hgamma : (LaurentPolynomial.C ((WPFiniteWSource.W p : (ZMod p)[X]).eval (1 / 4)) +
      LaurentPolynomial.C ((WPFiniteWSource.W p).eval 4)) *
        LaurentPolynomial.C (2 / WPFiniteABSourceTail.epsilon p) =
      LaurentPolynomial.C
        (2 * ((WPFiniteWSource.W p).eval (1 / 4) + (WPFiniteWSource.W p).eval 4) /
          WPFiniteABSourceTail.epsilon p) := by
    rw [← _root_.map_add, ← _root_.map_mul]
    congr 1
    ring
  rw [Gclosed, _root_.map_add, _root_.map_add, D_mul, hDK,
    zero_mul, zero_add, _root_.map_sub, _root_.map_add, D_C_mul, D_C_mul, hJa, hJb,
    logarithmic_density_decomposition p hp]
  linear_combination
    poleDensity p 4 * hHa - D (originalHa p).toLaurent * ha +
    poleDensity p (1 / 4) * hHb - D (originalHb p).toLaurent * hb -
    originalK0 p * T (-1) * hHx + originalK0 p * D (originalHx p).toLaurent * ht -
    T (-1) * hrho + T ((p : ℤ) - 1) * hgamma

/-- UW16f identifies the literal whole nonresonant primitive, including its original holes. -/
theorem originalLogPrimitiveField_Gclosed (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    nonresonantPrimitiveField p (originalLogProductField p) = Gclosed p := by
  have h := nonresonantPrimitiveField_derivative p (Gclosed p) (Gclosed_nonunit_zero p hp)
  have h0 (c : ZMod p) : nonresonantPrimitiveField p (LaurentPolynomial.C c * T (-1)) = 0 := by
    simpa using nonresonantPrimitiveField_resonance p c 0 (dvd_zero _)
  have hpos (c : ZMod p) : nonresonantPrimitiveField p
      (LaurentPolynomial.C c * T ((p : ℤ) - 1)) = 0 :=
    nonresonantPrimitiveField_resonance p c p (dvd_refl _)
  rw [Gclosed_derivative p hp, _root_.map_add, _root_.map_sub, h0, hpos, sub_zero, add_zero] at h
  exact h

/-- The same integral logarithmic carry reduces with its actual original endpoints. -/
theorem originalLogEndSymI_Gclosed (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (WPPIntegralReduction.residueHom p) (originalLogEndSymI p hp) =
      endSym (fourUnitField p hp) (Gclosed p) := by
  rw [originalLogEndSymI_field p hp, originalLogPrimitiveField_Gclosed p hp]

theorem properJField_originalJa (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    properJField p = LaurentPolynomial.C (WPFiniteABSourceTail.epsilon p / 15 : ZMod p) *
      originalJa p := by
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p) ≠ 0 :=
    pow_ne_zero _ (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega))
  have hs : (WPFiniteABSourceTail.epsilon p / 15 : ZMod p) *
      (2 / WPFiniteABSourceTail.epsilon p) = 2 / 15 := by
    field_simp [heps]
  have hC := congrArg (fun c : ZMod p => (LaurentPolynomial.C c : (ZMod p)[T;T⁻¹])) hs
  rw [_root_.map_mul] at hC
  unfold properJField originalJa scaledLog logFourField
  simp only [_root_.map_ofNat]
  linear_combination
    -(T (-(p : ℤ)) - LaurentPolynomial.C (1 / 4 : ZMod p)) *
      (((WPFiniteAffineLog.LP p).comp (4 * X) : (ZMod p)[X]).toLaurent) * hC

theorem originalJa_invert (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    invert (originalJa p : (ZMod p)[T;T⁻¹]) = originalJb p := by
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have htp : (T (p : ℤ) * T (-(p : ℤ)) : (ZMod p)[T;T⁻¹]) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  have hca : (LaurentPolynomial.C (1 / 4 : ZMod p) : (ZMod p)[T;T⁻¹]) *
      LaurentPolynomial.C (4 : ZMod p) = 1 := by
    rw [← _root_.map_mul, one_div_mul_cancel h4, _root_.map_one]
  simp only [originalJa, originalJb, _root_.map_mul, _root_.map_sub, invert_C,
    invert_T, neg_neg, SourceClosureLogInversion.scaledLog_invert p 4 h4,
    ZMod.pow_card, show (4 : ZMod p)⁻¹ = 1 / 4 by simp only [one_div]]
  linear_combination
    -LaurentPolynomial.C (2 / WPFiniteABSourceTail.epsilon p) *
      LaurentPolynomial.C (4 : ZMod p) * scaledLog p (1 / 4) * htp +
    LaurentPolynomial.C (2 / WPFiniteABSourceTail.epsilon p) * T (-(p : ℤ)) *
      scaledLog p (1 / 4) * hca

theorem originalJb_invert (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    invert (originalJb p : (ZMod p)[T;T⁻¹]) = originalJa p := by
  rw [← originalJa_invert p hp, involutive_invert]

theorem originalJa_endpoints (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)⁻¹
        (originalJa p) = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)
        (originalJa p) = 0 := by
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p) ≠ 0 :=
    pow_ne_zero _ (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega))
  have h15 : (15 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 15 (by omega) (by omega)
  have hs : (WPFiniteABSourceTail.epsilon p / 15 : ZMod p) ≠ 0 := div_ne_zero heps h15
  obtain ⟨ha, hb⟩ := properJField_endpoints p hp
  rw [properJField_originalJa p hp, _root_.map_mul, LaurentPolynomial.eval₂_C,
    RingHom.id_apply] at ha hb
  exact ⟨(mul_eq_zero.mp ha).resolve_left hs, (mul_eq_zero.mp hb).resolve_left hs⟩

theorem originalJb_endpoints (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)⁻¹
        (originalJb p) = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)
        (originalJb p) = 0 := by
  obtain ⟨ha, hb⟩ := originalJa_endpoints p hp
  rw [← originalJa_invert p hp]
  simpa only [WPFiniteJWeightedResidue.inversion_eval, inv_inv] using And.intro hb ha

theorem originalJa_endSym (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    endSym (fourUnitField p hp) (originalJa p) = originalJa p + originalJb p := by
  obtain ⟨ha, hb⟩ := originalJa_endpoints p hp
  rw [endSym, ha, hb, _root_.map_zero, sub_zero, sub_zero, originalJa_invert p hp]

theorem originalK0_endpoints (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)⁻¹
        (originalK0 p) = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)
        (originalK0 p) = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p) ≠ 0 :=
    pow_ne_zero _ (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega))
  have hv : (fourUnitField p hp : ZMod p) = 4 := rfl
  have h4p : (4 : ZMod p) ^ p = 4 := ZMod.pow_card _
  constructor <;>
    simp only [originalK0, _root_.map_sub, _root_.map_mul, _root_.map_add,
      LaurentPolynomial.eval₂_C, RingHom.id_apply, LaurentPolynomial.eval₂_T_n,
      LaurentPolynomial.eval₂_T_neg_n, Units.val_inv_eq_inv_val, hv, inv_pow, h4p,
      inv_inv] <;> field_simp [h2, h4, heps] <;> ring

theorem originalK0_invert (p : ℕ) [Fact p.Prime] :
    invert (originalK0 p : (ZMod p)[T;T⁻¹]) = originalK0 p := by
  simp only [originalK0, _root_.map_sub, _root_.map_mul, _root_.map_add,
    invert_C, invert_T, neg_neg]
  ring

theorem Gclosed_endpoints (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)⁻¹
        (Gclosed p) = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)
        (Gclosed p) = 0 := by
  obtain ⟨hKa, hKb⟩ := originalK0_endpoints p hp
  obtain ⟨hJa, hJb⟩ := originalJa_endpoints p hp
  obtain ⟨hBa, hBb⟩ := originalJb_endpoints p hp
  constructor
  · simp only [Gclosed, _root_.map_add, _root_.map_mul, hKa, hJa, hBa,
      zero_mul, mul_zero, add_zero]
  · simp only [Gclosed, _root_.map_add, _root_.map_mul, hKb, hJb, hBb,
      zero_mul, mul_zero, add_zero]

/-- UW17e's joint reflection uses the literal primitive and both original ends. -/
theorem Gclosed_endSym_joint (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    endSym (fourUnitField p hp) (Gclosed p) =
      originalK0 p *
        ((originalHa p).toLaurent + (originalHb p).toLaurent +
          invert (originalHa p).toLaurent + invert (originalHb p).toLaurent -
          (originalHx p).toLaurent - invert (originalHx p).toLaurent) +
      LaurentPolynomial.C
        ((WPFiniteWSource.W p).eval (1 / 4) + (WPFiniteWSource.W p).eval 4) *
          (originalJa p + originalJb p) := by
  obtain ⟨ha, hb⟩ := Gclosed_endpoints p hp
  rw [endSym, ha, hb, _root_.map_zero, sub_zero, sub_zero]
  simp only [Gclosed, _root_.map_add, _root_.map_sub, _root_.map_mul, invert_C,
    originalK0_invert p, originalJa_invert p hp, originalJb_invert p hp]
  ring

theorem canSlots_endSym {R : Type*} [CommRing R] (p : ℕ) (u : Rˣ)
    (F : R[T;T⁻¹]) :
    endSym u (canSlots p F) = endSym u F -
      LaurentPolynomial.C (F.coeff (p : ℤ)) * endSym u (T (p : ℤ)) := by
  rw [canSlots, endSym_sub, endSym_sub, endSym_C, sub_zero, endSym_C_mul]

theorem frobeniusEndSym_original (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    endSym (fourUnitField p hp) (T (p : ℤ)) =
      T (p : ℤ) + T (-(p : ℤ)) - LaurentPolynomial.C (17 / 4 : ZMod p) := by
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have hv : (fourUnitField p hp : ZMod p) = 4 := rfl
  have h4p : (4 : ZMod p) ^ p = 4 := ZMod.pow_card _
  have hvi : ((1 / fourUnitField p hp : (ZMod p)ˣ) : ZMod p) = (1 / 4 : ZMod p) := by
    simp only [one_div, Units.val_inv_eq_inv_val, hv]
  have hqp : (1 / 4 : ZMod p) ^ p = 1 / 4 := ZMod.pow_card _
  have hevi : LaurentPolynomial.eval₂ (RingHom.id (ZMod p))
      (fourUnitField p hp)⁻¹ (T (p : ℤ)) = (1 / 4 : ZMod p) := by
    rw [LaurentPolynomial.eval₂_T_n, ← one_div (fourUnitField p hp), hvi, hqp]
  have hev : LaurentPolynomial.eval₂ (RingHom.id (ZMod p))
      (fourUnitField p hp) (T (p : ℤ)) = (4 : ZMod p) := by
    rw [LaurentPolynomial.eval₂_T_n, hv, h4p]
  have hs : (1 / 4 : ZMod p) + 4 = 17 / 4 := by field_simp [h4]; ring
  have hC := congrArg (fun c : ZMod p => (LaurentPolynomial.C c : (ZMod p)[T;T⁻¹])) hs
  rw [_root_.map_add] at hC
  rw [endSym, invert_T, hevi, hev]
  linear_combination -hC

/-- Removing the original positive-p slot creates both reflected Frobenius corrections. -/
theorem canSlots_endSym_original (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (F : (ZMod p)[T;T⁻¹]) :
    endSym (fourUnitField p hp) (canSlots p F) = endSym (fourUnitField p hp) F -
      LaurentPolynomial.C (F.coeff (p : ℤ)) *
        (T (p : ℤ) + T (-(p : ℤ)) - LaurentPolynomial.C (17 / 4 : ZMod p)) := by
  rw [canSlots_endSym, frobeniusEndSym_original p hp]

noncomputable def Tprod (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  originalK1Field p * (WPFiniteWSource.W p).toLaurent +
    originalK0Field p *
      (Polynomial.C (-2 * (5 : ZMod p) ^ ((p - 1) / 2) *
        (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) / 15) *
          originalE4CenteredField p).toLaurent

/-- UW17e's whole VS uses the original Tprod, both canonical holes, and the literal Gclosed. -/
theorem originalWholeVSI_Gclosed (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (WPPIntegralReduction.residueHom p) (originalWholeVSI p hp) =
      endSym (fourUnitField p hp)
        (canSlots p (Tprod p) -
          LaurentPolynomial.C
            (WPFiniteABSourceTail.epsilon p *
              (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) / 15) * originalJa p -
          Gclosed p) := by
  rw [originalWholeVSI_field p hp, originalLogPrimitiveField_Gclosed p hp,
    properEndSymField, properJField_originalJa p hp, endSym_C_mul]
  have hs : (LaurentPolynomial.C (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) :
      (ZMod p)[T;T⁻¹]) * LaurentPolynomial.C (WPFiniteABSourceTail.epsilon p / 15) =
      LaurentPolynomial.C
        (WPFiniteABSourceTail.epsilon p *
          (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) / 15) := by
    rw [← _root_.map_mul]
    congr 1
    ring
  rw [endSym_sub, endSym_sub, endSym_C_mul]
  dsimp only [Tprod]
  rw [← mul_assoc, hs]

/-- The invisible zeroth slot is the actual endpoint centering of the full product carry. -/
theorem originalWholeVSI_field_origin (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (coefficientMap (WPPIntegralReduction.residueHom p) (originalWholeVSI p hp)).coeff 0 =
      -LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)
        (canSlots p (Tprod p)) -
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)⁻¹
        (canSlots p (Tprod p)) := by
  have hJa0 : (originalJa p : (ZMod p)[T;T⁻¹]).coeff 0 = 0 := by
    simpa only [polePrimitive, originalJa] using
      polePrimitive_nonunit_zero p (1 / 4) 4 0 (dvd_zero _)
  have hG0 := Gclosed_nonunit_zero p hp 0 (dvd_zero _)
  obtain ⟨hJa, hJb⟩ := originalJa_endpoints p hp
  obtain ⟨hGa, hGb⟩ := Gclosed_endpoints p hp
  rw [originalWholeVSI_Gclosed p hp, endSym_sub, endSym_sub, endSym_C_mul]
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, C_mul_coeff,
    endSym_origin_coefficient, canSlots_origin p (by omega : 0 < p),
    hJa0, hG0, hJa, hJb, hGa, hGb, mul_zero, sub_zero]
  ring

/-- Every field-derivative-invisible coefficient has its original whole value,
including the retained endpoint constant at zero. -/
theorem originalWholeVSI_field_frobenius (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℤ) (hj : (p : ℤ) ∣ j) :
    (coefficientMap (WPPIntegralReduction.residueHom p) (originalWholeVSI p hp)).coeff j =
      if j = 0 then
        -LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)
          (canSlots p (Tprod p)) -
        LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)⁻¹
          (canSlots p (Tprod p))
      else 0 := by
  by_cases hj0 : j = 0
  · subst j
    simp only [if_true]
    exact originalWholeVSI_field_origin p hp
  · rw [if_neg hj0, coefficientMap_coeff,
      originalWholeVSI_nonzero_frobenius p hp j hj hj0, _root_.map_zero]

end WPFieldAssembly.SourceClosureSigmaGclosed
