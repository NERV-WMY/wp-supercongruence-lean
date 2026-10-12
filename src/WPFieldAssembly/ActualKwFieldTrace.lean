import WPFieldAssembly.LaurentPoleField
import WPLaurentIntegralResidue

open scoped LaurentPolynomial Polynomial
open LaurentPolynomial WPActualChiSource WPActualEtaIntegrality
  WPPIntegralReduction WPLaurentIntegralResidue

namespace WPFieldAssembly.ActualKwFieldTrace

variable {K J : Type*} [CommRing K] [CommRing J]

noncomputable def R : K[T;T⁻¹] := T 1 * (4*T 1-11)
noncomputable def A : K[T;T⁻¹] := (4*T 1-1)*(4-T 1)
noncomputable def dR : K[T;T⁻¹] := 8*T 1-11
noncomputable def dA : K[T;T⁻¹] := -8*T 1+17
noncomputable def delta : K[T;T⁻¹] := A*dR-R*dA

theorem delta_expansion : (delta : K[T;T⁻¹]) = 24*T 1^2-32*T 1+44 := by
  unfold delta A dR R dA
  ring

theorem R_map (f : K →+* J) : coefficientMap f (R : K[T;T⁻¹]) = R := by
  simp only [R, map_mul, map_sub, map_ofNat, coefficientMap_T]

theorem delta_map (f : K →+* J) : coefficientMap f (delta : K[T;T⁻¹]) = delta := by
  simp only [delta, A, dR, R, dA, map_mul, map_sub, map_add,
    map_neg, map_ofNat, map_one, coefficientMap_T]

theorem rational_A : (A : ℚ[T;T⁻¹]) = LaurentPoleTrace.Abar.toLaurent := by
  simp only [A, LaurentPoleTrace.Abar, map_mul, map_sub, map_ofNat, map_one,
    Polynomial.toLaurent_X]

theorem field_A (p : ℕ) [Fact p.Prime] :
    (A : (ZMod p)[T;T⁻¹]) = (LaurentPoleField.fieldAbar p).toLaurent := by
  simp only [A, LaurentPoleField.fieldAbar, map_mul, map_sub, map_ofNat, map_one,
    Polynomial.toLaurent_X]

section Differential
variable {F : Type*} [Field F]

theorem derivative_R : WPFiniteLaurentDifferential.D (R : F[T;T⁻¹]) = dR := by
  have hT : WPFiniteLaurentDifferential.D (T 1 : F[T;T⁻¹]) = 1 := by
    simpa using WPFiniteLaurentDifferential.D_monomial (1 : F) 1
  change WPFiniteLaurentDifferential.D (T 1*(C 4*T 1-C 11)) = 8*T 1-11
  rw [WPFiniteLaurentDifferential.D_mul, map_sub,
    WPFiniteLaurentDifferential.D_C_mul, WPFiniteLaurentDifferential.D_C, hT]
  simp only [map_ofNat, mul_one, one_mul, sub_zero]
  ring

theorem derivative_A : WPFiniteLaurentDifferential.D (A : F[T;T⁻¹]) = dA := by
  have hT : WPFiniteLaurentDifferential.D (T 1 : F[T;T⁻¹]) = 1 := by
    simpa using WPFiniteLaurentDifferential.D_monomial (1 : F) 1
  change WPFiniteLaurentDifferential.D ((C 4*T 1-C 1)*(C 4-T 1)) = -8*T 1+17
  rw [WPFiniteLaurentDifferential.D_mul, map_sub, map_sub,
    WPFiniteLaurentDifferential.D_C_mul, WPFiniteLaurentDifferential.D_C,
    WPFiniteLaurentDifferential.D_C, hT]
  simp only [map_ofNat, map_one, mul_one, sub_zero]
  ring

theorem delta_derivative : (delta : F[T;T⁻¹]) =
    A*WPFiniteLaurentDifferential.D R-R*WPFiniteLaurentDifferential.D A := by
  rw [derivative_R, derivative_A]
  rfl
end Differential

/-- The literal rational Kw numerator is kept before reduction. -/
noncomputable def rationalKw (p : ℕ) : ℚ[T;T⁻¹] :=
  C (3*5^(p-1) : ℚ)*T (p : ℤ)*(4*T 1-11)^p

theorem rationalKw_factor (p : ℕ) :
    rationalKw p = C (3*5^(p-1) : ℚ)*(R : ℚ[T;T⁻¹])^p := by
  simp only [rationalKw, R, mul_pow, T_pow, mul_one]
  ring

noncomputable def integralKw (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[T;T⁻¹] := C (3*5^(p-1))*R^p

noncomputable def rationalKwDlog (p : ℕ) : ℚ[T;T⁻¹] :=
  C (3*5^(p-1) : ℚ)*R^(p-1)*delta

noncomputable def integralKwDlog (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[T;T⁻¹] := C (3*5^(p-1))*R^(p-1)*delta

theorem integralKw_rational (p : ℕ) [Fact p.Prime] :
    coefficientMap (integralRationals p).subtype (integralKw p) = rationalKw p := by
  rw [rationalKw_factor]
  rw [integralKw, map_mul, coefficientMap_C, map_pow, R_map]
  rfl

theorem integralKwDlog_rational (p : ℕ) [Fact p.Prime] :
    coefficientMap (integralRationals p).subtype (integralKwDlog p) = rationalKwDlog p := by
  unfold integralKwDlog rationalKwDlog
  rw [map_mul, map_mul, coefficientMap_C, map_pow, R_map, delta_map]
  rfl

theorem five_fermat (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (5 : ZMod p)^(p-1) = 1 := by
  have h5 : (5 : ZMod p) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  exact ZMod.pow_card_sub_one_eq_one h5

theorem integralKw_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (integralKw p) = 3*(R : (ZMod p)[T;T⁻¹])^p := by
  have hs : residueHom p (3*5^(p-1) : integralRationals p) = (3 : ZMod p) := by
    simp only [map_mul, map_pow, map_ofNat, five_fermat p hp, mul_one]
  rw [integralKw, map_mul, coefficientMap_C, map_pow, R_map, hs, map_ofNat]

theorem integralKwDlog_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (integralKwDlog p) =
      3*(R : (ZMod p)[T;T⁻¹])^(p-1)*delta := by
  have hs : residueHom p (3*5^(p-1) : integralRationals p) = (3 : ZMod p) := by
    simp only [map_mul, map_pow, map_ofNat, five_fermat p hp, mul_one]
  rw [integralKwDlog, map_mul, map_mul, coefficientMap_C, map_pow,
    R_map, delta_map, hs, map_ofNat]

theorem rationalKw_integral (p : ℕ) [Fact p.Prime] :
    rationalKw p ∈ integralLaurent p := by
  rw [← integralKw_rational p]
  exact coefficientMap_subtype_integral p _

theorem rationalKwDlog_integral (p : ℕ) [Fact p.Prime] :
    rationalKwDlog p ∈ integralLaurent p := by
  rw [← integralKwDlog_rational p]
  exact coefficientMap_subtype_integral p _

theorem reduce_integral_map (p : ℕ) [Fact p.Prime]
    (P : (integralRationals p)[T;T⁻¹]) :
    reduceLaurent p (coefficientMap (integralRationals p).subtype P) =
      coefficientMap (residueHom p) P := by
  ext j
  rw [reduceLaurent_coeff, coefficientMap_coeff, coefficientMap_coeff]
  rfl

theorem integralLift_residue (p : ℕ) [Fact p.Prime] (L : ℚ[T;T⁻¹])
    (hL : L ∈ integralLaurent p) :
    coefficientMap (residueHom p) (integralLift p ⟨L,hL⟩) = reduceLaurent p L := by
  rw [← reduce_integral_map, integralLift_rational]

theorem rationalKw_product_reduce (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (L : ℚ[T;T⁻¹]) (hL : L ∈ integralLaurent p) :
    reduceLaurent p (rationalKw p*L) =
      3*(R : (ZMod p)[T;T⁻¹])^p*reduceLaurent p L := by
  have h := reduce_integral_map p (integralKw p*integralLift p ⟨L,hL⟩)
  simpa only [map_mul, integralKw_rational, integralLift_rational,
    integralKw_residue p hp, integralLift_residue] using h

theorem rationalKwDlog_product_reduce (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (L : ℚ[T;T⁻¹]) (hL : L ∈ integralLaurent p) :
    reduceLaurent p (rationalKwDlog p*L) =
      3*(R : (ZMod p)[T;T⁻¹])^(p-1)*delta*reduceLaurent p L := by
  have h := reduce_integral_map p (integralKwDlog p*integralLift p ⟨L,hL⟩)
  simpa only [map_mul, integralKwDlog_rational, integralLift_rational,
    integralKwDlog_residue p hp, integralLift_residue] using h

theorem fieldTrace_C_mul (p m : ℕ) [Fact p.Prime] (a : ZMod p)
    (P : (ZMod p)[T;T⁻¹]) :
    LaurentPoleField.fieldTrace p m (C a*P) = a*LaurentPoleField.fieldTrace p m P := by
  simpa only [LaurentPolynomial.smul_eq_C_mul, smul_eq_mul] using
    (LaurentPoleField.fieldTrace p m).map_smul a P

theorem fieldTrace_three_mul (p m : ℕ) [Fact p.Prime]
    (P : (ZMod p)[T;T⁻¹]) :
    LaurentPoleField.fieldTrace p m (3*P) =
      3*LaurentPoleField.fieldTrace p m P := by
  simpa only [map_ofNat] using fieldTrace_C_mul p m (3 : ZMod p) P

theorem fieldKw_trace_cartier (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (L : (ZMod p)[T;T⁻¹]) :
    LaurentPoleField.fieldTrace p p (3*R^p*L) =
      3*LaurentPoleField.fieldTrace p 1
        (R*WPFiniteCartier.cartier p (Fact.out : p.Prime).pos L) := by
  rw [mul_assoc, fieldTrace_three_mul]
  have h := LaurentPoleField.trace_frobenius_cartier p 1 hp (R^p*L)
  rw [Nat.mul_one, WPFiniteCartier.cartier_frobenius_product] at h
  rw [h]

theorem actualKw_trace_reduce (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (L : ℚ[T;T⁻¹]) (hL : L ∈ integralLaurent p) :
    ((LaurentPoleTrace.trace p (rationalKw p*L) : ℚ) : ZMod p) =
      3*LaurentPoleField.fieldTrace p 1
        (R*WPFiniteCartier.cartier p (Fact.out : p.Prime).pos (reduceLaurent p L)) := by
  rw [LaurentPoleField.trace_reduce p p hp _
    ((integralLaurent p).mul_mem (rationalKw_integral p) hL),
    rationalKw_product_reduce p hp L hL, fieldKw_trace_cartier p hp]

theorem rationalKwDlog_literal (p : ℕ) : rationalKwDlog p =
    C (3*5^(p-1) : ℚ)*(R : ℚ[T;T⁻¹])^(p-1)*
      (LaurentPoleTrace.Abar.toLaurent*WPFiniteLaurentDifferential.D R-
        R*WPFiniteLaurentDifferential.D LaurentPoleTrace.Abar.toLaurent) := by
  rw [rationalKwDlog, delta_derivative, rational_A]

theorem rationalKwDlog_clearing (p : ℕ) (hp : 0 < p) :
    rationalKwDlog p*(R : ℚ[T;T⁻¹]) = rationalKw p*delta := by
  have hp1 : p-1+1 = p := by omega
  have hpow : (R : ℚ[T;T⁻¹])^p = R^(p-1)*R := by
    simpa only [hp1] using pow_succ (R : ℚ[T;T⁻¹]) (p-1)
  rw [rationalKwDlog, rationalKw_factor, hpow]
  ring

theorem derivative_R_power (n : ℕ) :
    WPFiniteLaurentDifferential.D ((R : ℚ[T;T⁻¹])^n) =
      C (n : ℚ)*R^(n-1)*WPFiniteLaurentDifferential.D R := by
  let P : ℚ[X] := Polynomial.X*(4*Polynomial.X-11)
  have hP : P.toLaurent = (R : ℚ[T;T⁻¹]) := by
    dsimp only [P, R]
    simp only [map_mul, map_sub, map_ofNat, Polynomial.toLaurent_X]
  have h := congrArg (fun Q : ℚ[X] => Q.toLaurent) (Polynomial.derivative_pow P n)
  simpa only [map_mul, Polynomial.toLaurent_C, map_pow,
    ← WPFiniteLaurentDifferential.D_toLaurent, hP] using h

theorem rationalKw_derivative (p : ℕ) :
    WPFiniteLaurentDifferential.D (rationalKw p) =
      C (p : ℚ)*(C (3*5^(p-1) : ℚ)*R^(p-1)*WPFiniteLaurentDifferential.D R) := by
  rw [rationalKw_factor, WPFiniteLaurentDifferential.D_C_mul, derivative_R_power]
  ring

/-- The complete derivative numerator is divisible by p over Q before any reduction. -/
theorem rationalKw_derivative_division (p : ℕ) (hp : 0 < p) :
    LaurentPoleTrace.Abar.toLaurent*WPFiniteLaurentDifferential.D (rationalKw p)-
      C (p : ℚ)*rationalKw p*WPFiniteLaurentDifferential.D LaurentPoleTrace.Abar.toLaurent =
        C (p : ℚ)*rationalKwDlog p := by
  have hp1 : p-1+1 = p := by omega
  have hpow : (R : ℚ[T;T⁻¹])^p = R^(p-1)*R := by
    simpa only [hp1] using pow_succ (R : ℚ[T;T⁻¹]) (p-1)
  rw [← rational_A, rationalKw_derivative, rationalKw_factor, rationalKwDlog,
    hpow, delta_derivative]
  ring

theorem rationalKwDlog_divided_numerator (p : ℕ) (hp : 0 < p) :
    C (1/(p : ℚ))*(LaurentPoleTrace.Abar.toLaurent*WPFiniteLaurentDifferential.D (rationalKw p)-
      C (p : ℚ)*rationalKw p*WPFiniteLaurentDifferential.D LaurentPoleTrace.Abar.toLaurent) =
        rationalKwDlog p := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  rw [rationalKw_derivative_division p hp, ← mul_assoc, ← map_mul,
    one_div_mul_cancel hpq, map_one, one_mul]

theorem actualKwDlog_trace_reduce (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (L : ℚ[T;T⁻¹]) (hL : L ∈ integralLaurent p) :
    ((LaurentPoleTrace.trace (p+1) (rationalKwDlog p*L) : ℚ) : ZMod p) =
      3*LaurentPoleField.fieldTrace p (p+1)
        (R^(p-1)*((LaurentPoleField.fieldAbar p).toLaurent*WPFiniteLaurentDifferential.D R-
          R*WPFiniteLaurentDifferential.D (LaurentPoleField.fieldAbar p).toLaurent)*
          reduceLaurent p L) := by
  rw [LaurentPoleField.trace_reduce p (p+1) hp _
    ((integralLaurent p).mul_mem (rationalKwDlog_integral p) hL),
    rationalKwDlog_product_reduce p hp L hL,
    mul_assoc (3 : (ZMod p)[T;T⁻¹]), mul_assoc (3 : (ZMod p)[T;T⁻¹]),
    fieldTrace_three_mul, delta_derivative, field_A]

theorem fieldKwDlog_trace_split (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (L : (ZMod p)[T;T⁻¹]) :
    LaurentPoleField.fieldTrace p (p+1) (3*R^(p-1)*delta*L) =
      3*(LaurentPoleField.fieldTrace p p (R^(p-1)*dR*L)-
        LaurentPoleField.fieldTrace p (p+1) (R^p*dA*L)) := by
  have hp1 : p-1+1 = p := by omega
  have hpow : (R : (ZMod p)[T;T⁻¹])^p = R^(p-1)*R := by
    simpa only [hp1] using pow_succ (R : (ZMod p)[T;T⁻¹]) (p-1)
  have he : (3*R^(p-1)*delta*L : (ZMod p)[T;T⁻¹]) =
      C 3*(A*(R^(p-1)*dR*L)-R^p*dA*L) := by
    rw [hpow, delta]
    simp only [map_ofNat]
    ring
  rw [he, fieldTrace_C_mul, map_sub, field_A,
    LaurentPoleField.fieldTrace_cleared p p hp]

end WPFieldAssembly.ActualKwFieldTrace
