import WPFieldAssembly.NativeChiResidue
import WPFieldAssembly.NativeShiftedChi

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPPIntegralReduction WPActualEtaIntegrality
  WPActualChiSource WPLaurentIntegralResidue WPFiniteLaurentDifferential
  WPHasseIntegralTransport WPActualNativeHasse WPActualEtaPole WPActualPullbackSource
  WPFieldAssembly.NativeChiCovariance WPFieldAssembly.NativeChiResidue
  WPFieldAssembly.NativeShiftedChi
  WPFiniteJCarrier

namespace WPFieldAssembly.NativeChiFieldSource

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

noncomputable def laurentConcomitant {K : Type*} [Field K]
    (a2 a1 a0 f g : K[T;T⁻¹]) : K[T;T⁻¹] :=
  a2 * (f * D (D g) + g * D (D f) - D f * D g) +
    a1 * (f * D g + g * D f) + a0 * f * g

noncomputable def liftOfLaurent (p : ℕ) [Fact p.Prime] (P : ℚ[X])
    (hP : P.toLaurent ∈ integralLaurent p) : (integralRationals p)[X] :=
  integralPolynomialLift p P
    (fun n => by
      have h := hP (n : ℤ)
      rw [toLaurent_coeff_nat] at h
      exact h)

theorem liftOfLaurent_mapQ (p : ℕ) [Fact p.Prime] (P : ℚ[X])
    (hP : P.toLaurent ∈ integralLaurent p) :
    (liftOfLaurent p P hP).map (integralRationals p).subtype = P := by
  unfold liftOfLaurent
  exact integralPolynomialLift_rational _ _ _

noncomputable def polynomialLaurentModel (p : ℕ) [Fact p.Prime]
    (P : (integralRationals p)[X]) : integralLaurent p :=
  ⟨(P.map (integralRationals p).subtype).toLaurent, by
    rw [← coefficientMap_toLaurent]
    exact coefficientMap_subtype_integral p P.toLaurent⟩

theorem polynomialLaurentModel_val (p : ℕ) [Fact p.Prime]
    (P : (integralRationals p)[X]) :
    (polynomialLaurentModel p P).val =
      (P.map (integralRationals p).subtype).toLaurent := rfl

theorem residue_polynomialLaurentModel (p : ℕ) [Fact p.Prime]
    (P : (integralRationals p)[X]) :
    residueLaurent p (polynomialLaurentModel p P) =
      (P.map (residueHom p)).toLaurent := by
  have hLift : integralLift p (polynomialLaurentModel p P) = P.toLaurent := by
    apply WPLaurentIntegralResidue.coefficientMap_injective
      (integralRationals p).subtype (Subring.subtype_injective (integralRationals p))
    rw [integralLift_rational, coefficientMap_toLaurent]
    rfl
  change coefficientMap (residueHom p) (integralLift p _) = _
  rw [hLift, coefficientMap_toLaurent]

noncomputable def integralD (p : ℕ) [Fact p.Prime]
    (P : integralLaurent p) : integralLaurent p :=
  ⟨D P.val, integral_D p P.val P.property⟩

theorem integralD_val (p : ℕ) [Fact p.Prime] (P : integralLaurent p) :
    (integralD p P).val = D P.val := rfl

theorem integral_sub_val (p : ℕ) [Fact p.Prime] (F G : integralLaurent p) :
    (F - G).val = F.val - G.val := rfl

theorem residue_integralD (p : ℕ) [Fact p.Prime] (P : integralLaurent p) :
    residueLaurent p (integralD p P) = D (residueLaurent p P) := by
  ext j
  rw [D_coeff, residueLaurent_coeff, residueLaurent_coeff]
  change residueHom p ⟨(D P.val).coeff j, (integralD p P).property j⟩ =
    ((j + 1 : ℤ) : ZMod p) *
      residueHom p ⟨P.val.coeff (j + 1), P.property (j + 1)⟩
  have hc : (⟨(D P.val).coeff j, (integralD p P).property j⟩ : integralRationals p) =
      ((j + 1 : ℤ) : integralRationals p) *
        ⟨P.val.coeff (j + 1), P.property (j + 1)⟩ := by
    apply Subtype.ext
    change (D P.val).coeff j = ((j + 1 : ℤ) : ℚ) * P.val.coeff (j + 1)
    exact D_coeff P.val j
  rw [hc, map_mul, map_intCast]

noncomputable def integralT (p : ℕ) [Fact p.Prime] (j : ℤ) : integralLaurent p :=
  ⟨T j, integral_T p j⟩

theorem residue_integralT (p : ℕ) [Fact p.Prime] (j : ℤ) :
    residueLaurent p (integralT p j) = T j := by
  have hLift : integralLift p (integralT p j) = T j := by
    apply WPLaurentIntegralResidue.coefficientMap_injective
      (integralRationals p).subtype (Subring.subtype_injective (integralRationals p))
    rw [integralLift_rational, coefficientMap_T]
    rfl
  change coefficientMap (residueHom p) (integralLift p _) = _
  rw [hLift, coefficientMap_T]

noncomputable def c2Integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  liftOfLaurent p NativeChiCovariance.c2
    (covariance_coefficients_integral p (by omega)).1

noncomputable def c1Integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  liftOfLaurent p NativeChiCovariance.c1
    (covariance_coefficients_integral p (by omega)).2.1

noncomputable def c0Integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  liftOfLaurent p NativeChiCovariance.c0
    (covariance_coefficients_integral p (by omega)).2.2.1

theorem c2Integral_mapQ (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (c2Integral p hp).map (integralRationals p).subtype = NativeChiCovariance.c2 := by
  exact liftOfLaurent_mapQ _ _ _

theorem c1Integral_mapQ (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (c1Integral p hp).map (integralRationals p).subtype = NativeChiCovariance.c1 := by
  exact liftOfLaurent_mapQ _ _ _

theorem c0Integral_mapQ (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (c0Integral p hp).map (integralRationals p).subtype = NativeChiCovariance.c0 := by
  exact liftOfLaurent_mapQ _ _ _

noncomputable def c2Field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (ZMod p)[X] :=
  (c2Integral p hp).map (residueHom p)
noncomputable def c1Field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (ZMod p)[X] :=
  (c1Integral p hp).map (residueHom p)
noncomputable def c0Field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (ZMod p)[X] :=
  (c0Integral p hp).map (residueHom p)

noncomputable def halfPullbackIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  (nativeIntegral p ((p - 1) / 2) (by omega) (by omega)).comp (integralV p (by omega))

theorem halfPullbackIntegral_mapQ (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (halfPullbackIntegral p hp).map (integralRationals p).subtype = nativeHalfPullback p := by
  simp only [halfPullbackIntegral, Polynomial.map_comp,
    nativeIntegral_map_rational, integralV_map_rational, nativeHalfPullback]

theorem halfPullbackIntegral_mapField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (halfPullbackIntegral p hp).map (residueHom p) =
      (nativeField p ((p - 1) / 2)).comp (fieldV p) := by
  simp only [halfPullbackIntegral, Polynomial.map_comp,
    nativeIntegral_map_field, integralV_map_field]

noncomputable def halfPullbackField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (ZMod p)[X] :=
  (halfPullbackIntegral p hp).map (residueHom p)

theorem halfPullbackField_eq (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    halfPullbackField p hp = (nativeField p ((p - 1) / 2)).comp (fieldV p) :=
  halfPullbackIntegral_mapField p hp

theorem halfPullbackLaurent_val (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (polynomialLaurentModel p (halfPullbackIntegral p hp)).val =
      Fpull ((p - 1) / 2) Vx := by
  rw [polynomialLaurentModel_val, halfPullbackIntegral_mapQ]
  unfold nativeHalfPullback
  exact (Fpull_toLaurent ((p - 1) / 2)).symm

noncomputable def integralHalf (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : integralRationals p :=
  ⟨1 / 2, WPFiniteConductorPolynomial.small_inverse_integral p 2 (by omega) (by omega)⟩
noncomputable def halfField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : ZMod p :=
  residueHom p (integralHalf p hp)
noncomputable def halfLaurent (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : integralLaurent p :=
  ⟨LaurentPolynomial.C (integralHalf p hp).val, integral_C p _ (integralHalf p hp).property⟩

theorem residue_halfLaurent (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueLaurent p (halfLaurent p hp) = LaurentPolynomial.C (halfField p hp) := by
  change residueLaurent p ⟨LaurentPolynomial.C (integralHalf p hp).val, _⟩ =
    LaurentPolynomial.C ((integralHalf p hp).val : ZMod p)
  exact residueLaurent_C p (integralHalf p hp)

theorem two_mul_halfField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    2 * halfField p hp = 1 := by
  have hi : (2 : integralRationals p) * integralHalf p hp = 1 := by
    apply Subtype.ext
    change (2 : ℚ) * (1 / 2) = 1
    norm_num
  have he := congrArg (residueHom p) hi
  simpa only [halfField, map_mul, map_ofNat, map_one] using he

theorem halfField_eq (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    halfField p hp = (1 / 2 : ZMod p) := by
  have h2 : (2 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  apply mul_left_cancel₀ h2
  rw [two_mul_halfField]
  field_simp [h2]

noncomputable def halfChiField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (ZMod p)[T;T⁻¹] :=
  residueLaurent p (halfChiIntegral p hp)

noncomputable def integralConcomitant (p : ℕ) [Fact p.Prime]
    (a2 a1 a0 f g : integralLaurent p) : integralLaurent p :=
  a2 * (f * integralD p (integralD p g) + g * integralD p (integralD p f) -
      integralD p f * integralD p g) +
    a1 * (f * integralD p g + g * integralD p f) + a0 * f * g

noncomputable def sourceIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : integralLaurent p :=
  let a2 := polynomialLaurentModel p (c2Integral p hp)
  let a1 := polynomialLaurentModel p (c1Integral p hp)
  let a0 := polynomialLaurentModel p (c0Integral p hp)
  let f := polynomialLaurentModel p (halfPullbackIntegral p hp)
  let χ := halfChiIntegral p hp
  let u := integralT p (-1)
  let h := halfLaurent p hp
  integralConcomitant p a2 a1 a0 f χ +
    h * (u * a1 - u ^ 2 * a2) * f ^ 2 + h * u * a2 * f * integralD p f

theorem integralConcomitant_val (p : ℕ) [Fact p.Prime]
    (a2 a1 a0 f g : integralLaurent p) :
    (integralConcomitant p a2 a1 a0 f g).val =
      a2.val * (f.val * D (D g.val) + g.val * D (D f.val) - D f.val * D g.val) +
        a1.val * (f.val * D g.val + g.val * D f.val) + a0.val * f.val * g.val := rfl

theorem sourceIntegral_val (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (sourceIntegral p hp).val =
      NativeChiCovariance.concomitant (Fpull ((p - 1) / 2) Vx)
        (chiX p ((p - 1) / 2) ((p - 1) / 2)) +
      NativeChiCovariance.forcing (Fpull ((p - 1) / 2) Vx) := by
  simp only [sourceIntegral, Subring.coe_add, Subring.coe_mul, integral_sub_val,
    Subring.coe_pow, integralConcomitant_val, polynomialLaurentModel_val, integralD_val]
  simp only [c2Integral_mapQ, c1Integral_mapQ, c0Integral_mapQ, halfPullbackIntegral_mapQ]
  change laurentConcomitant NativeChiCovariance.c2.toLaurent
    NativeChiCovariance.c1.toLaurent NativeChiCovariance.c0.toLaurent
      (nativeHalfPullback p).toLaurent (chiX p ((p - 1) / 2) ((p - 1) / 2)) +
    LaurentPolynomial.C (1 / 2 : ℚ) *
      (T (-1) * NativeChiCovariance.c1.toLaurent - T (-1) ^ 2 * NativeChiCovariance.c2.toLaurent) *
        (nativeHalfPullback p).toLaurent ^ 2 +
      LaurentPolynomial.C (1 / 2 : ℚ) * T (-1) * NativeChiCovariance.c2.toLaurent *
        (nativeHalfPullback p).toLaurent * D (nativeHalfPullback p).toLaurent = _
  simp only [nativeHalfPullback, ← Fpull_toLaurent, laurentConcomitant]
  simp only [NativeChiCovariance.concomitant, NativeChiCovariance.forcing,
    NativeChiCovariance.r0, NativeChiCovariance.r1]
  ring

theorem sourceIntegral_residueZero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueLaurent p (sourceIntegral p hp) = 0 := by
  rcases actual_half_chi_source_residueZero p hp with ⟨hS, hz⟩
  have hSubtype : sourceIntegral p hp =
      ⟨NativeChiCovariance.concomitant (Fpull ((p - 1) / 2) Vx)
          (chiX p ((p - 1) / 2) ((p - 1) / 2)) +
        NativeChiCovariance.forcing (Fpull ((p - 1) / 2) Vx), hS⟩ :=
    Subtype.ext (sourceIntegral_val p hp)
  rw [hSubtype]
  exact hz

theorem actual_half_chi_field_laurent_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let f := (halfPullbackField p hp).toLaurent
    let χ := halfChiField p hp
    laurentConcomitant (c2Field p hp).toLaurent (c1Field p hp).toLaurent
        (c0Field p hp).toLaurent f χ +
      LaurentPolynomial.C (halfField p hp) *
        (T (-1) * (c1Field p hp).toLaurent - T (-1) ^ 2 * (c2Field p hp).toLaurent) * f ^ 2 +
      LaurentPolynomial.C (halfField p hp) * T (-1) * (c2Field p hp).toLaurent * f * D f = 0 := by
  have hz := sourceIntegral_residueZero p hp
  simpa only [sourceIntegral, integralConcomitant, laurentConcomitant,
    map_add, map_sub, map_mul, map_pow, residue_integralD,
    residue_polynomialLaurentModel, residue_integralT, residue_halfLaurent,
    c2Field, c1Field, c0Field, halfPullbackField, halfChiField] using hz

theorem actual_half_chi_native_field_laurent_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let N := (p - 1) / 2
    let f := ((nativeField p N).comp (fieldV p)).toLaurent
    let χ := residueLaurent p (halfChiIntegral p hp)
    laurentConcomitant (c2Field p hp).toLaurent (c1Field p hp).toLaurent
        (c0Field p hp).toLaurent f χ +
      LaurentPolynomial.C (1 / 2 : ZMod p) *
        (T (-1) * (c1Field p hp).toLaurent - T (-1) ^ 2 * (c2Field p hp).toLaurent) * f ^ 2 +
      LaurentPolynomial.C (1 / 2 : ZMod p) * T (-1) * (c2Field p hp).toLaurent * f * D f = 0 := by
  have hz := actual_half_chi_field_laurent_source p hp
  simpa only [halfPullbackField_eq, halfField_eq, halfChiField] using hz

noncomputable def selfIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : integralLaurent p :=
  let f := polynomialLaurentModel p (halfPullbackIntegral p hp)
  integralConcomitant p (polynomialLaurentModel p (c2Integral p hp))
    (polynomialLaurentModel p (c1Integral p hp))
    (polynomialLaurentModel p (c0Integral p hp)) f f

theorem selfIntegral_val (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (selfIntegral p hp).val = NativeChiCovariance.concomitant
      (Fpull ((p - 1) / 2) Vx) (Fpull ((p - 1) / 2) Vx) := by
  simp only [selfIntegral, integralConcomitant_val, polynomialLaurentModel_val]
  rw [c2Integral_mapQ, c1Integral_mapQ, c0Integral_mapQ, halfPullbackIntegral_mapQ]
  simp only [nativeHalfPullback, ← Fpull_toLaurent, NativeChiCovariance.concomitant]

/-- The actual integral self norm has a p² factor before reduction. -/
theorem actual_half_self_field_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    laurentConcomitant (c2Field p hp).toLaurent (c1Field p hp).toLaurent
      (c0Field p hp).toLaurent (halfPullbackField p hp).toLaurent
        (halfPullbackField p hp).toLaurent = 0 := by
  rcases actual_half_self_concomitant_quotient p hp with ⟨K, hK⟩
  have hself : selfIntegral p hp = (p : integralLaurent p) ^ 2 * K := by
    apply Subtype.ext
    rw [selfIntegral_val, hK]
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast]
    rw [map_pow]
    rfl
  have hz : residueLaurent p (selfIntegral p hp) = 0 := by
    rw [hself, map_mul, map_pow, map_natCast]
    have hp0 : (p : (ZMod p)[T;T⁻¹]) = 0 := by
      change LaurentPolynomial.C (p : ZMod p) = 0
      rw [ZMod.natCast_self, map_zero]
    rw [hp0, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
  simpa only [selfIntegral, integralConcomitant, laurentConcomitant, map_add,
    map_sub, map_mul, residue_integralD, residue_polynomialLaurentModel,
    c2Field, c1Field, c0Field, halfPullbackField] using hz

end WPFieldAssembly.NativeChiFieldSource
