import WPActualResonanceReduction
import WPActualEtaFieldCutoff

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource
open WPActualEtaIntegration WPActualEtaSupport WPActualEtaPrimitive
open WPActualEtaPole WPPIntegralReduction WPActualChiSource
open WPActualEtaIntegrality WPLaurentIntegralResidue WPActualResonanceReduction
open WPQuadraticRationalCartier

namespace WPActualCanonicalSource

private def doubleIndex : ℤ →+ ℤ where
  toFun j := 2 * j
  map_zero' := by ring
  map_add' := by intros; ring

noncomputable def squareOver {R : Type*} [CommRing R] : R[T;T⁻¹] →+* R[T;T⁻¹] :=
  AddMonoidAlgebra.mapDomainRingHom R doubleIndex

theorem squareOver_monomial {R : Type*} [CommRing R] (c : R) (j : ℤ) :
    squareOver (C c * T j) = C c * T (2 * j) := by
  simp [squareOver, doubleIndex, ← single_eq_C_mul_T]

theorem squareOver_map_rational {R : Type*} [CommRing R] (f : R →+* ℚ) (P : R[T;T⁻¹]) :
    coefficientMap f (squareOver P) = squareX (coefficientMap f P) := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, map_add, map_add, hP, hQ]
  | C_mul_T j c =>
    rw [squareOver_monomial, coefficientMap_monomial, coefficientMap_monomial, squareX_monomial]

theorem squareOver_map_field (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] (f : R →+* ZMod p) (P : R[T;T⁻¹]) :
    coefficientMap f (squareOver P) = squareSubstitute p (coefficientMap f P) := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, map_add, map_add, hP, hQ]
  | C_mul_T j c =>
    rw [squareOver_monomial, coefficientMap_monomial, coefficientMap_monomial,
      squareSubstitute_monomial]

theorem squareX_integral (p : ℕ) [Fact p.Prime] (P : ℚ[T;T⁻¹])
    (hP : P ∈ integralLaurent p) : squareX P ∈ integralLaurent p := by
  have h := coefficientMap_subtype_integral p (squareOver (integralLift p ⟨P, hP⟩))
  rw [squareOver_map_rational, integralLift_rational] at h
  exact h

theorem reduceLaurent_eq_residueLaurent (p : ℕ) [Fact p.Prime]
    (P : ℚ[T;T⁻¹]) (hP : P ∈ integralLaurent p) :
    reduceLaurent p P = residueLaurent p ⟨P, hP⟩ := by
  ext j
  rw [reduceLaurent_coeff, residueLaurent_coeff]

theorem reduceLaurent_squareX (p : ℕ) [Fact p.Prime] (P : ℚ[T;T⁻¹])
    (hP : P ∈ integralLaurent p) :
    reduceLaurent p (squareX P) = squareSubstitute p (reduceLaurent p P) := by
  have hs : squareX P =
      coefficientMap (integralRationals p).subtype (squareOver (integralLift p ⟨P, hP⟩)) := by
    rw [squareOver_map_rational, integralLift_rational]
  rw [hs, reduceLaurent_integral_map, squareOver_map_field,
    ← reduceLaurent_integral_map, integralLift_rational]

theorem derivative_coefficient (P : ℚ[T;T⁻¹]) (j : ℤ) :
    (derivative P).coeff j = ((j + 1 : ℤ) : ℚ) * P.coeff (j + 1) := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    ring
  | C_mul_T n c =>
    rw [derivative_monomial, finite_monomial_coeff, finite_monomial_coeff]
    by_cases h : n = j + 1
    · subst n
      simp
      ring
    · have hn : n - 1 ≠ j := by omega
      simp [h, hn]

theorem derivative_integral (p : ℕ) [Fact p.Prime] (P : ℚ[T;T⁻¹])
    (hP : P ∈ integralLaurent p) : derivative P ∈ integralLaurent p := by
  intro j
  rw [derivative_coefficient]
  exact (integralRationals p).mul_mem
    (intCast_mem (integralRationals p) (j + 1)) (hP (j + 1))

theorem derivative_bounded (P : ℚ[T;T⁻¹]) (lo hi : ℤ)
    (hP : bounded P lo hi) : bounded (derivative P) (lo - 1) (hi - 1) := by
  intro j hj
  have hq : P.coeff (j + 1) ≠ 0 := by
    intro hzero
    rw [derivative_coefficient, hzero, mul_zero] at hj
    exact hj rfl
  have h := hP (j + 1) hq
  omega

theorem squareX_bounded (P : ℚ[T;T⁻¹]) (lo hi : ℤ) (hP : bounded P lo hi) :
    bounded (squareX P) (2 * lo) (2 * hi) := by
  classical
  intro j hj
  have hmem := Finsupp.mem_support_iff.mpr hj
  change j ∈ (P.coeff.mapDomain (fun n : ℤ => 2 * n)).support at hmem
  obtain ⟨n, hn, hnj⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
  have h := hP n (Finsupp.mem_support_iff.mp hn)
  omega

theorem Vpull_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    Vpull ∈ integralLaurent p := by
  have h := coefficientMap_subtype_integral p (integralPullV p hp)
  rw [integralPullV_map_rational] at h
  exact h

theorem logarithmicSDensity_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    logarithmicSDensity p ∈ integralLaurent p := by
  let L := integralLaurent p
  have hV := Vpull_integral p hp
  exact L.sub_mem
    (L.mul_mem (L.mul_mem (integral_T p _) (L.pow_mem hV _))
      (derivative_integral p Vpull hV))
    (L.mul_mem (L.pow_mem hV _) (integral_T p _))

theorem logarithmicSDensity_bounded (p : ℕ) (hp : 1 ≤ p) :
    bounded (logarithmicSDensity p) (-(p : ℤ) - 1) (5 * (p : ℤ) - 1) := by
  unfold logarithmicSDensity baseDensity
  apply bounded_sub
  · apply bounded_mono
      (bounded_mul (bounded_mul (bounded_T _) (bounded_pow Vpull_bounded (p - 1)))
        (derivative_bounded Vpull 0 6 Vpull_bounded)) <;> omega
  · apply bounded_mono
      (bounded_mul (bounded_pow Vpull_bounded p) (bounded_T _)) <;> omega

/-- The original canonical density with both endpoints and all signed coefficients. -/
noncomputable def canonicalSource (p N e : ℕ) : ℚ[T;T⁻¹] :=
  logarithmicSDensity p * actualCanonicalPullback p N e

theorem canonicalPeriod_eq_rationalPrimitive (p N e : ℕ) :
    canonicalPeriod p N e = rationalPrimitive p (canonicalSource p N e) :=
  (rationalPrimitive_eq_endpointIntegral p (canonicalSource p N e)).symm

theorem canonicalSource_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    canonicalSource p ((p - 1) / 2) (p - 1 - p / 6) ∈ integralLaurent p := by
  exact (integralLaurent p).mul_mem (logarithmicSDensity_integral p (by omega))
    (squareX_integral p _ (actual_native_cutoff_Aeta_integral p hp))

/-- The original logarithmic coefficient is a complete even Laurent pullback. -/
theorem canonicalSource_normalform (p N e : ℕ) :
    canonicalSource p N e = T (-(p : ℤ) - 1) *
      squareX ((C 2 * T 1 * WPActualEtaPole.Vx ^ (p - 1) *
        derivative WPActualEtaPole.Vx - WPActualEtaPole.Vx ^ p) * Aeta p N e) := by
  have hd : derivative Vpull = C 2 * T 1 * squareX (derivative WPActualEtaPole.Vx) := by
    rw [← squareX_Vx, squareX_derivative]
  have ht : (T (-(p : ℤ)) * T 1 : ℚ[T;T⁻¹]) = T (-(p : ℤ) - 1) * T 2 := by
    rw [← T_add, ← T_add]
    congr 1
    omega
  unfold canonicalSource logarithmicSDensity baseDensity actualCanonicalPullback
  rw [hd]
  simp only [map_mul, map_sub, map_pow, squareX_C, squareX_T, squareX_Vx]
  calc
    _ = (C 2 * Vpull ^ (p - 1) * squareX (derivative WPActualEtaPole.Vx) *
        (T (-(p : ℤ)) * T 1) -
          Vpull ^ p * T (-(p : ℤ) - 1)) * squareX (Aeta p N e) := by ring
    _ = _ := by rw [ht]; ring

theorem canonicalSource_no_log (p : ℕ) (hp : Odd p) (N e : ℕ) :
    (canonicalSource p N e).coeff (-1) = 0 := by
  rw [canonicalSource_normalform]
  have he : (T (-(p : ℤ) - 1) : ℚ[T;T⁻¹]) =
      C 1 * T (-(p : ℤ) - 1) := by simp
  rw [he, WPFiniteCartier.coefficient_monomial_mul]
  have hj : Odd (-1 - (-(p : ℤ) - 1)) := by
    rw [show -1 - (-(p : ℤ) - 1) = (p : ℤ) by ring]
    exact_mod_cast hp
  rw [squareX_odd_coefficient _ _ hj, one_mul]

theorem canonicalSource_bounded (p N e : ℕ) (hp : 1 ≤ p) (hN : N ≤ e) (he : 1 ≤ e) :
    bounded (canonicalSource p N e)
      (-(p : ℤ) - 1 + 2 * ((N : ℤ) - 3 * (e : ℤ) + 1))
      (5 * (p : ℤ) - 1 + 6 * (e : ℤ)) := by
  unfold canonicalSource actualCanonicalPullback
  apply bounded_mono
    (bounded_mul (logarithmicSDensity_bounded p hp)
      (squareX_bounded _ _ _ (actual_Aeta_full_support p N e hN he))) <;> omega

theorem canonicalSource_primitive_bounds (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℤ) (hj : j ∈ (canonicalSource p ((p - 1) / 2) (p - 1 - p / 6)).coeff.support) :
    j + 1 ≠ 0 ∧ (j + 1).natAbs < p ^ 2 := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hne := Finsupp.mem_support_iff.mp hj
  have hz : j + 1 ≠ 0 := by
    intro h
    have hj1 : j = -1 := by omega
    rw [hj1, canonicalSource_no_log p hpodd] at hne
    exact hne rfl
  have hw := canonicalSource_bounded p ((p - 1) / 2) (p - 1 - p / 6)
    (by omega) (by omega) (by omega) j hne
  have hlo : -(7 * (p : ℤ)) < j + 1 := by omega
  have hhi : j + 1 < 11 * (p : ℤ) := by omega
  have ha : (j + 1).natAbs < 11 * p := by omega
  exact ⟨hz, ha.trans (by nlinarith)⟩

theorem literal_canonicalPeriod_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (canonicalPeriod p ((p - 1) / 2) (p - 1 - p / 6)) := by
  rw [canonicalPeriod_eq_rationalPrimitive]
  exact rationalPrimitive_integral p (by omega) _
    (canonicalSource_integral p hp)
    (fun j hj => (canonicalSource_primitive_bounds p hp j hj).1)
    (fun j hj => (canonicalSource_primitive_bounds p hp j hj).2)

theorem reduceLaurent_mul_integral (p : ℕ) [Fact p.Prime]
    (P Q : ℚ[T;T⁻¹]) (hP : P ∈ integralLaurent p) (hQ : Q ∈ integralLaurent p) :
    reduceLaurent p (P * Q) = reduceLaurent p P * reduceLaurent p Q := by
  rw [reduceLaurent_eq_residueLaurent p (P * Q) ((integralLaurent p).mul_mem hP hQ),
    reduceLaurent_eq_residueLaurent p P hP, reduceLaurent_eq_residueLaurent p Q hQ]
  exact (residueLaurent p).map_mul ⟨P, hP⟩ ⟨Q, hQ⟩

theorem reduceLaurent_sub_integral (p : ℕ) [Fact p.Prime]
    (P Q : ℚ[T;T⁻¹]) (hP : P ∈ integralLaurent p) (hQ : Q ∈ integralLaurent p) :
    reduceLaurent p (P - Q) = reduceLaurent p P - reduceLaurent p Q := by
  rw [reduceLaurent_eq_residueLaurent p (P - Q) ((integralLaurent p).sub_mem hP hQ),
    reduceLaurent_eq_residueLaurent p P hP, reduceLaurent_eq_residueLaurent p Q hQ]
  exact (residueLaurent p).map_sub ⟨P, hP⟩ ⟨Q, hQ⟩

theorem reduceLaurent_pow_integral (p : ℕ) [Fact p.Prime]
    (P : ℚ[T;T⁻¹]) (hP : P ∈ integralLaurent p) (n : ℕ) :
    reduceLaurent p (P ^ n) = reduceLaurent p P ^ n := by
  rw [reduceLaurent_eq_residueLaurent p (P ^ n) ((integralLaurent p).pow_mem hP n),
    reduceLaurent_eq_residueLaurent p P hP]
  exact (residueLaurent p).map_pow ⟨P, hP⟩ n

theorem reduceLaurent_C_integral (p : ℕ) [Fact p.Prime] (c : ℚ)
    (hc : c ∈ integralRationals p) :
    reduceLaurent p (C c) = C (c : ZMod p) := by
  rw [reduceLaurent_eq_residueLaurent p (C c) (integral_C p c hc),
    residueLaurent_C p ⟨c, hc⟩]

theorem reduceLaurent_T (p : ℕ) [Fact p.Prime] (j : ℤ) :
    reduceLaurent p (T j) = T j := by
  have h : (T j : ℚ[T;T⁻¹]) =
      coefficientMap (integralRationals p).subtype (T j) := by rw [coefficientMap_T]
  rw [h, reduceLaurent_integral_map, coefficientMap_T]

theorem derivative_toLaurent (P : ℚ[X]) :
    derivative (Polynomial.toLaurent P) = Polynomial.toLaurent P.derivative := by
  have hs (Q : ℚ[X]) : substitute Q (T 1) = Polynomial.toLaurent Q := by
    simpa only [Polynomial.toLaurent_X, Polynomial.comp_X, substitute, substituteOver,
      Polynomial.coe_eval₂RingHom] using
      (substituteOver_toLaurent Q Polynomial.X)
  rw [← hs P, derivative_substitute, hs P.derivative]
  have hd : derivative (T (1 : ℤ) : ℚ[T;T⁻¹]) = 1 := by
    simpa using derivative_monomial 1 1
  rw [hd, mul_one]

noncomputable def integralVx (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[T;T⁻¹] := Polynomial.toLaurent (WPHasseIntegralTransport.integralV p hp)

theorem integralVx_map_rational (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    coefficientMap (integralRationals p).subtype (integralVx p hp) = WPActualEtaPole.Vx := by
  rw [integralVx, coefficientMap_toLaurent, WPHasseIntegralTransport.integralV_map_rational]
  rfl

theorem derivativeIntegralVx_map_rational (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    coefficientMap (integralRationals p).subtype
        (Polynomial.toLaurent (WPHasseIntegralTransport.integralV p hp).derivative) =
      derivative WPActualEtaPole.Vx := by
  rw [coefficientMap_toLaurent, ← Polynomial.derivative_map,
    WPHasseIntegralTransport.integralV_map_rational, ← derivative_toLaurent]
  rfl

noncomputable def integralCanonicalDensity (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[T;T⁻¹] :=
  T (-(p : ℤ) - 1) * squareOver
    (C 2 * T 1 * integralVx p hp ^ (p - 1) *
      Polynomial.toLaurent (WPHasseIntegralTransport.integralV p hp).derivative -
        integralVx p hp ^ p)

theorem integralCanonicalDensity_map_rational (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    coefficientMap (integralRationals p).subtype (integralCanonicalDensity p hp) =
      logarithmicSDensity p := by
  rw [integralCanonicalDensity, map_mul, coefficientMap_T, squareOver_map_rational]
  simp only [map_sub, map_mul, map_ofNat, coefficientMap_T,
    map_pow, integralVx_map_rational, derivativeIntegralVx_map_rational]
  have hd : derivative Vpull = C 2 * T 1 * squareX (derivative WPActualEtaPole.Vx) := by
    rw [← squareX_Vx, squareX_derivative]
  have ht : (T (-(p : ℤ)) * T 1 : ℚ[T;T⁻¹]) = T (-(p : ℤ) - 1) * T 2 := by
    rw [← T_add, ← T_add]
    congr 1
    omega
  unfold logarithmicSDensity baseDensity
  rw [hd]
  simp only [squareX_T, squareX_Vx, map_ofNat]
  calc
    _ = 2 * Vpull ^ (p - 1) * squareX (derivative WPActualEtaPole.Vx) *
        (T (-(p : ℤ) - 1) * T 2) - Vpull ^ p * T (-(p : ℤ) - 1) := by ring
    _ = _ := by rw [← ht]; ring

noncomputable def fieldVx (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  Polynomial.toLaurent (WPHasseIntegralTransport.fieldV p)

noncomputable def fieldDerivativeVx (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  Polynomial.toLaurent (WPHasseIntegralTransport.fieldV p).derivative

noncomputable def fieldCanonicalDensity (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  T (-(p : ℤ) - 1) * squareSubstitute p
    (C 2 * T 1 * fieldVx p ^ (p - 1) * fieldDerivativeVx p - fieldVx p ^ p)

theorem integralCanonicalDensity_map_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    coefficientMap (residueHom p) (integralCanonicalDensity p hp) = fieldCanonicalDensity p := by
  rw [integralCanonicalDensity, map_mul, coefficientMap_T, squareOver_map_field]
  simp only [map_sub, map_mul, map_ofNat, coefficientMap_T, map_pow,
    integralVx, coefficientMap_toLaurent, WPHasseIntegralTransport.integralV_map_field,
    ← Polynomial.derivative_map]
  simp only [fieldCanonicalDensity, fieldVx, fieldDerivativeVx, map_sub, map_mul,
    map_pow, map_ofNat]

noncomputable def integralLiteralA (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[T;T⁻¹] :=
  integralLift p ⟨Aeta p ((p - 1) / 2) (p - 1 - p / 6),
    actual_native_cutoff_Aeta_integral p hp⟩

theorem integralLiteralA_map_rational (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (integralRationals p).subtype (integralLiteralA p hp) =
      Aeta p ((p - 1) / 2) (p - 1 - p / 6) := integralLift_rational p _

theorem integralLiteralA_map_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (integralLiteralA p hp) =
      WPActualEtaFieldCutoff.literalFieldAeta p hp := by
  ext j
  rw [coefficientMap_coeff, WPActualEtaFieldCutoff.literalFieldAeta_coeff,
    integralLiteralA, integralLift_coeff]
  rfl

noncomputable def integralLiteralCanonicalSource (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[T;T⁻¹] :=
  integralCanonicalDensity p (by omega) * squareOver (integralLiteralA p hp)

theorem integralLiteralCanonicalSource_map_rational (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (integralRationals p).subtype (integralLiteralCanonicalSource p hp) =
      canonicalSource p ((p - 1) / 2) (p - 1 - p / 6) := by
  rw [integralLiteralCanonicalSource, map_mul, integralCanonicalDensity_map_rational,
    squareOver_map_rational, integralLiteralA_map_rational]
  rfl

/-- The full original density reduces to the actual complete canonical field source. -/
theorem literal_canonicalSource_reduction (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    reduceLaurent p (canonicalSource p ((p - 1) / 2) (p - 1 - p / 6)) =
      fieldCanonicalDensity p *
        squareSubstitute p (WPActualEtaFieldCutoff.literalFieldAeta p hp) := by
  rw [← integralLiteralCanonicalSource_map_rational p hp, reduceLaurent_integral_map,
    integralLiteralCanonicalSource, map_mul, integralCanonicalDensity_map_field,
    squareOver_map_field, integralLiteralA_map_field]

theorem literal_canonicalPeriod_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (canonicalPeriod p ((p - 1) / 2) (p - 1 - p / 6) : ZMod p) =
      fieldPrimitive p (WPFiniteCartier.cartier p (Fact.out : p.Prime).pos
        (fieldCanonicalDensity p *
          squareSubstitute p (WPActualEtaFieldCutoff.literalFieldAeta p hp))) := by
  rw [canonicalPeriod_eq_rationalPrimitive,
    rationalPrimitive_residue_cartier p (by omega) _ (canonicalSource_integral p hp)
      (fun j hj => (canonicalSource_primitive_bounds p hp j hj).1)
      (fun j hj => (canonicalSource_primitive_bounds p hp j hj).2),
    literal_canonicalSource_reduction p hp]

end WPActualCanonicalSource
