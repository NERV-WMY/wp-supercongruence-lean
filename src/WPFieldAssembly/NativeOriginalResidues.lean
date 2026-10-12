import WPFieldAssembly.NativeIR28
import WPFieldAssembly.ActualNC77Chart
import WPFieldAssembly.OriginalLaurentDensity

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial WPPIntegralReduction
  WPActualRankTwoParameter WPActualRankTwoLegendreField
  WPActualRankTwoResidueSource WPActualResidueVanishing
  WPActualPullbackSource WPActualEtaPole WPActualEtaSupport
  WPActualEtaPrimitive WPActualPositiveResidueSource
  WPActualCentralResidueSource
  WPFieldAssembly.NativeQuadraticInverse
  WPFieldAssembly.ActualNC77Chart
  WPFieldAssembly.NativeFullGreen WPFieldAssembly.NativeStrictTail
  WPFieldAssembly.NativeIR28 WPFieldAssembly.ResidualProjection
  WPFieldAssembly.OriginalLaurentDensity
  WPMomentPrecision.NativeSecondLift

namespace WPFieldAssembly.NativeOriginalResidues

set_option maxHeartbeats 1200000

private theorem field_prime_zero (p : ℕ) : (p : (ZMod p)[X]) = 0 := by
  change C (p : ZMod p) = 0
  rw [ZMod.natCast_self, C_0]

variable (p : ℕ) [Fact p.Prime]

theorem divX_map_local {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (G : R[X]) : G.divX.map f = (G.map f).divX := by
  ext n
  simp only [coeff_map, coeff_divX]

theorem quadraticInverse_add_local {R : Type*} [CommRing R] (A B : R[X]) :
    quadraticInverse (A + B) = quadraticInverse A + quadraticInverse B := by
  have hc : contract 2 (A + B) = contract 2 A + contract 2 B := by
    ext n
    simp only [coeff_contract (by norm_num : (2 : ℕ) ≠ 0), coeff_add]
  unfold quadraticInverse
  rw [hc, add_comp]

theorem quadraticInverse_sub_local {R : Type*} [CommRing R] (A B : R[X]) :
    quadraticInverse (A - B) = quadraticInverse A - quadraticInverse B := by
  have hc : contract 2 (A - B) = contract 2 A - contract 2 B := by
    ext n
    simp only [coeff_contract (by norm_num : (2 : ℕ) ≠ 0), coeff_sub]
  unfold quadraticInverse
  rw [hc, sub_comp]

theorem quadraticInverse_nat_mul_local {R : Type*} [CommRing R]
    (n : ℕ) (A : R[X]) :
    quadraticInverse ((n : R[X]) * A) = (n : R[X]) * quadraticInverse A := by
  rw [show (n : R[X]) = C (n : R) by simp, quadraticInverse_C_mul]

theorem Ij_sub_local {K : Type*} [Field K] (p j : ℕ) (A B : K[X]) :
    Ij p j (A - B) = Ij p j A - Ij p j B := by
  rw [sub_eq_add_neg, show -B = C (-1 : K) * B by simp,
    Ij_add, Ij_C_mul]
  ring

theorem Ij_nat_mul_local {K : Type*} [Field K]
    (p j n : ℕ) (A : K[X]) :
    Ij p j ((n : K[X]) * A) = (n : K) * Ij p j A := by
  rw [show (n : K[X]) = C (n : K) by simp, Ij_C_mul]

/-- The density is formed in Z_(p)[X] before either coefficient map. -/
noncomputable def inverse125 (hp : 19 ≤ p) : integralRationals p :=
  ⟨1 / 125, by
    have h5 : (1 / 5 : ℚ) ∈ integralRationals p :=
      WPFiniteConductorPolynomial.small_inverse_integral p 5 (by norm_num) (by omega)
    have h := (integralRationals p).pow_mem h5 3
    (convert h using 1; norm_num)⟩

theorem inverse125_value (hp : 19 ≤ p) :
    (inverse125 p hp).val = (1 / 125 : ℚ) := rfl

theorem inverse125_field (hp : 19 ≤ p) :
    residueHom p (inverse125 p hp) = (1 / 125 : ZMod p) := by
  have h5 : (5 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h125 : (125 : ZMod p) ≠ 0 := by
    rw [show (125 : ZMod p) = 5 ^ 3 by ring]
    exact pow_ne_zero _ h5
  have hu : (125 : integralRationals p) * inverse125 p hp = 1 := by
    apply Subtype.ext
    change (125 : ℚ) * (1 / 125) = 1
    norm_num
  have hf : (125 : ZMod p) * residueHom p (inverse125 p hp) = 1 := by
    simpa only [_root_.map_mul, _root_.map_ofNat, _root_.map_one] using congrArg (residueHom p) hu
  apply (eq_div_iff h125).mpr
  simpa only [mul_comm] using hf

noncomputable def QrevIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  C (4 * inverse125 p hp) - C (33 * inverse125 p hp) * X +
    C (72 * inverse125 p hp) * X ^ 2 - C (16 * inverse125 p hp) * X ^ 3

noncomputable def FrevIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  C (132 * inverse125 p hp) * X ^ 3 -
    C (81 * inverse125 p hp) * X ^ 2 + C (12 * inverse125 p hp) * X

theorem QrevIntegral_value (hp : 19 ≤ p) :
    (QrevIntegral p hp).map (integralRationals p).subtype =
      (WPFiniteNC122Residue.Qrev : ℚ[X]) := by
  norm_num [QrevIntegral, inverse125, WPFiniteNC122Residue.Qrev]
  norm_num only [← C_mul]
  congr 5 <;> first
    | decide +kernel
    | (change (33 : ℚ) * _ = _; decide +kernel)

theorem FrevIntegral_value (hp : 19 ≤ p) :
    (FrevIntegral p hp).map (integralRationals p).subtype =
      (WPFiniteNC122Residue.Frev : ℚ[X]) := by
  norm_num [FrevIntegral, inverse125, WPFiniteNC122Residue.Frev]
  norm_num only [← C_mul]
  congr 5 <;> decide +kernel

theorem QrevIntegral_field (hp : 19 ≤ p) :
    (QrevIntegral p hp).map (residueHom p) =
      (WPFiniteNC122Residue.Qrev : (ZMod p)[X]) := by
  simp only [QrevIntegral, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow,
    Polynomial.map_ofNat, _root_.map_mul, _root_.map_ofNat, inverse125_field,
    WPFiniteNC122Residue.Qrev, div_eq_mul_inv, one_mul]

theorem FrevIntegral_field (hp : 19 ≤ p) :
    (FrevIntegral p hp).map (residueHom p) =
      (WPFiniteNC122Residue.Frev : (ZMod p)[X]) := by
  simp only [FrevIntegral, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow,
    Polynomial.map_ofNat, _root_.map_mul, _root_.map_ofNat, inverse125_field,
    WPFiniteNC122Residue.Frev, div_eq_mul_inv, one_mul]

noncomputable def densityIntegral (hp : 19 ≤ p)
    (G : (integralRationals p)[X]) : (integralRationals p)[X] :=
  G.divX.comp (QrevIntegral p hp) * FrevIntegral p hp

theorem densityIntegral_value (hp : 19 ≤ p) (G : (integralRationals p)[X]) :
    (densityIntegral p hp G).map (integralRationals p).subtype =
      WPFiniteNC122Residue.canceledDensity (G.map (integralRationals p).subtype) := by
  rw [densityIntegral, Polynomial.map_mul, Polynomial.map_comp,
    divX_map_local, QrevIntegral_value, FrevIntegral_value]
  rfl

theorem densityIntegral_field (hp : 19 ≤ p) (G : (integralRationals p)[X]) :
    (densityIntegral p hp G).map (residueHom p) =
      WPFiniteNC122Residue.canceledDensity (G.map (residueHom p)) := by
  rw [densityIntegral, Polynomial.map_mul, Polynomial.map_comp,
    divX_map_local, QrevIntegral_field, FrevIntegral_field]
  rfl

noncomputable def projectionIntegral (hp : 19 ≤ p) (j : ℕ)
    (G : (integralRationals p)[X]) : integralRationals p :=
  (densityIntegral p hp G).coeff ((p - 1) / 2 + j * p + 1)

theorem projectionIntegral_value (hp : 19 ≤ p) (j : ℕ)
    (G : (integralRationals p)[X]) :
    (projectionIntegral p hp j G).val = Ij p j (G.map (integralRationals p).subtype) := by
  rw [Ij, ← densityIntegral_value, coeff_map]
  rfl

theorem projectionIntegral_field (hp : 19 ≤ p) (j : ℕ)
    (G : (integralRationals p)[X]) :
    residueHom p (projectionIntegral p hp j G) = Ij p j (G.map (residueHom p)) := by
  rw [Ij, ← densityIntegral_field, coeff_map]
  rfl

theorem original_projection_integral (hp : 19 ≤ p) (j : ℕ)
    (G : (integralRationals p)[X]) :
    O p j (G.map (integralRationals p).subtype) ∈ integralRationals p := by
  rw [O_eq_Ij, ← projectionIntegral_value]
  exact (projectionIntegral p hp j G).property

theorem original_projection_field (hp : 19 ≤ p) (j : ℕ)
    (G : (integralRationals p)[X]) :
    (O p j (G.map (integralRationals p).subtype) : ZMod p) =
      Ij p j (G.map (residueHom p)) := by
  rw [O_eq_Ij, ← projectionIntegral_value]
  change residueHom p (projectionIntegral p hp j G) = _
  exact projectionIntegral_field p hp j G

theorem actual_U_models_equal (hp : 19 ≤ p) :
    nativeTwoNodeU p = actualU p := by
  rw [nativeTwoNodeU_eq p hp]
  rfl

theorem actual_integral_U_models_equal (hp : 19 ≤ p) :
    nativeUIntegral p hp = integralU p (by omega) := by
  apply Polynomial.map_injective (integralRationals p).subtype
    (Subring.subtype_injective (integralRationals p))
  rw [nativeUIntegral_value, integralU_value, actual_U_models_equal p hp]

/-- The two concrete full second corrections differ by the actual cubic remainder. -/
theorem actual_full_correction_cubic_comparison (hp : 19 ≤ p) :
    ∃ E : (integralRationals p)[X],
      nativeSecondCorrectionFullIntegral p hp =
        integralActualSecondCorrection p hp + C (p : integralRationals p) * E := by
  obtain ⟨E, hE⟩ := actual_full_integral_second_correction p hp
  have hd := Nat.div_mul_le_self p 6
  have hcut : fullCutoff p + 1 = p - p / 6 := by
    dsimp [fullCutoff]
    omega
  have hF : fullNativeJacobi p = rankJacobiNode p 1 ^ 2 +
      C (2 * (p : ℚ)) * rankJacobiNode p 1 * actualU p +
      C ((p : ℚ) ^ 2) *
        (integralActualSecondCorrection p hp).map (integralRationals p).subtype +
      C ((p : ℚ) ^ 3) * E.map (integralRationals p).subtype := by
    simpa only [fullNativeJacobi, hcut] using hE
  have hpq : (p : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hunit : C ((p : ℚ) ^ 2) * C (1 / (p : ℚ) ^ 2) = (1 : ℚ[X]) := by
    rw [← C_mul]
    have he : (p : ℚ) ^ 2 * (1 / (p : ℚ) ^ 2) = 1 := by field_simp [hpq]
    rw [he, C_1]
  have hc : C ((p : ℚ) ^ 2) *
      (nativeSecondCorrectionFullIntegral p hp).map (integralRationals p).subtype =
      fullNativeJacobi p - rankJacobiNode p 1 ^ 2 -
        2 * C (p : ℚ) * rankJacobiNode p 1 * actualU p := by
    rw [nativeSecondCorrectionFullIntegral_value, actual_U_models_equal p hp,
      ← mul_assoc, hunit, one_mul]
  have hRat : (nativeSecondCorrectionFullIntegral p hp).map
        (integralRationals p).subtype =
      (integralActualSecondCorrection p hp).map (integralRationals p).subtype +
        C (p : ℚ) * E.map (integralRationals p).subtype := by
    apply mul_left_cancel₀ (C_ne_zero.mpr (pow_ne_zero 2 hpq))
    rw [hc, hF]
    simp only [_root_.map_mul, _root_.map_pow, _root_.map_ofNat]
    ring
  refine ⟨E, ?_⟩
  apply Polynomial.map_injective (integralRationals p).subtype
    (Subring.subtype_injective (integralRationals p))
  simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    _root_.map_natCast, Polynomial.map_natCast] using hRat

theorem actual_full_correction_field_comparison (hp : 19 ≤ p) :
    (nativeSecondCorrectionFullIntegral p hp).map (residueHom p) =
      (integralActualSecondCorrection p hp).map (residueHom p) := by
  obtain ⟨E, hE⟩ := actual_full_correction_cubic_comparison p hp
  rw [hE]
  simp only [Polynomial.map_add, Polynomial.map_mul,
    _root_.map_natCast, Polynomial.map_natCast, field_prime_zero, zero_mul, add_zero]

noncomputable def fullCqIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  quadraticInverse (nativeSecondCorrectionFullIntegral p hp)

noncomputable def halfCqIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  quadraticInverse (nativeSecondCorrectionHalfIntegral p hp)

noncomputable def secondCqIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  quadraticInverse (integralActualSecondCorrection p hp)

noncomputable def fullCq (hp : 19 ≤ p) : ℚ[X] :=
  (fullCqIntegral p hp).map (integralRationals p).subtype

noncomputable def secondCq : ℚ[X] := quadraticInverse (actualSecondCorrection p)

theorem secondCqIntegral_value (hp : 19 ≤ p) :
    (secondCqIntegral p hp).map (integralRationals p).subtype = secondCq p := by
  rw [secondCqIntegral, quadraticInverse_map, integralActualSecondCorrection_value]
  rfl

theorem fullCqIntegral_field_comparison (hp : 19 ≤ p) :
    (fullCqIntegral p hp).map (residueHom p) =
      (secondCqIntegral p hp).map (residueHom p) := by
  rw [fullCqIntegral, secondCqIntegral, quadraticInverse_map,
    quadraticInverse_map, actual_full_correction_field_comparison p hp]

/-- The reviewed full q-native witness is attached to the concrete original correction. -/
theorem actual_full_original_q_low (hp : 19 ≤ p) :
    ((fullCqIntegral p hp - 6 * integralNormQ p (by omega)).map
      (residueHom p)).natDegree ≤ p / 6 ∧
    ((fullCqIntegral p hp - 6 * integralNormQ p (by omega)).map
      (residueHom p)).eval 0 = 0 := by
  have htransport : quadraticInverse (nativeIR28DifferenceFull p hp) =
      (fullCqIntegral p hp - 6 * integralNormQ p (by omega)).map (residueHom p) := by
    rw [nativeIR28DifferenceFull, ← quadraticInverse_map]
    congr 1
    rw [quadraticInverse_sub_local]
    have h6 := quadraticInverse_nat_mul_local 6 (nativeMixedSquareIntegral p hp)
    norm_num only [Nat.cast_ofNat] at h6
    rw [h6, nativeMixedSquareIntegral, actual_integral_U_models_equal p hp]
    rfl
  obtain ⟨l, hdegree, horigin, hsource⟩ := actual_native_IR28_full_q_witness p hp
  rw [hsource, quadraticInverse_quadratic] at htransport
  rw [← htransport]
  exact ⟨hdegree, horigin⟩

theorem halfCqIntegral_field_source (hp : 19 ≤ p) :
    (halfCqIntegral p hp).map (residueHom p) =
      (fullCqIntegral p hp).map (residueHom p) - quadraticInverse (BtailField p hp) := by
  simp only [halfCqIntegral, nativeSecondCorrectionHalfIntegral,
    quadraticInverse_sub_local, Polynomial.map_sub, fullCqIntegral,
    quadraticInverse_map]
  rfl

/-- Every original negative projection of the full low correction vanishes. -/
theorem actual_full_projection_drop (hp : 19 ≤ p) (j : ℕ) :
    Ij p j ((fullCqIntegral p hp).map (residueHom p)) =
      6 * Ij p j ((integralNormQ p (by omega)).map (residueHom p)) := by
  have hz := low_correction_both_projections_zero p hp
    ((fullCqIntegral p hp - 6 * integralNormQ p (by omega)).map (residueHom p))
    (actual_full_original_q_low p hp).1 j
  rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat,
    Ij_sub_local] at hz
  have h6 := Ij_nat_mul_local p j 6
    ((integralNormQ p (by omega)).map (residueHom p))
  norm_num only [Nat.cast_ofNat] at h6
  rw [h6] at hz
  exact sub_eq_zero.mp hz

theorem actual_original_full_projection_drop (hp : 19 ≤ p) (j : ℕ) :
    (O p j (fullCq p hp) : ZMod p) = 6 * (O p j (normQ p) : ZMod p) := by
  have hc := original_projection_field p hp j (fullCqIntegral p hp)
  change (O p j (fullCq p hp) : ZMod p) = _ at hc
  have hn := original_projection_field p hp j (integralNormQ p (by omega))
  rw [integralNormQ_value] at hn
  rw [hc, hn, actual_full_projection_drop p hp j]

/-- Moment's actual secondCorrection inherits the same full-cutoff drop. -/
theorem actual_original_second_projection_drop (hp : 19 ≤ p) (j : ℕ) :
    (O p j (secondCq p) : ZMod p) = 6 * (O p j (normQ p) : ZMod p) := by
  have hc := original_projection_field p hp j (secondCqIntegral p hp)
  rw [secondCqIntegral_value] at hc
  have hn := original_projection_field p hp j (integralNormQ p (by omega))
  rw [integralNormQ_value] at hn
  rw [hc, hn, ← fullCqIntegral_field_comparison p hp,
    actual_full_projection_drop p hp j]

/-- The half correction still carries the entire nonconstant strict upper tail. -/
theorem actual_half_projection_source (hp : 19 ≤ p) (j : ℕ) :
    Ij p j ((halfCqIntegral p hp).map (residueHom p)) =
      6 * Ij p j ((integralNormQ p (by omega)).map (residueHom p)) -
        Ij p j (quadraticInverse (BtailField p hp)) := by
  rw [halfCqIntegral_field_source, Ij_sub_local, actual_full_projection_drop p hp j]

noncomputable def originalNorm : ℚ :=
  12 * O p 0 (normQ p) + (15 / 2 : ℚ) * O p 1 (normQ p)

noncomputable def originalNormIntegral (hp : 19 ≤ p) : integralRationals p :=
  12 * projectionIntegral p hp 0 (integralNormQ p (by omega)) +
    (15 * integralHalf p (by omega)) *
      projectionIntegral p hp 1 (integralNormQ p (by omega))

theorem originalNormIntegral_value (hp : 19 ≤ p) :
    (originalNormIntegral p hp).val = originalNorm p := by
  have h0 : (projectionIntegral p hp 0 (integralNormQ p (by omega))).val =
      O p 0 (normQ p) := by
    rw [projectionIntegral_value, integralNormQ_value, O_eq_Ij]
  have h1 : (projectionIntegral p hp 1 (integralNormQ p (by omega))).val =
      O p 1 (normQ p) := by
    rw [projectionIntegral_value, integralNormQ_value, O_eq_Ij]
  change 12 * (projectionIntegral p hp 0 (integralNormQ p (by omega))).val +
    (15 * (1 / 2 : ℚ)) *
      (projectionIntegral p hp 1 (integralNormQ p (by omega))).val = _
  rw [h0, h1, originalNorm]
  ring

theorem original_norm_integral (hp : 19 ≤ p) :
    originalNorm p ∈ integralRationals p := by
  rw [← originalNormIntegral_value p hp]
  exact (originalNormIntegral p hp).property

/-- Neither of the two quadratic norm projections is removed. -/
theorem original_norm_field (hp : 19 ≤ p) :
    (originalNorm p : ZMod p) =
      12 * Ij p 0 ((integralNormQ p (by omega)).map (residueHom p)) +
        (15 / 2 : ZMod p) *
          Ij p 1 ((integralNormQ p (by omega)).map (residueHom p)) := by
  rw [← originalNormIntegral_value p hp]
  change residueHom p (originalNormIntegral p hp) = _
  simp only [originalNormIntegral, _root_.map_add, _root_.map_mul, _root_.map_ofNat,
    integralHalf_field, projectionIntegral_field]
  ring

theorem original_norm_actual_source (hp : 19 ≤ p) :
    (originalNorm p : ZMod p) =
      12 * Ij p 0 (quadraticInverse
        ((C (1 / 6 : ZMod p) * actualRankDividedField p (by omega)) ^ 2)) +
      (15 / 2 : ZMod p) * Ij p 1 (quadraticInverse
        ((C (1 / 6 : ZMod p) * actualRankDividedField p (by omega)) ^ 2)) := by
  rw [original_norm_field p hp, actual_norm_field_source p (by omega : 7 ≤ p)]

theorem quadraticInverse_degree_of_le {R : Type*} [CommRing R]
    (G : R[X]) (D : ℕ) (hG : G.natDegree ≤ 2 * D) :
    (quadraticInverse G).natDegree ≤ D := by
  have hc : (contract 2 G).natDegree ≤ D := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
    apply coeff_eq_zero_of_natDegree_lt
    omega
  have hlinear : (1 - X : R[X]).natDegree ≤ 1 := by
    simpa using natDegree_sub_le_of_le
      (show (1 : R[X]).natDegree ≤ 0 by simp) (natDegree_X_le (R := R))
  unfold quadraticInverse
  exact natDegree_comp_le.trans
    ((Nat.mul_le_mul hc hlinear).trans (by simp))

noncomputable def squareQ : ℚ[X] := quadraticInverse (rankJacobiNode p 1 ^ 2)

noncomputable def squareQIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  quadraticInverse (rankIntegralJacobi p (by omega) 1 ^ 2)

theorem squareQIntegral_value (hp : 19 ≤ p) :
    (squareQIntegral p hp).map (integralRationals p).subtype = squareQ p := by
  rw [squareQIntegral, quadraticInverse_map, Polynomial.map_pow,
    rankIntegralJacobi_value]
  rfl

theorem actual_squareQ_degree (hp : 19 ≤ p) : (squareQ p).natDegree ≤ p / 6 := by
  apply quadraticInverse_degree_of_le
  simpa only [pow_two, two_mul] using natDegree_mul_le_of_le
    (actual_low_rankJacobi_degree p (by omega))
    (actual_low_rankJacobi_degree p (by omega))

theorem actual_mixedQ_degree (hp : 19 ≤ p) :
    (mixedQ p).natDegree ≤ (p - 1) / 2 := by
  apply quadraticInverse_degree_of_le
  have hprod := natDegree_mul_le_of_le
    (actual_low_rankJacobi_degree p (by omega)) (actual_U_degree p)
  have h6 := Nat.div_mul_le_self p 6
  have hhalf := WPFiniteWSource.half_exponent p hp
  exact hprod.trans (by omega)

/-- The exact full native polynomial has its literal Q-divided correction. -/
theorem actual_full_native_q_source (hp : 19 ≤ p) :
    WPReview.nativePolynomial (fullCutoff p + 1) =
      squareQ p + C (2 * (p : ℚ)) * mixedQ p + C ((p : ℚ) ^ 2) * fullCq p hp := by
  have hpq : (p : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hunit : C ((p : ℚ) ^ 2) * C (1 / (p : ℚ) ^ 2) = (1 : ℚ[X]) := by
    rw [← C_mul]
    have he : (p : ℚ) ^ 2 * (1 / (p : ℚ) ^ 2) = 1 := by field_simp [hpq]
    rw [he, C_1]
  have hc := congrArg (fun G : ℚ[X] => C ((p : ℚ) ^ 2) * G)
    (nativeSecondCorrectionFullIntegral_value p hp)
  rw [actual_U_models_equal p hp, ← mul_assoc, hunit, one_mul] at hc
  have hF : fullNativeJacobi p = rankJacobiNode p 1 ^ 2 +
      C (2 * (p : ℚ)) * (rankJacobiNode p 1 * actualU p) +
      C ((p : ℚ) ^ 2) *
        (nativeSecondCorrectionFullIntegral p hp).map (integralRationals p).subtype := by
    simp only [_root_.map_mul, _root_.map_ofNat]
    linear_combination -hc
  have h := congrArg (fun G : ℚ[X] => quadraticInverse G) hF
  rw [fullNativeJacobi, quadraticInverse_quadratic,
    quadraticInverse_add_local, quadraticInverse_add_local,
    quadraticInverse_C_mul, quadraticInverse_C_mul] at h
  simpa only [squareQ, mixedQ, fullCq, fullCqIntegral, quadraticInverse_map] using h

/-- Needed for the ordinary unit-index primitive of the full correction. -/
theorem actual_fullCq_degree (hp : 19 ≤ p) :
    (fullCq p hp).natDegree ≤ fullCutoff p := by
  let e := fullCutoff p
  have h6 := Nat.div_mul_le_self p 6
  have hde : p / 6 ≤ e := by dsimp [e, fullCutoff]; omega
  have hF : (fullNativeJacobi p).natDegree ≤ 2 * e := by
    unfold fullNativeJacobi
    exact natDegree_comp_le.trans
      ((Nat.mul_le_mul
        (le_of_eq (WPFieldAssembly.NativePrecision.rational_native_degree e))
        (le_of_eq WPFieldAssembly.NativePrecision.quadratic_degree)).trans (by omega))
  have hY : (rankJacobiNode p 1 ^ 2).natDegree ≤ 2 * e := by
    have h := natDegree_mul_le_of_le
      (actual_low_rankJacobi_degree p (by omega))
      (actual_low_rankJacobi_degree p (by omega))
    simpa only [pow_two] using h.trans (by omega)
  have hYU : (rankJacobiNode p 1 * actualU p).natDegree ≤ 2 * e := by
    have h := natDegree_mul_le_of_le
      (actual_low_rankJacobi_degree p (by omega)) (actual_U_degree p)
    exact h.trans (by dsimp [e, fullCutoff] at *; omega)
  have hscaled : (2 * C (p : ℚ) * rankJacobiNode p 1 * actualU p).natDegree ≤ 2 * e := by
    have he : 2 * C (p : ℚ) * rankJacobiNode p 1 * actualU p =
        C (2 * (p : ℚ)) * (rankJacobiNode p 1 * actualU p) := by
      simp only [_root_.map_mul, _root_.map_ofNat]
      ring
    rw [he]
    exact (natDegree_C_mul_le _ _).trans hYU
  have hwhole : (fullNativeJacobi p - rankJacobiNode p 1 ^ 2 -
      2 * C (p : ℚ) * rankJacobiNode p 1 * actualU p).natDegree ≤ 2 * e := by
    have hfirst : (fullNativeJacobi p - rankJacobiNode p 1 ^ 2).natDegree ≤ 2 * e := by
      simpa only [max_self] using natDegree_sub_le_of_le hF hY
    simpa only [max_self] using natDegree_sub_le_of_le hfirst hscaled
  have hS : ((nativeSecondCorrectionFullIntegral p hp).map
      (integralRationals p).subtype).natDegree ≤ 2 * e := by
    rw [nativeSecondCorrectionFullIntegral_value, actual_U_models_equal p hp]
    exact (natDegree_C_mul_le _ _).trans hwhole
  rw [fullCq, fullCqIntegral, quadraticInverse_map]
  exact quadraticInverse_degree_of_le _ e hS

theorem actual_squareQ_projection_zero (hp : 19 ≤ p) (j : ℕ) :
    Ij p j (squareQ p) = 0 :=
  low_correction_both_projections_zero p hp _ (actual_squareQ_degree p hp) j

theorem actual_mixedQ_later_projection_zero (hp : 19 ≤ p) (j : ℕ) (hj : 1 ≤ j) :
    Ij p j (mixedQ p) = 0 := by
  unfold Ij
  apply coeff_eq_zero_of_natDegree_lt
  have hdegree := canceledDensity_degree_le (mixedQ p) ((p - 1) / 2)
    (by omega) (actual_mixedQ_degree p hp)
  have hhalf := Nat.div_mul_le_self (p - 1) 2
  have hjp : p ≤ j * p := by
    simpa using Nat.mul_le_mul_right p hj
  omega

theorem actual_full_native_projection (hp : 19 ≤ p) (j : ℕ) :
    Ij p j (WPReview.nativePolynomial (fullCutoff p + 1)) =
      2 * (p : ℚ) * Ij p j (mixedQ p) +
        (p : ℚ) ^ 2 * Ij p j (fullCq p hp) := by
  rw [actual_full_native_q_source p hp, Ij_add, Ij_add, Ij_C_mul, Ij_C_mul,
    actual_squareQ_projection_zero p hp j, zero_add]

theorem actual_full_native_later_projection (hp : 19 ≤ p)
    (j : ℕ) (hj : 1 ≤ j) :
    Ij p j (WPReview.nativePolynomial (fullCutoff p + 1)) =
      (p : ℚ) ^ 2 * Ij p j (fullCq p hp) := by
  rw [actual_full_native_projection p hp, actual_mixedQ_later_projection_zero p hp j hj,
    mul_zero, zero_add]

open LaurentPolynomial WPFiniteLaurentIntegral WPLaurentIntegralResidue

/-- The entire positive second primitive has ordinary nonnegative support. -/
theorem actual_GX_bounded_local (e : ℕ) : bounded (GX e) 0 (3 * (e : ℤ)) := by
  unfold GX
  apply bounded_sum
  intro n hn
  have hne := Finset.mem_range.mp hn
  exact bounded_mono (bounded_mul (bounded_C _) (bounded_pow Vx_bounded n))
    (by omega) (by omega)

theorem actual_HX_negative_local (e : ℕ) (k : ℤ) (hk : k < 0) :
    (HX e).coeff k = 0 := by
  by_contra hc
  have h := (actual_HV_bounded e k hc).1
  omega

theorem actual_GX_negative_local (e : ℕ) (k : ℤ) (hk : k < 0) :
    (GX e).coeff k = 0 := by
  by_contra hc
  have h := (actual_GX_bounded_local e k hc).1
  omega

omit [Fact p.Prime] in
/-- Original negative resonance, before either rational division or reduction. -/
theorem actual_original_negative_residue [Fact p.Prime] (e j : ℕ)
    (hp : 0 < p) (hj : 1 ≤ j) :
    actualResidue p ((p - 1) / 2) e (-(j : ℤ)) =
      -(1 / (p : ℚ)) * O p j (WPReview.nativePolynomial (e + 1)) := by
  have hjz : 0 < (j : ℤ) := by exact_mod_cast hj
  have hpz : 0 < (p : ℤ) := by exact_mod_cast hp
  have hneg : -(j : ℤ) * (p : ℤ) < 0 := by
    have h := mul_pos hjz hpz
    nlinarith
  have hH := actual_HX_negative_local e (-(j : ℤ) * p) hneg
  have hG := actual_GX_negative_local e (-(j : ℤ) * p) hneg
  rw [actualResidue, actual_Peta_positive_decomposition]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, constant_mul_coefficient,
    finite_derivative_coeff, monomial_shift_coefficient]
  rw [show -(j : ℤ) * p - 1 + 1 = -(j : ℤ) * p by omega,
    show -(j : ℤ) * p - 1 - -1 = -(j : ℤ) * p by omega, hH, hG]
  simp only [mul_zero, add_zero, zero_sub, sub_zero]
  simp only [O, Fpull]
  ring

/-- The negative digit is divided in Q at the actual e cutoff. -/
theorem actual_negative_digit_full_projection (hp : 19 ≤ p) :
    actualNegativeDigit p = -O p 1 (fullCq p hp) := by
  have hpq : (p : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [actualNegativeDigit]
  change actualResidue p ((p - 1) / 2) (fullCutoff p) (-1) / (p : ℚ) = _
  have hr := actual_original_negative_residue p (fullCutoff p) 1
    (Fact.out : p.Prime).pos (by norm_num)
  norm_num only [Nat.cast_one] at hr
  rw [hr, O_eq_Ij, actual_full_native_later_projection p hp 1 (by norm_num), O_eq_Ij]
  field_simp [hpq]

/-- Actual IR29b; the full strict tail has been retained until the full drop theorem. -/
theorem actual_negative_digit_norm_source (hp : 19 ≤ p) :
    (actualNegativeDigit p : ZMod p) = -6 * (O p 1 (normQ p) : ZMod p) := by
  rw [actual_negative_digit_full_projection p hp, Rat.cast_neg,
    actual_original_full_projection_drop p hp 1]
  ring

theorem integralNegativeDigit_norm_source (hp : 19 ≤ p) :
    residueHom p (integralNegativeDigit p hp) =
      -6 * Ij p 1 ((integralNormQ p (by omega)).map (residueHom p)) := by
  change (actualNegativeDigit p : ZMod p) = _
  rw [actual_negative_digit_norm_source p hp]
  have hn := original_projection_field p hp 1 (integralNormQ p (by omega))
  rw [integralNormQ_value] at hn
  rw [hn]

end WPFieldAssembly.NativeOriginalResidues
