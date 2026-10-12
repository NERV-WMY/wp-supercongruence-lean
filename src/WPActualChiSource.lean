import WPActualHasseReciprocal
import WPActualEtaPole

open scoped Polynomial LaurentPolynomial
open LaurentPolynomial WPActualNativeHasse WPHasseIntegralTransport WPActualHasseReciprocal
  WPActualPullbackSource WPActualEtaPole WPPIntegralReduction

namespace WPActualChiSource

noncomputable def coefficientMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : R[T;T⁻¹] →+* S[T;T⁻¹] := AddMonoidAlgebra.mapRingHom ℤ f

theorem coefficientMap_coeff {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : R[T;T⁻¹]) (j : ℤ) :
    (coefficientMap f P).coeff j = f (P.coeff j) :=
  AddMonoidAlgebra.coeff_mapRingHom f P j

theorem coefficientMap_monomial {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c : R) (j : ℤ) :
    coefficientMap f (C c * T j) = C (f c) * T j := by
  simp only [← single_eq_C_mul_T, coefficientMap, AddMonoidAlgebra.mapRingHom_single]

theorem coefficientMap_C {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c : R) : coefficientMap f (C c) = C (f c) := by
  simpa using coefficientMap_monomial f c 0

theorem coefficientMap_T {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (j : ℤ) : coefficientMap f (T j) = T j := by
  simpa using coefficientMap_monomial f 1 j

theorem coefficientMap_invert {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : R[T;T⁻¹]) :
    coefficientMap f (invert P) = invert (coefficientMap f P) := by
  ext j
  simp only [coefficientMap_coeff, invert_apply]

theorem coefficientMap_toLaurent {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : Polynomial R) :
    coefficientMap f (Polynomial.toLaurent P) = Polynomial.toLaurent (P.map f) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, Polynomial.map_add, map_add]
  | monomial n c =>
    rw [Polynomial.toLaurent_C_mul_T, coefficientMap_monomial, Polynomial.map_monomial,
      Polynomial.toLaurent_C_mul_T]

noncomputable def substituteOver {R : Type*} [CommRing R]
    (P : Polynomial R) (L : R[T;T⁻¹]) : R[T;T⁻¹] := P.eval₂ C L

theorem substituteOver_toLaurent {R : Type*} [CommRing R] (P V : Polynomial R) :
    substituteOver P (Polynomial.toLaurent V) = Polynomial.toLaurent (P.comp V) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [substituteOver, Polynomial.eval₂_add, Polynomial.add_comp, map_add] at *
    rw [hP, hQ]
  | monomial n c =>
    simp only [substituteOver, Polynomial.eval₂_monomial, Polynomial.monomial_comp,
      map_mul, map_pow, Polynomial.toLaurent_C]

theorem substituteOver_invert {R : Type*} [CommRing R]
    (P : Polynomial R) (L : R[T;T⁻¹]) :
    invert (substituteOver P L) = substituteOver P (invert L) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [substituteOver, Polynomial.eval₂_add, map_add] at *
    rw [hP, hQ]
  | monomial n c =>
    simp only [substituteOver, Polynomial.eval₂_monomial, map_mul, map_pow, invert_C]

/-- Original Q is exactly the reciprocal of V, including its entire negative-power support. -/
theorem actual_Vx_reciprocal : invert Vx = Qx := by
  simp only [Vx, Vpolynomial, map_mul, map_pow, map_sub, map_ofNat, map_one,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X, invert_C, invert_T]
  have hT : (T (1 : ℤ) : ℚ[T;T⁻¹]) * T (-1) = 1 := by
    rw [← T_add]; norm_num
  have hfirst : (4 * T (-1) - 1 : ℚ[T;T⁻¹]) = (4 - T 1) * T (-1) := by
    rw [sub_mul, hT]
  have hsecond : (4 - T (-1) : ℚ[T;T⁻¹]) = (4 * T 1 - 1) * T (-1) := by
    rw [sub_mul, mul_assoc, hT, mul_one, one_mul]
  rw [hfirst, hsecond]
  have hp : (T (-1) : ℚ[T;T⁻¹]) ^ 3 = T (-3) := by rw [T_pow]; norm_num
  unfold Qx
  calc
    _ = (C (1 / 125 : ℚ) * (4 * T 1 - 1) * (4 - T 1) ^ 2 * T (-1) ^ 3 : ℚ[T;T⁻¹]) := by ring
    _ = _ := by rw [hp]

theorem Fpull_toLaurent (e : ℕ) :
    Fpull e Vx = Polynomial.toLaurent ((WPReview.nativePolynomial (e + 1)).comp Vpolynomial) :=
  substituteOver_toLaurent _ _

theorem Fpull_reciprocal (e : ℕ) : invert (Fpull e Vx) = Fpull e Qx := by
  change invert (substituteOver _ Vx) = substituteOver _ Qx
  rw [substituteOver_invert, actual_Vx_reciprocal]

/-- The literal unscaled numerator, with all n<=e still present. -/
noncomputable def numeratorIntegral (p e N : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) : (integralRationals p)[T;T⁻¹] :=
  let L := Polynomial.toLaurent ((nativeIntegral p e hp he).comp (integralV p hp))
  L - T (N : ℤ) * invert L

theorem actual_numerator_rational (p e N : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) :
    coefficientMap (integralRationals p).subtype (numeratorIntegral p e N hp he) =
      Fpull e Vx - T (N : ℤ) * Fpull e Qx := by
  simp only [numeratorIntegral, map_sub, map_mul, coefficientMap_T, coefficientMap_invert,
    coefficientMap_toLaurent, Polynomial.map_comp, nativeIntegral_map_rational,
    integralV_map_rational]
  rw [← Fpull_toLaurent, Fpull_reciprocal]

theorem actual_numerator_field_zero (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hd : p / 6 ≤ e) :
    coefficientMap (residueHom p) (numeratorIntegral p e ((p - 1) / 2) hp he) = 0 := by
  simp only [numeratorIntegral, map_sub, map_mul, coefficientMap_T, coefficientMap_invert,
    coefficientMap_toLaurent, Polynomial.map_comp, nativeIntegral_map_field,
    integralV_map_field]
  rw [actual_full_native_field_cutoff p e hp he hd, ← actual_native_Hasse_Laurent p hp, sub_self]

theorem divide_prime_integral (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : 0 ≤ padicValRat p q) (hres : (q : ZMod p) = 0) :
    0 ≤ padicValRat p (q / (p : ℚ)) := by
  have hval := (integral_residue_zero_iff p q hq).mp hres
  simp only [WPReview.RationalCongruent, sub_zero] at hval
  rcases hval with hzero | hval
  · rw [hzero, zero_div]; simp
  · have hq0 : q ≠ 0 := by
      intro hzero; rw [hzero] at hval; simp at hval
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    rw [padicValRat.div hq0 hp0, padicValRat.self (Fact.out : p.Prime).one_lt]
    omega

/-- Actual chi has p-integral coefficients; Hasse reciprocity is proved, not a hypothesis. -/
theorem actual_chiX_integral (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hd : p / 6 ≤ e) (j : ℤ) :
    0 ≤ padicValRat p ((chiX p ((p - 1) / 2) e).coeff j) := by
  let Delta := numeratorIntegral p e ((p - 1) / 2) hp he
  have hQ := congrArg (fun L : ℚ[T;T⁻¹] => L.coeff j)
    (actual_numerator_rational p e ((p - 1) / 2) hp he)
  rw [coefficientMap_coeff] at hQ
  have hF := congrArg (fun L : (ZMod p)[T;T⁻¹] => L.coeff j)
    (actual_numerator_field_zero p e hp he hd)
  rw [coefficientMap_coeff] at hF
  have hres : ((Delta.coeff j).val : ZMod p) = 0 := hF
  have hdiv := divide_prime_integral p (Delta.coeff j).val (Delta.coeff j).property hres
  have hcoeff : (chiX p ((p - 1) / 2) e).coeff j = (Delta.coeff j).val / p := by
    rw [chiX, ← smul_eq_C_mul]
    change (1 / (p : ℚ)) * (Fpull e Vx - T (((p - 1) / 2 : ℕ) : ℤ) * Fpull e Qx).coeff j = _
    rw [← hQ]
    change (1 / (p : ℚ)) * (Delta.coeff j).val = (Delta.coeff j).val / p
    ring
  rw [hcoeff]
  exact hdiv

theorem actual_native_cutoff_chi_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (j : ℤ) :
    0 ≤ padicValRat p ((chiX p ((p - 1) / 2) (p - 1 - p / 6)).coeff j) := by
  apply actual_chiX_integral p _ (by omega) (by omega) _ j
  have hdiv := Nat.div_mul_le_self p 6
  omega

end WPActualChiSource
