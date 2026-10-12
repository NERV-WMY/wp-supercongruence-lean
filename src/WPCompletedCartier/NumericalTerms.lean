import WPCompletedCartier.Basic
import WPResidueQuotient.PolePresentation
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
Actual integral finite Cartier numerators and factorial terms at `u = 1/10`.
The rational selector and literal polynomial proofs are imported.  The only
new selector proofs concern extension of coefficients to the actual rings.
-/

namespace WPCompletedCartier.NumericalTerms

noncomputable section

open scoped BigOperators
open WPResidueQuotient

section FiniteAlgebra

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Coefficient Frobenius fixes every coefficient of the actual group algebra. -/
def phi (p : ℕ) : WPResidueQuotient.LaurentPolynomial R →ₐ[R] WPResidueQuotient.LaurentPolynomial R :=
  AddMonoidAlgebra.mapDomainAlgHom R R (WPCartierFinite.exponentScale p)

/-- Finite coefficient selection, using the checked quotient-lattice scaling. -/
def kappa (p : ℕ) (hp : 0 < p) :
    WPResidueQuotient.LaurentPolynomial R →ₗ[R] WPResidueQuotient.LaurentPolynomial R where
  toFun P := AddMonoidAlgebra.ofCoeff
    (Finsupp.comapDomain (WPCartierFinite.exponentScale p) P.coeff
      (WPCartierFinite.exponentScale_injective p hp).injOn)
  map_add' P Q := by
    apply AddMonoidAlgebra.coeff_injective
    ext x
    simp [Finsupp.comapDomain_apply]
  map_smul' c P := by
    apply AddMonoidAlgebra.coeff_injective
    ext x
    simp [Finsupp.comapDomain_apply]

@[simp] theorem kappa_coeff (p : ℕ) (hp : 0 < p)
    (P : WPResidueQuotient.LaurentPolynomial R) (x : Exponents) :
    (kappa p hp P).coeff x = P.coeff (WPCartierFinite.exponentScale p x) := rfl

@[simp] theorem phi_single (p : ℕ) (x : Exponents) (c : R) :
    phi p (AddMonoidAlgebra.single x c) =
      AddMonoidAlgebra.single (WPCartierFinite.exponentScale p x) c := by
  simp [phi, AddMonoidAlgebra.mapDomainAlgHom]

@[simp] theorem kappa_scalar_change (p : ℕ) (hp : 0 < p) (φ : R →+* S)
    (P : WPResidueQuotient.LaurentPolynomial R) :
    kappa p hp (Specialization.laurentMap φ P) =
      Specialization.laurentMap φ (kappa p hp P) := by
  apply AddMonoidAlgebra.coeff_injective
  ext x
  simp

theorem phi_scalar_change (p : ℕ) (φ : R →+* S) (P : WPResidueQuotient.LaurentPolynomial R) :
    phi p (Specialization.laurentMap φ P) =
      Specialization.laurentMap φ (phi p P) := by
  induction P using AddMonoidAlgebra.induction_on with
  | of x => simp
  | add P Q hP hQ => simp [hP, hQ]
  | smul c P hP =>
      simp only [Specialization.laurentMap_smul, map_smul, hP]

@[simp] theorem kappa_rational (p : ℕ) (hp : 0 < p)
    (P : WPCartierFinite.LaurentPolynomial) :
    kappa p hp P = WPCartierFinite.kappa p hp P := rfl

@[simp] theorem phi_rational (p : ℕ) (P : WPCartierFinite.LaurentPolynomial) :
    phi p P = WPCartierFinite.phi p P := rfl

/-- Exact agreement of the independently checked canonical lattice conventions. -/
theorem canonicalRepresentative_eq (x : Exponents) :
    canonicalRepresentative x = WPCartierFinite.canonicalSix x := by
  symm
  apply canonicalRepresentative_unique x (WPCartierFinite.canonicalSix x)
  · exact ⟨WPCartierFinite.canonicalSix_nonnegative x,
      WPCartierFinite.canonicalSix_has_zero x⟩
  · exact WPCartierFinite.qSix_canonicalSix x

theorem canonicalDegreeNat_eq (x : Exponents) :
    canonicalDegreeNat x = WPCartierFinite.canonicalDegree x := by
  rw [canonicalDegreeNat_eq_sum_toNat, canonicalRepresentative_eq]
  rfl

theorem canonicalDegreeNat_scale (p : ℕ) (hp : 0 < p) (x : Exponents) :
    canonicalDegreeNat (WPCartierFinite.exponentScale p x) =
      p * canonicalDegreeNat x := by
  simp only [canonicalDegreeNat_eq, WPCartierFinite.canonicalDegree_scale p hp]

theorem kappa_supported (p : ℕ) (hp : 0 < p) (d : ℕ)
    {P : WPResidueQuotient.LaurentPolynomial R} (hP : P ∈ numeratorFiltration R (p * d)) :
    kappa p hp P ∈ numeratorFiltration R d := by
  rw [mem_numeratorFiltration] at hP ⊢
  intro x hx
  have hpx : WPCartierFinite.exponentScale p x ∈ P.coeff.support := by
    simpa only [Finsupp.mem_support_iff, kappa_coeff] using hx
  have h := hP _ hpx
  rw [canonicalDegreeNat_scale p hp] at h
  exact Nat.le_of_mul_le_mul_left h hp

theorem kappa_supported_strict (p : ℕ) (hp : 0 < p) (d : ℕ)
    {P : WPResidueQuotient.LaurentPolynomial R} (hP : P ∈ numeratorFiltration R (p * d - 1)) :
    kappa p hp P ∈ numeratorFiltration R (d - 1) := by
  rw [mem_numeratorFiltration] at hP ⊢
  intro x hx
  have hpx : WPCartierFinite.exponentScale p x ∈ P.coeff.support := by
    simpa only [Finsupp.mem_support_iff, kappa_coeff] using hx
  have h := hP _ hpx
  rw [canonicalDegreeNat_scale p hp] at h
  by_cases hd : d = 0
  · subst d
    simp only [mul_zero, Nat.zero_sub] at h ⊢
    exact Nat.le_of_mul_le_mul_left (by simpa only [mul_zero] using h) hp
  · have hdpos : 0 < p * d := Nat.mul_pos hp (Nat.pos_of_ne_zero hd)
    have hlt : p * canonicalDegreeNat x < p * d := by omega
    have hxd : canonicalDegreeNat x < d := (Nat.mul_lt_mul_left hp).mp hlt
    omega

theorem kappa_mul_phi (p : ℕ) (hp : 0 < p) (P H : WPResidueQuotient.LaurentPolynomial R) :
    kappa p hp (P * phi p H) = kappa p hp P * H := by
  have hsingle (x : Exponents) (c : R) :
      kappa p hp (P * phi p (AddMonoidAlgebra.single x c)) =
        kappa p hp P * AddMonoidAlgebra.single x c := by
    apply AddMonoidAlgebra.coeff_injective
    ext y
    simp only [phi_single, kappa_coeff, AddMonoidAlgebra.coeff_mul_single_apply]
    congr 2
    simp
  induction H using AddMonoidAlgebra.induction_on with
  | of x => simpa using hsingle x 1
  | add H K hH hK => simp [mul_add, hH, hK]
  | smul c H hH => simp [hH]

@[simp] theorem kappa_scaled_single (p : ℕ) (hp : 0 < p) (x : Exponents) (c : R) :
    kappa p hp (AddMonoidAlgebra.single (WPCartierFinite.exponentScale p x) c) =
      AddMonoidAlgebra.single x c := by
  apply AddMonoidAlgebra.coeff_injective
  exact Finsupp.comapDomain_single _ _ _ _

@[simp] theorem kappa_one (p : ℕ) (hp : 0 < p) :
    kappa p hp (1 : WPResidueQuotient.LaurentPolynomial R) = 1 := by
  simpa [AddMonoidAlgebra.one_def] using kappa_scaled_single (R := R) p hp 0 1

@[simp] theorem kappa_phi (p : ℕ) (hp : 0 < p) (P : WPResidueQuotient.LaurentPolynomial R) :
    kappa p hp (phi p P) = P := by
  simpa using kappa_mul_phi p hp 1 P

theorem logarithmicDerivation_coeff (w : Exponents →+ ℤ)
    (P : WPResidueQuotient.LaurentPolynomial R) (x : Exponents) :
    (logarithmicDerivation w P).coeff x = (w x : R) * P.coeff x := by
  classical
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ => simp [hP, hQ, mul_add]
  | single y r =>
      rw [logarithmicDerivation_single]
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      split_ifs with hy
      · subst y
        rfl
      · simp

theorem kappa_logarithmicDerivation (p : ℕ) (hp : 0 < p) (w : Exponents →+ ℤ)
    (P : WPResidueQuotient.LaurentPolynomial R) :
    kappa p hp (logarithmicDerivation w P) =
      (p : R) • logarithmicDerivation w (kappa p hp P) := by
  apply AddMonoidAlgebra.coeff_injective
  ext x
  simp only [kappa_coeff, logarithmicDerivation_coeff, AddMonoidAlgebra.coeff_smul,
    Finsupp.smul_apply, smul_eq_mul]
  have hw : w (WPCartierFinite.exponentScale p x) = (p : ℤ) * w x := by
    rw [WPCartierFinite.exponentScale_eq_nsmul, w.map_nsmul]
    simp
  rw [hw, Int.cast_mul, Int.cast_natCast, mul_assoc]

theorem logarithmicDerivation_phi (p : ℕ) (w : Exponents →+ ℤ)
    (P : WPResidueQuotient.LaurentPolynomial R) :
    logarithmicDerivation w (phi p P) = (p : R) • phi p (logarithmicDerivation w P) := by
  induction P using AddMonoidAlgebra.induction_on with
  | of x =>
      have hw : w (WPCartierFinite.exponentScale p x) = (p : ℤ) * w x := by
        rw [WPCartierFinite.exponentScale_eq_nsmul, w.map_nsmul]
        simp
      change logarithmicDerivation w (phi p (AddMonoidAlgebra.single x 1)) =
        (p : R) • phi p (logarithmicDerivation w (AddMonoidAlgebra.single x 1))
      rw [phi_single, logarithmicDerivation_single, logarithmicDerivation_single,
        phi_single, hw]
      simp only [Int.cast_mul, Int.cast_natCast, mul_one, AddMonoidAlgebra.smul_single']
  | add P Q hP hQ => simp [hP, hQ, smul_add]
  | smul c P hP =>
      simp only [map_smul, Derivation.map_smul, hP]
      rw [smul_comm]

end FiniteAlgebra

section PadicCoefficients

variable (p : ℕ) [Fact p.Prime]

/-- A rational coefficient is placed in the actual p-adic integers by its norm. -/
def integralRat (q : ℚ) (hq : 0 ≤ padicValRat p q) : ℤ_[p] :=
  ⟨(q : ℚ_[p]), (Padic.norm_le_one_iff_val_nonneg _).mpr
    (by simpa only [Padic.valuation_ratCast] using hq)⟩

@[simp] theorem integralRat_coe (q : ℚ) (hq : 0 ≤ padicValRat p q) :
    (integralRat p q hq : ℚ_[p]) = (q : ℚ_[p]) := rfl

theorem integralRat_zero (hq : 0 ≤ padicValRat p 0) :
    integralRat p 0 hq = 0 := by
  apply Subtype.ext
  simp

/-- The finite coefficient lift uses the polynomial's actual coefficient function. -/
def integralPolynomial (P : WPCartierFinite.LaurentPolynomial)
    (hP : ∀ x, WPCartierFinite.pIntegral p (P.coeff x)) : WPResidueQuotient.LaurentPolynomial ℤ_[p] :=
  AddMonoidAlgebra.ofCoeff (Finsupp.onFinset P.coeff.support
    (fun x => integralRat p (P.coeff x)
      (WPCartierFinite.pIntegral_valuation_nonnegative p _ (hP x)))
    (by
      intro x hx
      by_contra hn
      apply hx
      apply Subtype.ext
      change (P.coeff x : ℚ_[p]) = 0
      simp only [Finsupp.notMem_support_iff.mp hn, Rat.cast_zero]))

@[simp] theorem integralPolynomial_coeff (P : WPCartierFinite.LaurentPolynomial)
    (hP : ∀ x, WPCartierFinite.pIntegral p (P.coeff x)) (x : Exponents) :
    (integralPolynomial p P hP).coeff x = integralRat p (P.coeff x)
      (WPCartierFinite.pIntegral_valuation_nonnegative p _ (hP x)) := rfl

def toField : WPResidueQuotient.LaurentPolynomial ℤ_[p] →+* WPResidueQuotient.LaurentPolynomial ℚ_[p] :=
  Specialization.laurentMap PadicInt.Coe.ringHom

def fromRational : WPCartierFinite.LaurentPolynomial →+* WPResidueQuotient.LaurentPolynomial ℚ_[p] :=
  Specialization.laurentMap (algebraMap ℚ ℚ_[p])

theorem toField_injective : Function.Injective (toField p) := by
  intro P Q h
  apply AddMonoidAlgebra.coeff_injective
  ext x
  apply Subtype.val_injective
  have hx := congrArg (fun H : WPResidueQuotient.LaurentPolynomial ℚ_[p] => H.coeff x) h
  change (P.coeff x : ℚ_[p]) = (Q.coeff x : ℚ_[p]) at hx
  exact hx

@[simp] theorem toField_integralPolynomial (P : WPCartierFinite.LaurentPolynomial)
    (hP : ∀ x, WPCartierFinite.pIntegral p (P.coeff x)) :
    toField p (integralPolynomial p P hP) = fromRational p P := by
  apply AddMonoidAlgebra.coeff_injective
  ext x
  change ((integralPolynomial p P hP).coeff x : ℚ_[p]) = (P.coeff x : ℚ_[p])
  rfl

theorem integralPolynomial_supported (P : WPCartierFinite.LaurentPolynomial)
    (hP : ∀ x, WPCartierFinite.pIntegral p (P.coeff x)) (d : ℕ)
    (hd : WPCartierFinite.SupportBound P d) :
    integralPolynomial p P hP ∈ numeratorFiltration ℤ_[p] d := by
  rw [mem_numeratorFiltration]
  intro x hx
  rw [canonicalDegreeNat_eq]
  apply hd x
  apply Finsupp.mem_support_iff.mpr
  intro hzero
  have hz : (integralPolynomial p P hP).coeff x = 0 := by
    apply Subtype.ext
    change (P.coeff x : ℚ_[p]) = 0
    simp only [hzero, Rat.cast_zero]
  exact (Finsupp.mem_support_iff.mp hx) hz

variable (hp7 : 7 ≤ p)

/-- The literal numerical fiber; the prime 7 and prime 19 are included. -/
def f : WPResidueQuotient.LaurentPolynomial ℤ_[p] := torusPolynomial (Parameter.integralTenth p hp7)

/-- The actual integral divided error is lifted from checked literal coefficients. -/
def G : WPResidueQuotient.LaurentPolynomial ℤ_[p] :=
  integralPolynomial p (WPCartierFinite.literalG p)
    (WPCartierFinite.literalG_coefficient_integral p Fact.out hp7)

@[simp] theorem toField_G : toField p (G p hp7) =
    fromRational p (WPCartierFinite.literalG p) := by
  exact toField_integralPolynomial p _ _

theorem fromRational_literalF : fromRational p WPCartierFinite.literalF =
    torusPolynomial (1 / 10 : ℚ_[p]) := by
  have hx (i : Fin 6) : WPCartierFinite.laurentMap (MvPolynomial.X i) =
      laurentVertex (R := ℚ) i := by
    simp only [MvPolynomial.X, WPCartierFinite.laurentMap_monomial]
    congr 1
    ext j
    simp [WPCartierFinite.ordinaryExponent, sixVertex, sixToFive, Pi.single_apply,
      Finsupp.single_apply, eq_comm]
  rw [WPCartierFinite.literalF_formula]
  simp only [hx, fromRational, map_sub, map_one, Specialization.laurentMap_smul,
    map_sum, Specialization.laurentMap_vertex]
  norm_num [torusPolynomial, Algebra.smul_def]

@[simp] theorem toField_f : toField p (f p hp7) =
    fromRational p WPCartierFinite.literalF := by
  rw [fromRational_literalF]
  change Specialization.laurentMap PadicInt.Coe.ringHom
    (torusPolynomial (Parameter.integralTenth p hp7)) = _
  rw [Specialization.laurentMap_f]
  congr 1
  exact ParameterSpecialization.integralTenth_in_field p hp7

theorem f_eq_integralPolynomial : f p hp7 =
    integralPolynomial p WPCartierFinite.literalF
      (WPCartierFinite.literalF_coefficient_integral p Fact.out hp7) := by
  apply toField_injective p
  rw [toField_f, toField_integralPolynomial]

theorem phi_fromRational (P : WPCartierFinite.LaurentPolynomial) :
    phi p (fromRational p P) = fromRational p (WPCartierFinite.phi p P) := by
  exact phi_scalar_change p (algebraMap ℚ ℚ_[p]) P

/-- Literal defining equation, in the actual integral finite group algebra. -/
theorem G_scaled : (p : ℤ_[p]) • G p hp7 = phi p (f p hp7) - f p hp7 ^ p := by
  apply toField_injective p
  simp only [toField, Specialization.laurentMap_smul, map_natCast,
    ← phi_scalar_change, map_sub, map_pow]
  change (p : ℚ_[p]) • toField p (G p hp7) =
    phi p (toField p (f p hp7)) - toField p (f p hp7) ^ p
  rw [toField_G, toField_f, phi_fromRational]
  rw [← map_pow, ← map_sub]
  have h := congrArg (fromRational p)
    (WPCartierFinite.literalG_scaled p (Fact.out : p.Prime).pos)
  simpa only [fromRational, Specialization.laurentMap_smul, map_natCast] using h

theorem toField_G_formula : toField p (G p hp7) =
    (1 / (p : ℚ_[p])) • (phi p (toField p (f p hp7)) - toField p (f p hp7) ^ p) := by
  rw [toField_G, toField_f, phi_fromRational, ← map_pow, ← map_sub]
  have h := congrArg (fromRational p)
    (WPCartierFinite.literalG_formula p)
  simpa only [fromRational, Specialization.laurentMap_smul, map_div₀,
    map_one, map_natCast] using h

theorem f_supported : f p hp7 ∈ numeratorFiltration ℤ_[p] 1 :=
  torusPolynomial_mem_numeratorFiltration _

theorem G_supported : G p hp7 ∈ numeratorFiltration ℤ_[p] p :=
  integralPolynomial_supported p _ _ p (WPCartierFinite.literalG_support p)

theorem numeratorFiltration_pow {P : WPResidueQuotient.LaurentPolynomial ℤ_[p]} {d : ℕ}
    (hP : P ∈ numeratorFiltration ℤ_[p] d) (k : ℕ) :
    P ^ k ∈ numeratorFiltration ℤ_[p] (k * d) := by
  induction k with
  | zero => simpa using one_mem_numeratorFiltration (R := ℤ_[p]) 0
  | succ k ih =>
      simpa only [pow_succ, Nat.succ_mul] using numeratorFiltration_mul ih hP

/-- The literal numerator of the kth generator term, with an admissible pole h. -/
def selectedNumerator (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h k : ℕ) :
    WPResidueQuotient.LaurentPolynomial ℤ_[p] :=
  kappa p (Fact.out : p.Prime).pos (A * f p hp7 ^ (p * h - m) * G p hp7 ^ k)

theorem selectedNumerator_scalar_change (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h k : ℕ) :
    toField p (selectedNumerator p hp7 A m h k) =
      kappa p (Fact.out : p.Prime).pos
        (toField p A * fromRational p WPCartierFinite.literalF ^ (p * h - m) *
          fromRational p (WPCartierFinite.literalG p) ^ k) := by
  simp only [selectedNumerator, toField, ← kappa_scalar_change,
    map_mul, map_pow]
  change kappa p (Fact.out : p.Prime).pos
      (toField p A * toField p (f p hp7) ^ (p * h - m) * toField p (G p hp7) ^ k) = _
  rw [toField_f, toField_G]
  rfl

theorem selectedNumerator_rational (A : WPCartierFinite.LaurentPolynomial)
    (hA : ∀ x, WPCartierFinite.pIntegral p (A.coeff x)) (m h k : ℕ) :
    toField p (selectedNumerator p hp7 (integralPolynomial p A hA) m h k) =
      fromRational p (WPCartierFinite.kappa p (Fact.out : p.Prime).pos
        (A * WPCartierFinite.literalF ^ (p * h - m) * WPCartierFinite.literalG p ^ k)) := by
  rw [selectedNumerator_scalar_change, toField_integralPolynomial]
  simp only [← map_pow, ← map_mul]
  exact kappa_scalar_change p (Fact.out : p.Prime).pos (algebraMap ℚ ℚ_[p]) _

theorem selectedNumerator_closed (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h k : ℕ)
    (hmh : m ≤ p * h) (hA : A ∈ numeratorFiltration ℤ_[p] m) :
    selectedNumerator p hp7 A m h k ∈ numeratorFiltration ℤ_[p] (h + k) := by
  apply kappa_supported
  have hf := numeratorFiltration_pow p (f_supported p hp7) (p * h - m)
  have hG := numeratorFiltration_pow p (G_supported p hp7) k
  have hb := numeratorFiltration_mul (numeratorFiltration_mul hA hf) hG
  have he : m + ((p * h - m) * 1) + k * p = p * (h + k) := by
    rw [Nat.mul_one, Nat.mul_add, Nat.mul_comm k p]
    omega
  simpa only [he] using hb

theorem selectedNumerator_interior (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h k : ℕ)
    (hm : 1 ≤ m) (hmh : m ≤ p * h)
    (hA : A ∈ numeratorFiltration ℤ_[p] (m - 1)) :
    selectedNumerator p hp7 A m h k ∈ numeratorFiltration ℤ_[p] (h + k - 1) := by
  apply kappa_supported_strict
  have hf := numeratorFiltration_pow p (f_supported p hp7) (p * h - m)
  have hG := numeratorFiltration_pow p (G_supported p hp7) k
  have hb := numeratorFiltration_mul (numeratorFiltration_mul hA hf) hG
  have he : m - 1 + ((p * h - m) * 1) + k * p = p * (h + k) - 1 := by
    rw [Nat.mul_one, Nat.mul_add, Nat.mul_comm k p]
    omega
  simpa only [he] using hb

/-- Literal low-pole numerators, with the same order as the checked finite array. -/
def finiteNumerator (k r : ℕ) : WPResidueQuotient.LaurentPolynomial ℤ_[p] :=
  kappa p (Fact.out : p.Prime).pos (G p hp7 ^ k * f p hp7 ^ (p - r))

theorem finiteNumerator_scalar_change (k r : ℕ) :
    toField p (finiteNumerator p hp7 k r) =
      fromRational p (WPCartierFinite.finiteNumerator p (Fact.out : p.Prime).pos k r) := by
  simp only [finiteNumerator, toField, ← kappa_scalar_change, map_mul, map_pow]
  change kappa p (Fact.out : p.Prime).pos
      (toField p (G p hp7) ^ k * toField p (f p hp7) ^ (p - r)) = _
  rw [toField_G, toField_f]
  simp only [← map_pow, ← map_mul]
  exact kappa_scalar_change p (Fact.out : p.Prime).pos (algebraMap ℚ ℚ_[p]) _

theorem finiteNumerator_supported (k r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ p) :
    finiteNumerator p hp7 k r ∈ numeratorFiltration ℤ_[p] k := by
  have hA : (1 : WPResidueQuotient.LaurentPolynomial ℤ_[p]) ∈
      numeratorFiltration ℤ_[p] (r - 1) := one_mem_numeratorFiltration _
  have hb := selectedNumerator_interior p hp7 1 r 1 k hr (by simpa using hrp) hA
  simpa [finiteNumerator, selectedNumerator, mul_comm] using hb

end PadicCoefficients

section FactorialScalars

variable (p : ℕ) [Fact p.Prime]

theorem factorialTailScalar_nonnegative (hp7 : 7 ≤ p) (k : ℕ) :
    0 ≤ padicValRat p (WPCartierFinite.factorialTailScalar p k) := by
  by_cases hk : k = 0
  · subst k
    simp [WPCartierFinite.factorialTailScalar]
  · have h := WPCartierFinite.factorial_tail_lower_bound p k Fact.out hp7 (by omega)
    have hkQ : (1 : ℚ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have he : (0 : ℚ) ≤ (padicValRat p (WPCartierFinite.factorialTailScalar p k) : ℚ) := by
      linarith
    exact_mod_cast he

/-- This integral scalar is literally p^k/k!, not a replacement coefficient. -/
def factorialTail (hp7 : 7 ≤ p) (k : ℕ) : ℤ_[p] :=
  integralRat p (WPCartierFinite.factorialTailScalar p k)
    (factorialTailScalar_nonnegative p hp7 k)

@[simp] theorem factorialTail_coe (hp7 : 7 ≤ p) (k : ℕ) :
    (factorialTail p hp7 k : ℚ_[p]) =
      (p : ℚ_[p]) ^ k / (k.factorial : ℚ_[p]) := by
  simp [factorialTail, WPCartierFinite.factorialTailScalar]

def factorialRatio (m h : ℕ) : ℕ := (m - 1).factorial / (h - 1).factorial

theorem factorialRatio_mul (m h : ℕ) (hhm : h ≤ m) :
    factorialRatio m h * (h - 1).factorial = (m - 1).factorial :=
  Nat.div_mul_cancel (Nat.factorial_dvd_factorial (by omega))

theorem factorialRatio_cast (m h : ℕ) (hhm : h ≤ m) :
    (factorialRatio m h : ℚ_[p]) =
      ((m - 1).factorial : ℚ_[p]) / ((h - 1).factorial : ℚ_[p]) := by
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero (h - 1))).mpr
  exact_mod_cast factorialRatio_mul m h hhm

def termScalar (hp7 : 7 ≤ p) (m h k : ℕ) : ℤ_[p] :=
  factorialTail p hp7 k * (factorialRatio m h : ℤ_[p])

theorem termScalar_coe (hp7 : 7 ≤ p) (m h k : ℕ) (hhm : h ≤ m) :
    (termScalar p hp7 m h k : ℚ_[p]) =
      (p : ℚ_[p]) ^ k / (k.factorial : ℚ_[p]) *
        (((m - 1).factorial : ℚ_[p]) / ((h - 1).factorial : ℚ_[p])) := by
  simp only [termScalar, PadicInt.coe_mul, factorialTail_coe, PadicInt.coe_natCast,
    factorialRatio_cast p m h hhm]

theorem factorialTail_valuation (hp7 : 7 ≤ p) (k : ℕ) :
    (factorialTail p hp7 k : ℚ_[p]).valuation =
      (k : ℤ) - (WPTruncationArithmetic.factorialValuation p k : ℤ) := by
  change ((WPCartierFinite.factorialTailScalar p k : ℚ) : ℚ_[p]).valuation = _
  rw [Padic.valuation_ratCast]
  exact WPCartierFinite.factorial_tail_valuation p k Fact.out

theorem factorialTail_recurrence (hp7 : 7 ≤ p) (k : ℕ) :
    (k + 1 : ℤ_[p]) * factorialTail p hp7 (k + 1) =
      (p : ℤ_[p]) * factorialTail p hp7 k := by
  apply Subtype.ext
  simp only [PadicInt.coe_mul, factorialTail_coe, PadicInt.coe_natCast,
    PadicInt.coe_add, PadicInt.coe_one, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  have hf : (k.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk : (k + 1 : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (by omega : (k + 1 : ℕ) ≠ 0)
  field_simp

theorem termScalar_valuation_lower (hp7 : 7 ≤ p) (m h k : ℕ) (hhm : h ≤ m) :
    (k : ℤ) - (WPTruncationArithmetic.factorialValuation p k : ℤ) ≤
      (termScalar p hp7 m h k : ℚ_[p]).valuation := by
  have hrNat : factorialRatio m h ≠ 0 := by
    intro hz
    have he := factorialRatio_mul m h hhm
    simp only [hz, zero_mul] at he
    exact Nat.factorial_ne_zero (m - 1) he.symm
  have hr : (factorialRatio m h : ℚ_[p]) ≠ 0 := by exact_mod_cast hrNat
  have ht : (factorialTail p hp7 k : ℚ_[p]) ≠ 0 := by
    change ((WPCartierFinite.factorialTailScalar p k : ℚ) : ℚ_[p]) ≠ 0
    exact_mod_cast WPCartierFinite.factorial_tail_nonzero p k Fact.out
  simp only [termScalar, PadicInt.coe_mul, PadicInt.coe_natCast]
  rw [Padic.valuation_mul ht hr, factorialTail_valuation,
    Padic.valuation_natCast]
  have hv : (0 : ℤ) ≤ padicValNat p (factorialRatio m h) := by positivity
  omega

/-- Every actual factorial has only finite p-power loss.  Its unit factor
    is cancelled in Zp, so factorials themselves are never called units. -/
theorem factorial_clear_p_power (n : ℕ) :
    ∃ b : ℤ_[p], ∃ e : ℕ, b * (n.factorial : ℤ_[p]) = (p : ℤ_[p]) ^ e := by
  have hn : (n.factorial : ℤ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  refine ⟨↑(PadicInt.unitCoeff hn)⁻¹, (n.factorial : ℤ_[p]).valuation, ?_⟩
  calc
    _ = ↑(PadicInt.unitCoeff hn)⁻¹ *
        ((PadicInt.unitCoeff hn : ℤ_[p]) * (p : ℤ_[p]) ^ (n.factorial : ℤ_[p]).valuation) :=
      congrArg (fun z : ℤ_[p] => ↑(PadicInt.unitCoeff hn)⁻¹ * z) (PadicInt.unitCoeff_spec hn)
    _ = _ := by rw [← mul_assoc, Units.inv_mul, one_mul]

theorem integralRat_divisible (q : ℚ) (hq : 0 ≤ padicValRat p q) (n : ℕ)
    (hn : (n : ℤ) ≤ padicValRat p q) :
    integralRat p q hq ∈ Adic.powerSubmodule (p : ℤ_[p]) n := by
  rw [PadicScalarCompletion.powerSubmodule_eq_span]
  by_cases hz : q = 0
  · subst q
    rw [integralRat_zero]
    exact Submodule.zero_mem _
  · apply (PadicInt.mem_span_pow_iff_le_valuation _ ?_ n).mpr
    · change n ≤ ((q : ℚ_[p]).valuation).toNat
      rw [Padic.valuation_ratCast]
      omega
    · intro he
      have hqz : (q : ℚ_[p]) = 0 := congrArg Subtype.val he
      exact hz (Rat.cast_injective hqz)

theorem factorialTail_eventual (hp7 : 7 ≤ p) (n : ℕ) :
    ∀ k : ℕ, 6 * n + 1 ≤ k →
      factorialTail p hp7 k ∈ Adic.powerSubmodule (p : ℤ_[p]) n := by
  intro k hk
  apply integralRat_divisible
  have h := WPCartierFinite.factorial_tail_lower_bound p k Fact.out hp7 (by omega)
  have hkQ : (6 * n + 1 : ℚ) ≤ k := by exact_mod_cast hk
  have hnQ : (n : ℚ) ≤ (padicValRat p (WPCartierFinite.factorialTailScalar p k) : ℚ) := by
    nlinarith
  exact_mod_cast hnQ

theorem factorialTail_five (hp7 : 7 ≤ p) (k : ℕ) (hk : 5 ≤ k) :
    factorialTail p hp7 k ∈ Adic.powerSubmodule (p : ℤ_[p]) 5 := by
  apply integralRat_divisible
  exact WPCartierFinite.factorial_tail_five p k Fact.out hp7 hk

theorem termScalar_five (hp7 : 7 ≤ p) (m h k : ℕ) (hk : 5 ≤ k) :
    termScalar p hp7 m h k ∈ Adic.powerSubmodule (p : ℤ_[p]) 5 := by
  simpa only [termScalar, smul_eq_mul, mul_comm] using
    (Adic.powerSubmodule (M := ℤ_[p]) (p : ℤ_[p]) 5).smul_mem
      (factorialRatio m h : ℤ_[p]) (factorialTail_five p hp7 k hk)

theorem termScalar_eventual (hp7 : 7 ≤ p) (n m h k : ℕ) (hk : 6 * n + 1 ≤ k) :
    termScalar p hp7 m h k ∈ Adic.powerSubmodule (p : ℤ_[p]) n := by
  obtain ⟨z, hz⟩ := (Adic.mem_powerSubmodule _ _ _).mp (factorialTail_eventual p hp7 n k hk)
  apply (Adic.mem_powerSubmodule _ _ _).mpr
  refine ⟨z * (factorialRatio m h : ℤ_[p]), ?_⟩
  change (p : ℤ_[p]) ^ n * (z * _) = factorialTail p hp7 k * _
  rw [← mul_assoc]
  change ((p : ℤ_[p]) ^ n • z) * _ = _
  rw [hz]

end FactorialScalars

/-- For a positive input pole this is exactly ceil(m/p). -/
def canonicalPole (p m : ℕ) : ℕ := (m - 1) / p + 1

theorem canonicalPole_positive (p m : ℕ) : 1 ≤ canonicalPole p m := by
  exact Nat.le_add_left 1 ((m - 1) / p)

theorem canonicalPole_le_input (p m : ℕ) (hm : 1 ≤ m) : canonicalPole p m ≤ m := by
  have h := Nat.div_le_self (m - 1) p
  simp only [canonicalPole]
  omega

theorem canonicalPole_admissible (p m : ℕ) (hp : 0 < p) (hm : 1 ≤ m) :
    m ≤ p * canonicalPole p m := by
  have hdiv := Nat.mod_add_div (m - 1) p
  have hmod := Nat.mod_lt (m - 1) hp
  simp only [canonicalPole, Nat.mul_add, Nat.mul_one]
  omega

section ActualTerms

variable (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)

/-- The factorial-cleared term at any positive admissible h.  Its sum is
    `(h-1)!` times the unnormalized Cartier value. -/
def clearedTerm (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h k : ℕ) :
    ActualRing (Parameter.integralTenth p hp7) :=
  factorialTail p hp7 k •
    factorialNumeratorMap (Parameter.integralTenth p hp7) (h + k - 1)
      (selectedNumerator p hp7 A m h k)

theorem clearedTerm_mem_closed (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h k : ℕ)
    (hh : 1 ≤ h) (hmh : m ≤ p * h) (hA : A ∈ numeratorFiltration ℤ_[p] m) :
    clearedTerm p hp7 A m h k ∈ FClosed (Parameter.integralTenth p hp7) := by
  apply (FClosed _).smul_mem
  apply factorialNumeratorMap_mem_closed
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ h + k)] using
    selectedNumerator_closed p hp7 A m h k hmh hA

theorem clearedTerm_mem_interior (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h k : ℕ)
    (hm : 1 ≤ m) (hmh : m ≤ p * h)
    (hA : A ∈ numeratorFiltration ℤ_[p] (m - 1)) :
    clearedTerm p hp7 A m h k ∈ FInterior (Parameter.integralTenth p hp7) := by
  apply (FInterior _).smul_mem
  exact factorialNumeratorMap_mem_interior _ _
    (selectedNumerator_interior p hp7 A m h k hm hmh hA)

def clearedClosedTerm (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h k : ℕ)
    (hh : 1 ≤ h) (hmh : m ≤ p * h) (hA : A ∈ numeratorFiltration ℤ_[p] m) :
    FClosed (Parameter.integralTenth p hp7) :=
  ⟨clearedTerm p hp7 A m h k, clearedTerm_mem_closed p hp7 A m h k hh hmh hA⟩

def clearedInteriorTerm (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h k : ℕ)
    (hm : 1 ≤ m) (hmh : m ≤ p * h) (hA : A ∈ numeratorFiltration ℤ_[p] (m - 1)) :
    FInterior (Parameter.integralTenth p hp7) :=
  ⟨clearedTerm p hp7 A m h k, clearedTerm_mem_interior p hp7 A m h k hm hmh hA⟩

theorem clearedClosedTerm_eventual (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h : ℕ)
    (hh : 1 ≤ h) (hmh : m ≤ p * h) (hA : A ∈ numeratorFiltration ℤ_[p] m)
    (n k : ℕ) (hk : 6 * n + 1 ≤ k) :
    clearedClosedTerm p hp7 A m h k hh hmh hA ∈
      Adic.powerSubmodule (p : ℤ_[p]) n := by
  obtain ⟨z, hz⟩ := (Adic.mem_powerSubmodule _ _ _).mp (factorialTail_eventual p hp7 n k hk)
  let q : FClosed (Parameter.integralTenth p hp7) :=
    ⟨factorialNumeratorMap _ (h + k - 1) (selectedNumerator p hp7 A m h k),
      factorialNumeratorMap_mem_closed _ _ (by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ h + k)] using
          selectedNumerator_closed p hp7 A m h k hmh hA)⟩
  apply (Adic.mem_powerSubmodule _ _ _).mpr
  refine ⟨z • q, ?_⟩
  apply Subtype.ext
  change (p : ℤ_[p]) ^ n • (z • (q : ActualRing (Parameter.integralTenth p hp7))) =
    factorialTail p hp7 k • (q : ActualRing (Parameter.integralTenth p hp7))
  rw [← mul_smul]
  change ((p : ℤ_[p]) ^ n • z) • _ = _
  rw [hz]

theorem clearedInteriorTerm_eventual (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h : ℕ)
    (hm : 1 ≤ m) (hmh : m ≤ p * h) (hA : A ∈ numeratorFiltration ℤ_[p] (m - 1))
    (n k : ℕ) (hk : 6 * n + 1 ≤ k) :
    clearedInteriorTerm p hp7 A m h k hm hmh hA ∈
      Adic.powerSubmodule (p : ℤ_[p]) n := by
  obtain ⟨z, hz⟩ := (Adic.mem_powerSubmodule _ _ _).mp (factorialTail_eventual p hp7 n k hk)
  let q : FInterior (Parameter.integralTenth p hp7) :=
    ⟨factorialNumeratorMap _ (h + k - 1) (selectedNumerator p hp7 A m h k),
      factorialNumeratorMap_mem_interior _ _
        (selectedNumerator_interior p hp7 A m h k hm hmh hA)⟩
  apply (Adic.mem_powerSubmodule _ _ _).mpr
  refine ⟨z • q, ?_⟩
  apply Subtype.ext
  change (p : ℤ_[p]) ^ n • (z • (q : ActualRing (Parameter.integralTenth p hp7))) =
    factorialTail p hp7 k • (q : ActualRing (Parameter.integralTenth p hp7))
  rw [← mul_smul]
  change ((p : ℤ_[p]) ^ n • z) • _ = _
  rw [hz]

/-- The kth term is an actual localized factorial rational function. -/
def generatorTerm (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h k : ℕ) :
    ActualRing (Parameter.integralTenth p hp7) :=
  termScalar p hp7 m h k •
    factorialNumeratorMap (Parameter.integralTenth p hp7) (h + k - 1)
      (selectedNumerator p hp7 A m h k)

theorem generatorTerm_eq_ratio_cleared (A : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (m h k : ℕ) :
    generatorTerm p hp7 A m h k = (factorialRatio m h : ℤ_[p]) •
      clearedTerm p hp7 A m h k := by
  simp only [generatorTerm, clearedTerm, termScalar, mul_smul]
  rw [smul_comm]

theorem generatorTerm_gamma_formula (A : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (m h k : ℕ) (hh : 1 ≤ h) :
    generatorTerm p hp7 A m h k = termScalar p hp7 m h k •
      (algebraMap (WPResidueQuotient.LaurentPolynomial ℤ_[p])
        (ActualRing (Parameter.integralTenth p hp7)) (selectedNumerator p hp7 A m h k) *
          Gamma (Parameter.integralTenth p hp7) (h + k)) := by
  simp only [generatorTerm, factorialNumeratorMap_apply, factorialPole, Gamma,
    Nat.sub_add_cancel (by omega : 1 ≤ h + k)]

theorem generatorTerm_mem_closed (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h k : ℕ)
    (hh : 1 ≤ h) (hmh : m ≤ p * h) (hA : A ∈ numeratorFiltration ℤ_[p] m) :
    generatorTerm p hp7 A m h k ∈ FClosed (Parameter.integralTenth p hp7) := by
  apply (FClosed _).smul_mem
  apply factorialNumeratorMap_mem_closed
  have hd := selectedNumerator_closed p hp7 A m h k hmh hA
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ h + k)] using hd

theorem generatorTerm_mem_interior (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h k : ℕ)
    (hm : 1 ≤ m) (hmh : m ≤ p * h)
    (hA : A ∈ numeratorFiltration ℤ_[p] (m - 1)) :
    generatorTerm p hp7 A m h k ∈ FInterior (Parameter.integralTenth p hp7) := by
  apply (FInterior _).smul_mem
  exact factorialNumeratorMap_mem_interior _ _
    (selectedNumerator_interior p hp7 A m h k hm hmh hA)

def closedTerm (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h k : ℕ)
    (hh : 1 ≤ h) (hmh : m ≤ p * h) (hA : A ∈ numeratorFiltration ℤ_[p] m) :
    FClosed (Parameter.integralTenth p hp7) :=
  ⟨generatorTerm p hp7 A m h k, generatorTerm_mem_closed p hp7 A m h k hh hmh hA⟩

def interiorTerm (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h k : ℕ)
    (hm : 1 ≤ m) (hmh : m ≤ p * h) (hA : A ∈ numeratorFiltration ℤ_[p] (m - 1)) :
    FInterior (Parameter.integralTenth p hp7) :=
  ⟨generatorTerm p hp7 A m h k, generatorTerm_mem_interior p hp7 A m h k hm hmh hA⟩

theorem closedTerm_divisible (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h : ℕ)
    (hh : 1 ≤ h) (hmh : m ≤ p * h) (hA : A ∈ numeratorFiltration ℤ_[p] m)
    (n k : ℕ) (hs : termScalar p hp7 m h k ∈ Adic.powerSubmodule (p : ℤ_[p]) n) :
    closedTerm p hp7 A m h k hh hmh hA ∈
      Adic.powerSubmodule (p : ℤ_[p]) n := by
  obtain ⟨z, hz⟩ := (Adic.mem_powerSubmodule _ _ _).mp
    hs
  let q : FClosed (Parameter.integralTenth p hp7) :=
    ⟨factorialNumeratorMap _ (h + k - 1) (selectedNumerator p hp7 A m h k),
      factorialNumeratorMap_mem_closed _ _ (by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ h + k)] using
          selectedNumerator_closed p hp7 A m h k hmh hA)⟩
  apply (Adic.mem_powerSubmodule _ _ _).mpr
  refine ⟨z • q, ?_⟩
  apply Subtype.ext
  change (p : ℤ_[p]) ^ n • (z • (q : ActualRing (Parameter.integralTenth p hp7))) =
    termScalar p hp7 m h k • (q : ActualRing (Parameter.integralTenth p hp7))
  rw [← mul_smul]
  change ((p : ℤ_[p]) ^ n • z) • _ = _
  rw [hz]

theorem interiorTerm_divisible (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h : ℕ)
    (hm : 1 ≤ m) (hmh : m ≤ p * h) (hA : A ∈ numeratorFiltration ℤ_[p] (m - 1))
    (n k : ℕ) (hs : termScalar p hp7 m h k ∈ Adic.powerSubmodule (p : ℤ_[p]) n) :
    interiorTerm p hp7 A m h k hm hmh hA ∈
      Adic.powerSubmodule (p : ℤ_[p]) n := by
  obtain ⟨z, hz⟩ := (Adic.mem_powerSubmodule _ _ _).mp
    hs
  let q : FInterior (Parameter.integralTenth p hp7) :=
    ⟨factorialNumeratorMap _ (h + k - 1) (selectedNumerator p hp7 A m h k),
      factorialNumeratorMap_mem_interior _ _
        (selectedNumerator_interior p hp7 A m h k hm hmh hA)⟩
  apply (Adic.mem_powerSubmodule _ _ _).mpr
  refine ⟨z • q, ?_⟩
  apply Subtype.ext
  change (p : ℤ_[p]) ^ n • (z • (q : ActualRing (Parameter.integralTenth p hp7))) =
    termScalar p hp7 m h k • (q : ActualRing (Parameter.integralTenth p hp7))
  rw [← mul_smul]
  change ((p : ℤ_[p]) ^ n • z) • _ = _
  rw [hz]

theorem closedTerm_eventual (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h : ℕ)
    (hh : 1 ≤ h) (hmh : m ≤ p * h) (hA : A ∈ numeratorFiltration ℤ_[p] m)
    (n k : ℕ) (hk : 6 * n + 1 ≤ k) :
    closedTerm p hp7 A m h k hh hmh hA ∈
      Adic.powerSubmodule (p : ℤ_[p]) n :=
  closedTerm_divisible p hp7 A m h hh hmh hA n k (termScalar_eventual p hp7 n m h k hk)

theorem interiorTerm_eventual (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h : ℕ)
    (hm : 1 ≤ m) (hmh : m ≤ p * h) (hA : A ∈ numeratorFiltration ℤ_[p] (m - 1))
    (n k : ℕ) (hk : 6 * n + 1 ≤ k) :
    interiorTerm p hp7 A m h k hm hmh hA ∈
      Adic.powerSubmodule (p : ℤ_[p]) n :=
  interiorTerm_divisible p hp7 A m h hm hmh hA n k (termScalar_eventual p hp7 n m h k hk)

theorem closedTerm_five (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h : ℕ)
    (hh : 1 ≤ h) (hmh : m ≤ p * h) (hA : A ∈ numeratorFiltration ℤ_[p] m)
    (k : ℕ) (hk : 5 ≤ k) :
    closedTerm p hp7 A m h k hh hmh hA ∈
      Adic.powerSubmodule (p : ℤ_[p]) 5 :=
  closedTerm_divisible p hp7 A m h hh hmh hA 5 k (termScalar_five p hp7 m h k hk)

theorem interiorTerm_five (A : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (m h : ℕ)
    (hm : 1 ≤ m) (hmh : m ≤ p * h) (hA : A ∈ numeratorFiltration ℤ_[p] (m - 1))
    (k : ℕ) (hk : 5 ≤ k) :
    interiorTerm p hp7 A m h k hm hmh hA ∈
      Adic.powerSubmodule (p : ℤ_[p]) 5 :=
  interiorTerm_divisible p hp7 A m h hm hmh hA 5 k (termScalar_five p hp7 m h k hk)

end ActualTerms

end
end WPCompletedCartier.NumericalTerms
