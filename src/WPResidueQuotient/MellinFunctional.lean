import WPResidueQuotient.MellinBaseChange
import WPResidueQuotient.VertexFunctional
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.CharP.Algebra

/-!
The Mellin coordinates descend through literal common-denominator equality
in the actual localization. A numerator is evaluated by a finite coefficient
sum, and a pole of order m is normalized by (m-1)!. The all-index pole and
canonicalization identities prove independence of the chosen presentation.
The resulting semilinear maps kill the actual logarithmic derivative images.
-/

noncomputable section

namespace WPResidueQuotient.MellinFactors

open scoped BigOperators LaurentSeries

variable (K : Type*) [Field K] [CharZero K]

instance LSK_charZero : CharZero (LSK K) :=
  charZero_of_injective_ringHom (HahnSeries.C_injective (Γ := ℤ) (R := K))

theorem increment_eq_add_standardExponent (a : ExponentVector) (i : Fin 6) :
    increment a i = a + standardExponent i := by
  classical
  ext j
  by_cases h : j = i <;> simp [increment, standardExponent, h]

theorem increment_nonneg (a : ExponentVector) (ha : ∀ i, 0 ≤ a i) (i j : Fin 6) :
    0 ≤ increment a i j := by
  rw [increment_eq_add_standardExponent]
  exact add_nonneg (ha j) (standardExponent_nonneg i j)

/-- The proved order-five endpoint supplies canonicalization in the literal
six-exponent lattice, including numerators whose minimum is positive. -/
theorem mellinSeriesK_canonicalize (r : Fin 5) (m : ℤ) (a : ExponentVector)
    (ha : ∀ i, 0 ≤ a i) :
    mellinSeriesK K r m (canonicalRepresentative (latticeQ a)) =
      mellinSeriesK K r m a := by
  rw [canonicalRepresentative_latticeQ]
  have hm : 0 ≤ minimumEntry a := le_minimumEntry a 0 ha
  have hc : ((minimumEntry a).toNat : ℤ) = minimumEntry a := Int.toNat_of_nonneg hm
  have h := mellinSeriesK_subtractDiagonal K r m a (minimumEntry a).toNat (by
    intro i
    rw [hc]
    exact minimumEntry_le a i)
  have he : subtractDiagonal a (minimumEntry a) = normalizeExponents a := by
    funext i
    rfl
  rw [hc, he] at h
  exact h.symm

def canonicalMellinSeries (r : Fin 5) (m : ℤ) (x : Exponents) : LSK K :=
  mellinSeriesK K r m (canonicalRepresentative x)

theorem canonicalMellinSeries_vertex (r : Fin 5) (m : ℤ) (x : Exponents) (i : Fin 6) :
    canonicalMellinSeries K r m (x + sixVertex i) =
      mellinSeriesK K r m (increment (canonicalRepresentative x) i) := by
  have hq : latticeQ (increment (canonicalRepresentative x) i) = x + sixVertex i := by
    rw [increment_eq_add_standardExponent, map_add, latticeQ_canonicalRepresentative,
      ← sixVertex_eq_latticeQ_standardExponent]
  rw [canonicalMellinSeries, ← hq]
  exact mellinSeriesK_canonicalize K r m _
    (increment_nonneg _ (canonicalRepresentative_nonneg x) i)

theorem canonicalMellinSeries_pole (r : Fin 5) (m : ℤ) (x : Exponents) :
    canonicalMellinSeries K r (m + 1) x -
        ∑ i, uSeries K * canonicalMellinSeries K r (m + 1) (x + sixVertex i) =
      (m : LSK K) * canonicalMellinSeries K r m x := by
  simp_rw [canonicalMellinSeries_vertex]
  exact mellinSeriesK_pole_relation K r m (canonicalRepresentative x)

section CommonPole

variable {R : Type*} [CommRing R]
variable (σ : R →+* LSK K) (u : R) (hu : σ u = uSeries K)

def monomialMellinMap (r : Fin 5) (m : ℕ) (x : Exponents) : R →ₛₗ[σ] LSK K where
  toFun c := σ c * canonicalMellinSeries K r (m : ℤ) x
  map_add' c d := by rw [map_add, add_mul]
  map_smul' c d := by
    change σ (c * d) * _ = σ c * (σ d * _)
    rw [map_mul, mul_assoc]

/-- A finite sum over the actual supported Laurent numerator. -/
def numeratorMellinMap (r : Fin 5) (m : ℕ) : LaurentPolynomial R →ₛₗ[σ] LSK K :=
  (Finsupp.lsum (LSK K) (monomialMellinMap K σ r m)).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] theorem numeratorMellinMap_single (r : Fin 5) (m : ℕ) (x : Exponents) (c : R) :
    numeratorMellinMap K σ r m (AddMonoidAlgebra.single x c) =
      σ c * canonicalMellinSeries K r (m : ℤ) x := by
  change Finsupp.lsum (LSK K) (monomialMellinMap K σ r m) (Finsupp.single x c) = _
  rw [Finsupp.lsum_single]
  rfl

theorem numerator_mul_torus (P : LaurentPolynomial R) :
    P * torusPolynomial u = P - u • ∑ i : Fin 6, P * laurentVertex i := by
  rw [torusPolynomial, mul_sub, mul_one, Algebra.smul_def]
  congr 1
  rw [← mul_assoc, mul_comm P (algebraMap R (LaurentPolynomial R) u),
    mul_assoc, Finset.mul_sum]

include hu in
theorem numeratorMellinMap_raise_single (r : Fin 5) (m : ℕ) (x : Exponents) (c : R) :
    numeratorMellinMap K σ r (m + 1)
        (AddMonoidAlgebra.single x c * torusPolynomial u) =
      (m : LSK K) * numeratorMellinMap K σ r m (AddMonoidAlgebra.single x c) := by
  rw [numerator_mul_torus, map_sub, map_smulₛₗ, map_sum]
  simp only [laurentVertex, AddMonoidAlgebra.single_mul_single, mul_one,
    numeratorMellinMap_single, smul_eq_mul, hu]
  have hp : canonicalMellinSeries K r ((m + 1 : ℕ) : ℤ) x -
      ∑ i, uSeries K * canonicalMellinSeries K r ((m + 1 : ℕ) : ℤ) (x + sixVertex i) =
        (m : LSK K) * canonicalMellinSeries K r (m : ℤ) x := by
    simpa only [Nat.cast_add, Nat.cast_one, Int.cast_natCast] using
      canonicalMellinSeries_pole K r (m : ℤ) x
  calc
    _ = σ c * (canonicalMellinSeries K r ((m + 1 : ℕ) : ℤ) x -
          ∑ i : Fin 6, uSeries K *
            canonicalMellinSeries K r ((m + 1 : ℕ) : ℤ) (x + sixVertex i)) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ = _ := by rw [hp]; ring

include hu in
/-- Pole raising is verified on actual finite numerators, with no support
assumption and with the canonical lower-endpoint terms already accounted for. -/
theorem numeratorMellinMap_raise (r : Fin 5) (m : ℕ) (P : LaurentPolynomial R) :
    numeratorMellinMap K σ r (m + 1) (P * torusPolynomial u) =
      (m : LSK K) * numeratorMellinMap K σ r m P := by
  induction P using AddMonoidAlgebra.induction_on with
  | of x =>
      exact numeratorMellinMap_raise_single K σ u hu r m x 1
  | add P Q hP hQ =>
      rw [add_mul, map_add, map_add, hP, hQ, mul_add]
  | smul c P hP =>
      rw [smul_mul_assoc, map_smulₛₗ, map_smulₛₗ, hP]
      simp only [smul_eq_mul]
      ring

def mellinPoleValue (r : Fin 5) (m : ℕ) (P : LaurentPolynomial R) : LSK K :=
  ((m - 1).factorial : LSK K)⁻¹ * numeratorMellinMap K σ r m P

theorem mellinPoleValue_add (r : Fin 5) (m : ℕ) (P Q : LaurentPolynomial R) :
    mellinPoleValue K σ r m (P + Q) =
      mellinPoleValue K σ r m P + mellinPoleValue K σ r m Q := by
  simp only [mellinPoleValue, map_add, mul_add]

theorem mellinPoleValue_smul (r : Fin 5) (m : ℕ) (c : R) (P : LaurentPolynomial R) :
    mellinPoleValue K σ r m (c • P) = σ c • mellinPoleValue K σ r m P := by
  rw [mellinPoleValue, map_smulₛₗ]
  simp only [mellinPoleValue, smul_eq_mul]
  ring

omit [CharZero K] in
theorem factorial_pole_scale (m : ℕ) (hm : 0 < m) :
    (m.factorial : LSK K) = (m : LSK K) * ((m - 1).factorial : LSK K) := by
  have hs : m - 1 + 1 = m := by omega
  have hf : m.factorial = m * (m - 1).factorial := by
    conv_lhs => rw [← hs, Nat.factorial_succ]
    rw [hs]
  simpa only [Nat.cast_mul] using congrArg (fun t : ℕ => (t : LSK K)) hf

include hu in
theorem mellinPoleValue_raise_one (r : Fin 5) (m : ℕ) (hm : 0 < m)
    (P : LaurentPolynomial R) :
    mellinPoleValue K σ r (m + 1) (P * torusPolynomial u) = mellinPoleValue K σ r m P := by
  have hm0 : (m : LSK K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  unfold mellinPoleValue
  rw [numeratorMellinMap_raise K σ u hu, Nat.add_sub_cancel,
    factorial_pole_scale K m hm, mul_inv]
  calc
    _ = ((m - 1).factorial : LSK K)⁻¹ *
          (((m : LSK K)⁻¹ * (m : LSK K)) * numeratorMellinMap K σ r m P) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hm0, one_mul]

include hu in
theorem mellinPoleValue_raise (r : Fin 5) (m k : ℕ) (hm : 0 < m)
    (P : LaurentPolynomial R) :
    mellinPoleValue K σ r (m + k) (P * torusPolynomial u ^ k) =
      mellinPoleValue K σ r m P := by
  induction k with
  | zero => simp [mellinPoleValue]
  | succ k ih =>
      rw [pow_succ, ← mul_assoc]
      have he : m + (k + 1) = (m + k) + 1 := by omega
      rw [he, mellinPoleValue_raise_one K σ u hu r (m + k) (by omega)]
      exact ih

variable [IsDomain R]

include hu in
/-- Independence is proved from the actual localization cross numerator
identity, rather than postulated on a formal presentation. -/
theorem mellinPoleValue_eq_of_fraction_eq (r : Fin 5) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) (P Q : LaurentPolynomial R)
    (h : poleLinearMap u m P = poleLinearMap u n Q) :
    mellinPoleValue K σ r m P = mellinPoleValue K σ r n Q := by
  have hc := (poleLinearMap_eq_iff_cross_multiply u m n P Q).1 h
  calc
    _ = mellinPoleValue K σ r (m + n) (P * torusPolynomial u ^ n) :=
      (mellinPoleValue_raise K σ u hu r m n hm P).symm
    _ = mellinPoleValue K σ r (n + m) (Q * torusPolynomial u ^ m) := by
      rw [hc, Nat.add_comm m n]
    _ = _ := mellinPoleValue_raise K σ u hu r n m hn Q

def mellinFunctionalValue (r : Fin 5) (g : FClosed u) : LSK K :=
  mellinPoleValue K σ r (vertexPresentation u g).1 (vertexPresentation u g).2

include hu in
theorem mellinFunctionalValue_eq_presentation (r : Fin 5) (g : FClosed u)
    (m : ℕ) (P : LaurentPolynomial R) (hm : 0 < m)
    (hg : (g : ActualRing u) = poleLinearMap u m P) :
    mellinFunctionalValue K σ u r g = mellinPoleValue K σ r m P := by
  have hs := vertexPresentation_spec u g
  exact mellinPoleValue_eq_of_fraction_eq K σ u hu r (vertexPresentation u g).1 m
    hs.1 hm (vertexPresentation u g).2 P (hs.2.2.symm.trans hg)

/-- An actual coordinate functional on the closed rational-function module. -/
def mellinFunctional (r : Fin 5) : FClosed u →ₛₗ[σ] LSK K where
  toFun := mellinFunctionalValue K σ u r
  map_add' g h := by
    let m := (vertexPresentation u g).1
    let n := (vertexPresentation u h).1
    let P := (vertexPresentation u g).2
    let Q := (vertexPresentation u h).2
    have hg := vertexPresentation_spec u g
    have hh := vertexPresentation_spec u h
    have he : ((g + h : FClosed u) : ActualRing u) =
        poleLinearMap u (m + n) (P * torusPolynomial u ^ n + Q * torusPolynomial u ^ m) := by
      rw [map_add, poleLinearMap_raise]
      rw [Nat.add_comm m n, poleLinearMap_raise]
      exact congrArg₂ (· + ·) hg.2.2 hh.2.2
    rw [mellinFunctionalValue_eq_presentation K σ u hu r (g + h) (m + n) _ (by omega) he,
      mellinPoleValue_add, mellinPoleValue_raise K σ u hu r m n hg.1]
    have hQ : mellinPoleValue K σ r (m + n) (Q * torusPolynomial u ^ m) =
        mellinPoleValue K σ r n Q := by
      rw [Nat.add_comm m n]
      exact mellinPoleValue_raise K σ u hu r n m hh.1 Q
    rw [hQ]
    rfl
  map_smul' c g := by
    have hg := vertexPresentation_spec u g
    have he : ((c • g : FClosed u) : ActualRing u) =
        poleLinearMap u (vertexPresentation u g).1 (c • (vertexPresentation u g).2) := by
      rw [map_smul, ← hg.2.2]
      rfl
    rw [mellinFunctionalValue_eq_presentation K σ u hu r (c • g) _ _ hg.1 he,
      mellinPoleValue_smul]
    rfl

theorem mellinFunctional_eq_presentation (r : Fin 5) (g : FClosed u)
    (m : ℕ) (P : LaurentPolynomial R) (hm : 0 < m)
    (hg : (g : ActualRing u) = poleLinearMap u m P) :
    mellinFunctional K σ u hu r g = mellinPoleValue K σ r m P :=
  mellinFunctionalValue_eq_presentation K σ u hu r g m P hm hg

omit [IsDomain R] in
theorem mellinPoleValue_factorial_single (r : Fin 5) (n : ℕ) (x : Exponents) :
    mellinPoleValue K σ r (n + 1)
      ((n.factorial : R) • AddMonoidAlgebra.single x 1) =
        canonicalMellinSeries K r ((n + 1 : ℕ) : ℤ) x := by
  have hn : (n.factorial : LSK K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  simp only [mellinPoleValue, Nat.add_sub_cancel, map_smulₛₗ, numeratorMellinMap_single,
    map_one, one_mul, map_natCast, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- Generator values use the actual nonnegative presentation and the proved
canonicalization identity. -/
theorem mellinFunctional_numeratorGenerator (r : Fin 5) (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n + 1) :
    mellinFunctional K σ u hu r
      ⟨numeratorGenerator u a n, numeratorGenerator_mem_closed u a n ha⟩ =
        mellinSeriesK K r ((n + 1 : ℕ) : ℤ) (fun i => (a i : ℤ)) := by
  have he : numeratorGenerator u a n = poleLinearMap u (n + 1)
      ((n.factorial : R) • AddMonoidAlgebra.single (latticeQ (fun i => (a i : ℤ))) 1) := by
    rw [numeratorGenerator_eq_canonical, canonicalNumeratorGenerator,
      factorialNumeratorMap_as_pole]
  rw [mellinFunctional_eq_presentation K σ u hu r _ (n + 1) _ (by omega) he,
    mellinPoleValue_factorial_single, canonicalMellinSeries]
  exact mellinSeriesK_canonicalize K r _ _ (fun i => Int.natCast_nonneg (a i))

theorem mellinFunctional_D_generator_zero (r : Fin 5) (i : Fin 5)
    (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ j, a j) ≤ n + 1) :
    mellinFunctional K σ u hu r (DClosed u i
      ⟨numeratorGenerator u a n, numeratorGenerator_mem_closed u a n ha⟩) = 0 := by
  let g : FClosed u := ⟨numeratorGenerator u a n, numeratorGenerator_mem_closed u a n ha⟩
  have hinc (j : Fin 6) : (∑ k, addNumeratorExponent a j k) ≤ (n + 1) + 1 := by
    rw [addNumeratorExponent_sum]
    omega
  let gi : FClosed u := ⟨numeratorGenerator u (addNumeratorExponent a i.castSucc) (n + 1),
    numeratorGenerator_mem_closed u _ _ (hinc i.castSucc)⟩
  let gj : FClosed u := ⟨numeratorGenerator u (addNumeratorExponent a 5) (n + 1),
    numeratorGenerator_mem_closed u _ _ (hinc 5)⟩
  have he : DClosed u i g = ((a i.castSucc : R) - (a 5 : R)) • g + u • (gi - gj) := by
    apply Subtype.ext
    change actualD u i (numeratorGenerator u a n) =
      ((a i.castSucc : R) - (a 5 : R)) • numeratorGenerator u a n + u •
        (numeratorGenerator u (addNumeratorExponent a i.castSucc) (n + 1) -
          numeratorGenerator u (addNumeratorExponent a 5) (n + 1))
    simpa only [Algebra.smul_def] using actualD_numeratorGenerator u i a n
  change mellinFunctional K σ u hu r (DClosed u i g) = 0
  rw [he, map_add, map_smulₛₗ, map_smulₛₗ]
  have hg := mellinFunctional_numeratorGenerator K σ u hu r a n ha
  have hi := mellinFunctional_numeratorGenerator K σ u hu r
    (addNumeratorExponent a i.castSucc) (n + 1) (hinc i.castSucc)
  have hj := mellinFunctional_numeratorGenerator K σ u hu r
    (addNumeratorExponent a 5) (n + 1) (hinc 5)
  change mellinFunctional K σ u hu r g = _ at hg
  change mellinFunctional K σ u hu r gi = _ at hi
  change mellinFunctional K σ u hu r gj = _ at hj
  rw [map_sub (mellinFunctional K σ u hu r), hg, hi, hj, hu]
  simp only [smul_eq_mul, map_sub, map_natCast]
  rw [addNumeratorExponent_cast, addNumeratorExponent_cast]
  have hp (j : Fin 6) : (fun k => (a k : ℤ)) + Pi.single j 1 =
      increment (fun k => (a k : ℤ)) j := by
    rw [increment_eq_add_standardExponent]
    congr 1
    ext k
    simp [standardExponent, Pi.single_apply]
  rw [hp, hp, mul_sub]
  have hd := mellinSeriesK_derivative_relation K r ((n + 1 : ℕ) : ℤ)
    (fun k => (a k : ℤ)) i.castSucc 5
  push_cast at hd ⊢
  simpa only [sub_eq_add_neg, add_assoc] using hd

/-- Every actual logarithmic derivative image has zero Mellin value. -/
theorem mellinFunctional_D_zero (r : Fin 5) (i : Fin 5) (g : FClosed u) :
    mellinFunctional K σ u hu r (DClosed u i g) = 0 := by
  have hkill : ∀ (z : ActualRing u) (hz : z ∈ FClosed u),
      mellinFunctional K σ u hu r (DClosed u i ⟨z, hz⟩) = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨a, n, ha, rfl⟩ := hz
        exact mellinFunctional_D_generator_zero K σ u hu r i a n ha
    | zero =>
        change mellinFunctional K σ u hu r (DClosed u i 0) = 0
        rw [map_zero, map_zero]
    | add z w hz hw ihz ihw =>
        change mellinFunctional K σ u hu r (DClosed u i
          (⟨z, hz⟩ + ⟨w, hw⟩ : FClosed u)) = 0
        rw [map_add, map_add, ihz, ihw, add_zero]
    | smul c z hz ihz =>
        change mellinFunctional K σ u hu r (DClosed u i (c • (⟨z, hz⟩ : FClosed u))) = 0
        rw [map_smul, map_smulₛₗ, ihz, smul_zero]
  exact hkill g g.property

theorem exactSubmodule_le_mellinFunctional_ker (r : Fin 5) :
    exactSubmodule u ≤ (mellinFunctional K σ u hu r).ker := by
  apply iSup_le
  intro i
  rintro g ⟨h, rfl⟩
  exact mellinFunctional_D_zero K σ u hu r i h

/-- The functional is now defined on the literal closed residue quotient. -/
def mellinQuotientFunctional (r : Fin 5) : ClosedResidueQuotient u →ₛₗ[σ] LSK K :=
  (exactSubmodule u).liftQ (mellinFunctional K σ u hu r)
    (exactSubmodule_le_mellinFunctional_ker K σ u hu r)

@[simp] theorem mellinQuotientFunctional_mk (r : Fin 5) (g : FClosed u) :
    mellinQuotientFunctional K σ u hu r (Submodule.Quotient.mk g) =
      mellinFunctional K σ u hu r g := rfl

def mellinQuotientVector : ClosedResidueQuotient u →ₛₗ[σ] (Fin 5 → LSK K) where
  toFun g r := mellinQuotientFunctional K σ u hu r g
  map_add' g h := by
    funext r
    exact map_add (mellinQuotientFunctional K σ u hu r) g h
  map_smul' c g := by
    funext r
    exact map_smulₛₗ (mellinQuotientFunctional K σ u hu r) c g

theorem mellinFunctional_factorialPole (r : Fin 5) (n : ℕ) :
    mellinFunctional K σ u hu r
      ⟨factorialPole u n, FInterior_le_FClosed u (factorialPole_mem_interior u n)⟩ =
        mellinSeriesK K r ((n + 1 : ℕ) : ℤ) zeroExponent := by
  have h := mellinFunctional_numeratorGenerator K σ u hu r (fun _ => 0) n (by simp)
  have he : numeratorGenerator u (fun _ => 0) n = factorialPole u n := by
    change algebraMap (LaurentPolynomial R) (ActualRing u) (AddMonoidAlgebra.single 0 1) *
      factorialPole u n = factorialPole u n
    simp [← AddMonoidAlgebra.one_def]
  have hz : (fun _ : Fin 6 => (0 : ℤ)) = zeroExponent := rfl
  simpa only [he, Nat.cast_zero, hz] using h

def gammaQuotientFamily (c : Fin 5) : ClosedResidueQuotient u :=
  Submodule.Quotient.mk
    (⟨factorialPole u c.val, FInterior_le_FClosed u (factorialPole_mem_interior u c.val)⟩ :
      FClosed u)

theorem mellinQuotientVector_gamma (c : Fin 5) :
    mellinQuotientVector K σ u hu (gammaQuotientFamily u c) =
      fun r : Fin 5 => mellinSeriesK K r (c.val + 1 : ℤ) zeroExponent := by
  funext r
  change mellinFunctional K σ u hu r
      ⟨factorialPole u c.val, FInterior_le_FClosed u (factorialPole_mem_interior u c.val)⟩ =
    mellinSeriesK K r ((c.val : ℤ) + 1) zeroExponent
  simpa only [Nat.cast_add, Nat.cast_one] using
    mellinFunctional_factorialPole K σ u hu r c.val

include hu in
/-- Injectivity of the actual scalar embedding and the actual nonzero
Mellin determinant prove independence of the five literal residue classes. -/
theorem gammaQuotientFamily_independent (hσ : Function.Injective σ) :
    LinearIndependent R (gammaQuotientFamily u) := by
  rw [linearIndependent_iff']
  intro s c hc j hj
  have he := congrArg (mellinQuotientVector K σ u hu) hc
  simp only [map_sum, map_smulₛₗ, map_zero, mellinQuotientVector_gamma] at he
  have h := (linearIndependent_iff'.1 (interiorMellinMatrixK_columns_independent K))
    s (fun i => σ (c i)) he j hj
  exact hσ (h.trans (map_zero σ).symm)

end CommonPole

/-- The requested characteristic-zero family over the actual parameter ring. -/
def parameterMellinFunctional (r : Fin 5) :
    FClosed (Parameter.u : Parameter.ParameterRing K) →ₛₗ[parameterSeriesMap K] LSK K :=
  mellinFunctional K (parameterSeriesMap K) Parameter.u (parameterSeriesMap_u K) r

def parameterMellinQuotientFunctional (r : Fin 5) :
    ClosedResidueQuotient (Parameter.u : Parameter.ParameterRing K)
      →ₛₗ[parameterSeriesMap K] LSK K :=
  mellinQuotientFunctional K (parameterSeriesMap K) Parameter.u (parameterSeriesMap_u K) r

theorem parameterGammaQuotientFamily_independent :
    LinearIndependent (Parameter.ParameterRing K)
      (gammaQuotientFamily (Parameter.u : Parameter.ParameterRing K)) :=
  gammaQuotientFamily_independent K (parameterSeriesMap K) Parameter.u
    (parameterSeriesMap_u K) (parameterSeriesMap_injective K)

end WPResidueQuotient.MellinFactors
