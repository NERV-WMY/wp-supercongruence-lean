import WPCompletedCartier.CartierConstruction
import WPCompletedCartier.InteriorConstruction
import WPCompletedCartier.LowPoleProjection
import WPCompletedCartier.ScalarBridge

namespace WPCompletedCartier.ActualMatrix

noncomputable section
open scoped BigOperators
open WPResidueQuotient WPResidueQuotient.Adic
open WPResidueQuotient.ActualCompletion
open WPCompletedCartier.LowPoleProjection WPCompletedCartier.ScalarBridge
open WPCartierFinite

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

local notation "u" => Parameter.integralTenth p hp
local notation "coordinates" => constantCoordinatesZp p hp hp7 hp19

/-- The eleven coordinates are obtained by applying the constructed operator to
the actual split section in the completed closed module. -/
def actual11 : (Fin 11 → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 11 → ℤ_[p]) :=
  (coordinates).comp ((CartierConstruction.completedCartier p hp).comp
    (constantSectionZp p hp hp7 hp19))

/-- The restriction to the five original interior coordinate positions. -/
def actual5 : (Fin 5 → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 5 → ℤ_[p]) :=
  moduleInteriorProjection.comp ((actual11 p hp hp7 hp19).comp moduleInteriorInclusion)

def actualGammaMatrix : Matrix (Fin 5) (Fin 5) ℤ_[p] :=
  fun i r => actual5 p hp hp7 hp19 (Pi.single r 1) i

set_option maxHeartbeats 1600000 in
theorem constantSectionZp_ofModule (c : Fin 11 → ℤ_[p]) :
    constantSectionZp p hp hp7 hp19 c =
      ofModule (p : ℤ_[p]) (Actual.elevenSection u c) := by
  have hc : (Adic.completePiEquiv (p : ℤ_[p])).symm
      ((PadicScalarCompletion.scalarPiEquiv p (Fin 11)).symm c) =
      ofModule (p : ℤ_[p]) c := by
    change (PadicScalarCompletion.finiteScalarEquiv p 11).symm c = _
    apply (PadicScalarCompletion.finiteScalarEquiv p 11).injective
    rw [LinearEquiv.apply_symm_apply, PadicScalarCompletion.finiteScalarEquiv_ofModule]
  have hm : (ActualSpecialization.integralConstantClosedSplitEquiv p hp hp7 hp19).symm
      (0, c) =
      Actual.elevenSection u c := by
    rw [ActualSpecialization.integralConstantClosedSplitEquiv,
      ActualSpecialization.closedSplitFromQuotient_symm_apply,
      Submodule.coe_zero, zero_add]
  let L : Adic.Completion (p : ℤ_[p]) (Fin 11 → ℤ_[p]) →ₗ[ℤ_[p]]
      Adic.Completion (p : ℤ_[p]) (FClosed u) :=
    @Adic.coordinateSection ℤ_[p] inferInstance (FClosed u) (exactSubmodule u)
      (Fin 11 → ℤ_[p]) (FClosed u).addCommGroup (FClosed u).module
      (exactSubmodule u).addCommGroup (exactSubmodule u).module
      (inferInstance : AddCommGroup (Fin 11 → ℤ_[p]))
      (inferInstance : Module ℤ_[p] (Fin 11 → ℤ_[p])) (p : ℤ_[p])
      (ActualSpecialization.integralConstantClosedSplitEquiv p hp hp7 hp19)
  have hmap : L (ofModule (p : ℤ_[p]) c) =
      ofModule (p : ℤ_[p]) (Actual.elevenSection u c) := by
    dsimp only [L]
    rw [Adic.coordinateSection_eq_completeMap, Adic.completeMap_ofModule]
    exact congrArg (ofModule (p : ℤ_[p])) hm
  have hs := congrArg L hc
  simpa only [L, constantSectionZp, constantCompletedSection, Adic.scalarCoordinateSection,
    LinearMap.comp_apply, LinearEquiv.coe_coe] using hs.trans hmap

theorem actual11_gamma_column (r : Fin 5) :
    actual11 p hp hp7 hp19 (Pi.single (Fin.castAdd 6 r) 1) =
      coordinates (CartierConstruction.cartier p hp (Actual.gammaClosedElement u r)) := by
  change coordinates (CartierConstruction.completedCartier p hp
    (constantSectionZp p hp hp7 hp19 (Pi.single (Fin.castAdd 6 r) 1))) = _
  rw [constantSectionZp_ofModule, Actual.elevenSection_single,
    Actual.elevenClosedElement_left, CartierConstruction.completedCartier_ofModule]

theorem interiorInclusion_single (r : Fin 5) :
    moduleInteriorInclusion (Pi.single r (1 : ℤ_[p])) =
      Pi.single (Fin.castAdd 6 r) 1 := by
  ext j
  refine Fin.addCases (m := 5) (n := 6) (fun i => ?_) (fun i => ?_) j
  · simp [moduleInteriorInclusion, Adic.moduleExactInclusion, Adic.elevenSplit,
      Pi.single_apply, Fin.ext_iff]
  · have hr : r.val < 5 := r.isLt
    simp [moduleInteriorInclusion, Adic.moduleExactInclusion, Adic.elevenSplit,
      Pi.single_apply, Fin.ext_iff]
    omega

theorem actualGammaMatrix_column (i r : Fin 5) :
    actualGammaMatrix p hp hp7 hp19 i r =
      coordinates (CartierConstruction.cartier p hp (Actual.gammaClosedElement u r))
        (Fin.castAdd 6 i) := by
  change moduleInteriorProjection
    (actual11 p hp hp7 hp19 (moduleInteriorInclusion (Pi.single r 1))) i = _
  rw [interiorInclusion_single, actual11_gamma_column]
  rfl

theorem actual11_preserves_interior (c : Fin 5 → ℤ_[p]) :
    actual11 p hp hp7 hp19 (moduleInteriorInclusion c) ∈ Actual.interiorCoordinates ℤ_[p] := by
  have hzero : ∀ j : Fin 6, moduleInteriorInclusion c (Fin.natAdd 5 j) = 0 := by
    intro j
    change (if h : 5 + j.val < 5 then c ⟨5 + j.val, h⟩ else 0) = 0
    rw [dif_neg (by omega)]
  let g : FInterior u :=
    ⟨(Actual.elevenSection u (moduleInteriorInclusion c) : ActualRing u),
      Actual.elevenSection_interior_of_boundary_zero u (moduleInteriorInclusion c) hzero⟩
  have hs : constantSectionZp p hp hp7 hp19 (moduleInteriorInclusion c) =
      completedInteriorInclusion u (p : ℤ_[p]) (ofModule (p : ℤ_[p]) g) := by
    rw [constantSectionZp_ofModule]
    change _ = Adic.completeMap (p : ℤ_[p]) (actualInteriorInclusion u)
      (ofModule (p : ℤ_[p]) g)
    rw [Adic.completeMap_ofModule]
    congr 1
  have hi := congrArg (fun L => L (ofModule (p : ℤ_[p]) g))
    (InteriorConstruction.completedCartier_intertwines p hp)
  change completedInteriorInclusion u (p : ℤ_[p])
      (InteriorConstruction.completedCartier p hp (ofModule (p : ℤ_[p]) g)) =
    CartierConstruction.completedCartier p hp
      (completedInteriorInclusion u (p : ℤ_[p]) (ofModule (p : ℤ_[p]) g)) at hi
  rw [← constantInteriorZp_image p hp hp7 hp19]
  refine ⟨CartierConstruction.completedCartier p hp
    (constantSectionZp p hp hp7 hp19 (moduleInteriorInclusion c)), ?_, rfl⟩
  rw [hs, ← hi]
  exact LinearMap.mem_range_self _ _

/-- This intertwining certifies that the five coordinates form the actual
interior restriction of the eleven-coordinate operator. -/
theorem actual5_inclusion (c : Fin 5 → ℤ_[p]) :
    moduleInteriorInclusion (actual5 p hp hp7 hp19 c) =
      actual11 p hp hp7 hp19 (moduleInteriorInclusion c) := by
  have hc : actual11 p hp hp7 hp19 (moduleInteriorInclusion c) ∈
      LinearMap.range (moduleInteriorInclusion (R := ℤ_[p])) := by
    rw [moduleInteriorInclusion_range]
    exact actual11_preserves_interior p hp hp7 hp19 c
  obtain ⟨a, ha⟩ := hc
  change moduleInteriorInclusion
    (moduleInteriorProjection (actual11 p hp hp7 hp19 (moduleInteriorInclusion c))) = _
  rw [← ha]
  have hl := DFunLike.congr_fun (moduleInteriorProjection_leftInverse (R := ℤ_[p])) a
  change moduleInteriorProjection (moduleInteriorInclusion a) = a at hl
  rw [hl]

/-- This identity derives the coordinate comparison from the actual integral
and field quotient sections, rather than from a supplied matrix comparison. -/
theorem integralCoordinates_cast (g : FClosed u) :
    (fun j => (ActualSpecialization.integralConstantCoordinates p hp hp7 hp19 g j : ℚ_[p])) =
      (ActualSpecialization.tenthQuotientEquiv ℚ_[p]).symm
        (ActualSpecialization.integralConstantQuotientMap p hp (Submodule.Quotient.mk g)) := by
  let c := ActualSpecialization.integralConstantCoordinates p hp hp7 hp19 g
  have hg : (Submodule.Quotient.mk g : ClosedResidueQuotient u) =
      Actual.elevenQuotientSection u c := by
    change Submodule.Quotient.mk g =
      Actual.elevenQuotientSection u
        ((ActualSpecialization.integralConstantQuotientEquiv p hp hp7 hp19).symm
          (Submodule.Quotient.mk g))
    rw [← ActualSpecialization.integralConstantQuotientEquiv_apply]
    exact (LinearEquiv.apply_symm_apply _ _).symm
  rw [hg, ActualSpecialization.integralConstantQuotientMap_section,
    ← ActualSpecialization.tenthQuotientEquiv_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- The finite canonical coefficient map reconstructs the actual Laurent
polynomial, including its full exponent lattice. -/
theorem canonicalCoefficients_reconstruct (P : WPCartierFinite.LaurentPolynomial) :
    (∑ a ∈ (canonicalCoefficients P).support,
      canonicalCoefficients P a • AddMonoidAlgebra.single
        (qSix (fun j => (a j : ℤ))) (1 : ℚ)) = P := by
  classical
  have hs : (canonicalCoefficients P).support = P.coeff.support.image canonicalSixNat :=
    Finsupp.mapDomain_support_of_injective canonicalSixNat_injective P.coeff
  rw [hs]
  rw [Finset.sum_image (fun x _ y _ h => canonicalSixNat_injective h)]
  simp only [canonicalCoefficients_apply,
    qSix_canonicalSixNat, AddMonoidAlgebra.smul_single', mul_one]
  simpa only [Finsupp.sum] using AddMonoidAlgebra.sum_coeff_single P

theorem canonicalCoefficients_degree (P : WPCartierFinite.LaurentPolynomial) (k : ℕ)
    (hP : SupportBound P k) (a : SixExponent) (ha : a ∈ (canonicalCoefficients P).support) :
    exponentDegree a ≤ k :=
  canonicalCoefficients_support_degree P k hP a ha

def rationalLaurentClosed (k : ℕ) (P : WPCartierFinite.LaurentPolynomial)
    (hP : SupportBound P k) : FClosed (1 / 10 : ℚ) :=
  ⟨poleLinearMap (1 / 10 : ℚ) (k + 1) P,
    by
      rw [pole_as_factorialNumeratorMap]
      apply factorialNumeratorMap_mem_closed
      apply (numeratorFiltration ℚ (k + 1)).smul_mem
      rw [mem_numeratorFiltration]
      intro x hx
      rw [NumericalTerms.canonicalDegreeNat_eq]
      exact (hP x hx).trans (Nat.le_succ k)⟩

theorem rationalLaurentClass_canonical (k : ℕ) (P : WPCartierFinite.LaurentPolynomial)
    (hP : SupportBound P k) :
    (Submodule.Quotient.mk (rationalLaurentClosed k P hP) : NumericalResidue) =
      actualPolynomialClass k (canonicalCoefficients P)
        (fun a ha => canonicalCoefficients_degree P k hP a ha) := by
  classical
  let s : FClosed (1 / 10 : ℚ) :=
    ∑ a ∈ (canonicalCoefficients P).support, if ha : a ∈ (canonicalCoefficients P).support then
      canonicalCoefficients P a • rawNumeratorClosed a k
        (canonicalCoefficients_degree P k hP a ha)
      else 0
  have hs : rationalLaurentClosed k P hP = s := by
    apply Subtype.ext
    change poleLinearMap (1 / 10 : ℚ) (k + 1) P = s.val
    rw [← canonicalCoefficients_reconstruct P, map_sum]
    dsimp only [s]
    rw [Submodule.coe_sum]
    change _ = ∑ a ∈ (canonicalCoefficients P).support,
      (if ha : a ∈ (canonicalCoefficients P).support then
        canonicalCoefficients P a • rawNumeratorClosed a k
          (canonicalCoefficients_degree P k hP a ha)
        else 0 : FClosed (1 / 10 : ℚ)).val
    apply Finset.sum_congr rfl
    intro a ha
    rw [dif_pos ha, map_smul, Submodule.coe_smul, rawNumeratorClosed_value]
    rfl
  rw [hs]
  change (exactSubmodule (1 / 10 : ℚ)).mkQ s = _
  dsimp only [s, actualPolynomialClass]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [dif_pos ha, dif_pos ha, map_smul, Submodule.mkQ_apply]
  exact congrArg (fun q : NumericalResidue => canonicalCoefficients P a • q)
    (rawNumeratorClass_is_actual a k (canonicalCoefficients_degree P k hP a ha)).symm

def gammaNumerator (r : Fin 5) : numeratorFiltration ℤ_[p] (r.val + 1) :=
  ⟨1, one_mem_numeratorFiltration _⟩

theorem gammaNumerator_toClosed (r : Fin 5) :
    CartierConstruction.numeratorToClosed p hp r.val (gammaNumerator p r) =
      Actual.gammaClosedElement u r := by
  apply Subtype.ext
  simp only [CartierConstruction.numeratorToClosed, LinearMap.codRestrict_apply,
    LinearMap.comp_apply, Submodule.subtype_apply, gammaNumerator,
    factorialNumeratorMap_apply, map_one, one_mul, Actual.gammaClosedElement]

include hp in
omit [Fact p.Prime] in
theorem height_low (r : Fin 5) : ActualSeries.height p r.val = 1 := by
  rw [ActualSeries.height, Nat.div_eq_of_lt (by omega)]

def gammaFiniteTerm (r : Fin 5) (k : ℕ) : FClosed u :=
  NumericalTerms.closedTerm p hp 1 (r.val + 1) 1 k (by omega)
    (by simpa only [Nat.mul_one] using (show r.val + 1 ≤ p by omega))
    (one_mem_numeratorFiltration _)

theorem selectedNumerator_one (r : Fin 5) (k : ℕ) :
    NumericalTerms.selectedNumerator p hp 1 (r.val + 1) 1 k =
      NumericalTerms.finiteNumerator p hp k (r.val + 1) := by
  simp only [NumericalTerms.selectedNumerator, NumericalTerms.finiteNumerator,
    mul_comm, mul_one]

theorem padicLaurentMap_eq_toField :
    IntegralTransport.laurentMap (IntegralTransport.padicCoefficientMap p) =
      NumericalTerms.toField p := by
  have hcoeff : IntegralTransport.padicCoefficientMap p = PadicInt.Coe.ringHom := by
    ext z
    rfl
  exact congrArg (fun φ : ℤ_[p] →+* ℚ_[p] =>
    AddMonoidAlgebra.mapRingHom WPResidueQuotient.Exponents φ) hcoeff

theorem gammaFiniteTerm_transport (r : Fin 5) (k : ℕ) :
    IntegralTransport.closedMap (IntegralTransport.padicCoefficientMap p) u (1 / 10 : ℚ_[p])
        (ParameterSpecialization.integralTenth_in_field p hp) (gammaFiniteTerm p hp r k) =
      ((r.val.factorial : ℚ_[p]) * (p : ℚ_[p]) ^ k) •
        IntegralTransport.closedMap (algebraMap ℚ ℚ_[p]) (1 / 10 : ℚ) (1 / 10 : ℚ_[p])
          (ActualSpecialization.rationalConstant_parameter_map ℚ_[p])
          (rationalLaurentClosed k
            (WPCartierFinite.finiteNumerator p (Fact.out : p.Prime).pos k (r.val + 1))
            (finiteNumerator_support p (Fact.out : p.Prime).pos k (r.val + 1)
              (by omega) (by omega))) := by
  apply Subtype.ext
  simp only [IntegralTransport.closedMap_coe, Submodule.coe_smul]
  change IntegralTransport.actualMap (IntegralTransport.padicCoefficientMap p) u
    (1 / 10 : ℚ_[p]) (ParameterSpecialization.integralTenth_in_field p hp)
      (NumericalTerms.generatorTerm p hp 1 (r.val + 1) 1 k) = _
  simp only [NumericalTerms.generatorTerm, IntegralTransport.actualMap_smul,
    factorialNumeratorMap_apply, map_mul, IntegralTransport.actualMap_laurent,
    IntegralTransport.actualMap_factorialPole, selectedNumerator_one, Nat.add_sub_cancel_left]
  rw [padicLaurentMap_eq_toField]
  simp only [IntegralTransport.padicCoefficientMap, PadicInt.algebraMap_apply]
  change (NumericalTerms.termScalar p hp (r.val + 1) 1 k : ℚ_[p]) •
    (algebraMap (WPResidueQuotient.LaurentPolynomial ℚ_[p]) (ActualRing (1 / 10 : ℚ_[p]))
      (NumericalTerms.toField p (NumericalTerms.finiteNumerator p hp k (r.val + 1))) *
        factorialPole (1 / 10 : ℚ_[p]) k) = _
  rw [NumericalTerms.finiteNumerator_scalar_change]
  have hs : (NumericalTerms.termScalar p hp (r.val + 1) 1 k : ℚ_[p]) *
      (k.factorial : ℚ_[p]) = (r.val.factorial : ℚ_[p]) * (p : ℚ_[p]) ^ k := by
    rw [NumericalTerms.termScalar_coe p hp _ _ _ (by omega)]
    simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, div_one]
    field_simp [show (k.factorial : ℚ_[p]) ≠ 0 from
      by exact_mod_cast Nat.factorial_ne_zero k]
  have hf (P : WPResidueQuotient.LaurentPolynomial ℚ_[p]) :
      algebraMap (WPResidueQuotient.LaurentPolynomial ℚ_[p])
          (ActualRing (1 / 10 : ℚ_[p])) P * factorialPole (1 / 10 : ℚ_[p]) k =
        (k.factorial : ℚ_[p]) • poleLinearMap (1 / 10 : ℚ_[p]) (k + 1) P := by
    change factorialNumeratorMap (1 / 10 : ℚ_[p]) k P = _
    rw [factorialNumeratorMap_as_pole, map_smul]
  rw [hf, smul_smul, hs]
  congr 1
  change poleLinearMap (1 / 10 : ℚ_[p]) (k + 1)
    (NumericalTerms.fromRational p _) =
      IntegralTransport.actualMap (algebraMap ℚ ℚ_[p]) (1 / 10 : ℚ) (1 / 10 : ℚ_[p])
        (ActualSpecialization.rationalConstant_parameter_map ℚ_[p])
        (poleLinearMap (1 / 10 : ℚ) (k + 1) _)
  simp only [poleLinearMap_apply, map_mul, map_pow,
    IntegralTransport.actualMap_laurent, IntegralTransport.actualMap_inverseF]
  rfl

theorem gammaFiniteTerm_quotient (r k : Fin 5) :
    ActualSpecialization.integralConstantQuotientMap p hp
        (Submodule.Quotient.mk (gammaFiniteTerm p hp r k.val)) =
      ((r.val.factorial : ℚ_[p]) * (p : ℚ_[p]) ^ k.val) •
        ActualSpecialization.rationalConstantMap ℚ_[p]
          (actualPolynomialClass k.val (actualFiniteCoefficients p (Fact.out : p.Prime).pos k r)
            (fun a ha => (actualFiniteCoefficients_support p
              (Fact.out : p.Prime).pos hp k r a ha).1)) := by
  change IntegralTransport.quotientMap (IntegralTransport.padicCoefficientMap p) u
    (1 / 10 : ℚ_[p]) (ParameterSpecialization.integralTenth_in_field p hp)
      (Submodule.Quotient.mk _) = _
  rw [IntegralTransport.quotientMap_mk, gammaFiniteTerm_transport]
  change (exactSubmodule (1 / 10 : ℚ_[p])).mkQ (_ • _) = _
  rw [map_smul]
  congr 1
  change ActualSpecialization.rationalConstantMap ℚ_[p]
    (Submodule.Quotient.mk (rationalLaurentClosed _ _ _)) = _
  rw [rationalLaurentClass_canonical]
  rfl

def gammaFiniteSum (r : Fin 5) : FClosed u := ∑ k : Fin 5, gammaFiniteTerm p hp r k.val

theorem gammaFiniteSum_quotient (r : Fin 5) :
    ActualSpecialization.integralConstantQuotientMap p hp
        (Submodule.Quotient.mk (gammaFiniteSum p hp r)) =
      (r.val.factorial : ℚ_[p]) • ActualSpecialization.rationalConstantMap ℚ_[p]
        (actualFiniteColumn p (Fact.out : p.Prime).pos hp r) := by
  change ActualSpecialization.integralConstantQuotientMap p hp
    ((exactSubmodule u).mkQ (∑ k : Fin 5, gammaFiniteTerm p hp r k.val)) = _
  rw [map_sum, map_sum]
  simp only [Submodule.mkQ_apply]
  simp_rw [gammaFiniteTerm_quotient]
  simp only [actualFiniteColumn, map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  let q : ClosedResidueQuotient (1 / 10 : ℚ_[p]) :=
    ActualSpecialization.rationalConstantMap ℚ_[p]
      (actualPolynomialClass k.val (actualFiniteCoefficients p (Fact.out : p.Prime).pos k r)
        (fun a ha => (actualFiniteCoefficients_support p
          (Fact.out : p.Prime).pos hp k r a ha).1))
  have ht : (p : ℚ_[p]) ^ k.val • q = (p : ℚ) ^ k.val • q := by
    simpa only [map_pow, map_natCast] using
      (IsScalarTower.algebraMap_smul ℚ_[p] ((p : ℚ) ^ k.val) q)
  exact (mul_smul (r.val.factorial : ℚ_[p]) ((p : ℚ_[p]) ^ k.val) q).trans
    (congrArg (fun x : ClosedResidueQuotient (1 / 10 : ℚ_[p]) =>
      (r.val.factorial : ℚ_[p]) • x) ht)

theorem gamma_tail_mem (r : Fin 5) :
    CartierConstruction.cartier p hp (Actual.gammaClosedElement u r) -
      ofModule (p : ℤ_[p]) (gammaFiniteSum p hp r) ∈
        powerSubmodule (M := ActualSeries.Completed p hp) (p : ℤ_[p]) 5 := by
  have ht := CartierConstruction.generatorImage_sub_five_mem p hp r.val (gammaNumerator p r)
  rw [← CartierConstruction.cartier_numerator, gammaNumerator_toClosed] at ht
  simp only [height_low p hp r] at ht
  convert ht using 1
  congr 1

theorem gammaFiniteSum_coordinates (i r : Fin 5) :
    (ActualSpecialization.integralConstantCoordinates p hp hp7 hp19
        (gammaFiniteSum p hp r) (Fin.castAdd 6 i) : ℚ_[p]) =
      (r.val.factorial : ℚ_[p]) * finiteMatrixQp p i r / (i.val.factorial : ℚ_[p]) := by
  let v : LowVector := fun j => finiteCartierArray p (Fact.out : p.Prime).pos r j /
    (j.val.factorial : ℚ)
  have hv : factorialDiagonal v = finiteCartierArray p (Fact.out : p.Prime).pos r := by
    ext j
    dsimp [factorialDiagonal, v]
    field_simp [show (j.val.factorial : ℚ) ≠ 0 from
      by exact_mod_cast Nat.factorial_ne_zero j.val]
  have hc : actualFiniteColumn p (Fact.out : p.Prime).pos hp r = numericalGammaSection v := by
    rw [← finiteCartierArray_actual_column, ← hv, actual_factorial_change]
  have hcoords := congrFun (integralCoordinates_cast p hp hp7 hp19
    (gammaFiniteSum p hp r)) (Fin.castAdd 6 i)
  rw [gammaFiniteSum_quotient, hc] at hcoords
  change _ = (ActualSpecialization.tenthQuotientEquiv ℚ_[p]).symm
    ((r.val.factorial : ℚ_[p]) • ActualSpecialization.rationalConstantMap ℚ_[p]
      (Actual.elevenQuotientSection (1 / 10 : ℚ) (Fin.append v (fun _ : Fin 6 => 0))))
        (Fin.castAdd 6 i) at hcoords
  rw [map_smul, ActualSpecialization.rationalConstantMap_elevenSection,
    ← ActualSpecialization.tenthQuotientEquiv_apply, LinearEquiv.symm_apply_apply] at hcoords
  simpa only [Pi.smul_apply, smul_eq_mul, Fin.append_left, v, Rat.cast_div,
    eq_ratCast, Rat.cast_natCast, finiteMatrixQp, coefficientMatrix, mul_div_assoc] using hcoords

/-- The infinite actual operator has the finite displayed column modulo p^5,
before changing the Gamma basis to the raw pole basis. -/
theorem actualGammaMatrix_congruence (i r : Fin 5) :
    QpCongruent p 5 (actualGammaMatrix p hp hp7 hp19 i r : ℚ_[p])
      ((r.val.factorial : ℚ_[p]) * finiteMatrixQp p i r / (i.val.factorial : ℚ_[p])) := by
  obtain ⟨z, hz⟩ := (mem_powerSubmodule _ _ _).mp (gamma_tail_mem p hp r)
  refine ⟨coordinates z (Fin.castAdd 6 i), ?_⟩
  have he := congrArg (fun x : ActualSeries.Completed p hp =>
    (coordinates x (Fin.castAdd 6 i) : ℚ_[p])) hz
  simp only [map_smul, map_sub, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
    PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast,
    PadicInt.coe_sub, constantCoordinatesZp_ofModule] at he
  rw [actualGammaMatrix_column, ← gammaFiniteSum_coordinates p hp hp7 hp19 i r]
  exact he.symm

def inverseFactorialZp (i : Fin 5) : ℤ_[p] :=
  ↑(lowPole_factorial_isUnit p hp i).unit⁻¹

theorem inverseFactorialZp_mul (i : Fin 5) :
    inverseFactorialZp p hp i * (i.val.factorial : ℤ_[p]) = 1 :=
  (lowPole_factorial_isUnit p hp i).val_inv_mul

@[simp] theorem inverseFactorialZp_coe (i : Fin 5) :
    (inverseFactorialZp p hp i : ℚ_[p]) = (i.val.factorial : ℚ_[p])⁻¹ := by
  apply mul_right_cancel₀ (show (i.val.factorial : ℚ_[p]) ≠ 0 from
    by exact_mod_cast Nat.factorial_ne_zero i.val)
  rw [inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero i.val)]
  have h := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) (inverseFactorialZp_mul p hp i)
  simpa only [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_one] using h

def factorialMatrixZp : Matrix (Fin 5) (Fin 5) ℤ_[p] :=
  Matrix.diagonal (fun i => (i.val.factorial : ℤ_[p]))

def inverseFactorialMatrixZp : Matrix (Fin 5) (Fin 5) ℤ_[p] :=
  Matrix.diagonal (inverseFactorialZp p hp)

/-- Literal H conjugation of the constructed Gamma-coordinate matrix. -/
def actualPhiMatrix : Matrix (Fin 5) (Fin 5) ℤ_[p] :=
  factorialMatrixZp p * actualGammaMatrix p hp hp7 hp19 * inverseFactorialMatrixZp p hp

theorem actualPhiMatrix_entries (i r : Fin 5) :
    actualPhiMatrix p hp hp7 hp19 i r =
      (i.val.factorial : ℤ_[p]) * actualGammaMatrix p hp hp7 hp19 i r *
        inverseFactorialZp p hp r := by
  simp only [actualPhiMatrix, factorialMatrixZp, inverseFactorialMatrixZp,
    Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem actualPhiMatrix_congruence (i r : Fin 5) :
    QpCongruent p 5 (actualPhiMatrix p hp hp7 hp19 i r : ℚ_[p])
      (finiteMatrixQp p i r) := by
  have h := qpCongruent_mul_integral p 5
    (qpCongruent_mul_integral p 5 (actualGammaMatrix_congruence p hp hp7 hp19 i r)
      (inverseFactorialZp p hp r)) (i.val.factorial : ℤ_[p])
  have hr : (r.val.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r.val
  have hi : (i.val.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i.val
  simp only [PadicInt.coe_natCast, inverseFactorialZp_coe] at h
  have hnormalized : Eq (α := ℚ_[p])
      (((r.val.factorial : ℚ_[p]) * finiteMatrixQp p i r / (i.val.factorial : ℚ_[p]) *
        (r.val.factorial : ℚ_[p])⁻¹) * (i.val.factorial : ℚ_[p]))
      (finiteMatrixQp p i r) := by
    rw [div_eq_mul_inv]
    calc
      _ = ((r.val.factorial : ℚ_[p]) * (r.val.factorial : ℚ_[p])⁻¹) *
          ((i.val.factorial : ℚ_[p])⁻¹ * (i.val.factorial : ℚ_[p])) *
          finiteMatrixQp p i r := by ring
      _ = _ := by rw [mul_inv_cancel₀ hr, inv_mul_cancel₀ hi, one_mul, one_mul]
  have hactual : Eq (α := ℚ_[p])
      (actualPhiMatrix p hp hp7 hp19 i r : ℚ_[p])
      (((actualGammaMatrix p hp hp7 hp19 i r : ℚ_[p]) *
        (r.val.factorial : ℚ_[p])⁻¹) * (i.val.factorial : ℚ_[p])) := by
    rw [actualPhiMatrix_entries, PadicInt.coe_mul, PadicInt.coe_mul,
      PadicInt.coe_natCast, inverseFactorialZp_coe]
    ring
  rw [hnormalized] at h
  exact hactual.symm ▸ h

/-- The scalar congruence is now applied to the constructed operator itself;
there is no matrix-comparison premise in this endpoint. -/
theorem actualCartier_literal_congruence :
    dotProduct (1 : Fin 5 → ℤ_[p])
        ((actualPhiMatrix p hp hp7 hp19).mulVec (markedZp p hp)) - literalSumZp p hp ∈
      Ideal.span ({(p : ℤ_[p]) ^ 5} : Set ℤ_[p]) :=
  actualZpMatrix_literal_transfer p hp (actualPhiMatrix p hp hp7 hp19)
    (actualPhiMatrix_congruence p hp hp7 hp19)

end
end WPCompletedCartier.ActualMatrix
