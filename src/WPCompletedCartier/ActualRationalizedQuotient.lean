import WPCompletedCartier.ActualQuotient
import WPCompletedCartier.QpExtension
import WPCompletedCartier.InverseTraceCoordinates
import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.RingTheory.Localization.Module

namespace WPCompletedCartier.ActualRationalizedQuotient

noncomputable section
open scoped BigOperators
open WPResidueQuotient WPResidueQuotient.Adic WPResidueQuotient.ActualCompletion
open WPCompletedCartier.PadicRationalization

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

local notation "S" => Submonoid.powers (p : ℤ_[p])
local notation "J" => ActualQuotient.interiorQuotientImage p hp
local notation "V" => InteriorSeries.Completed p hp
local notation "W" => RationalizedCartier.Rationalized p hp
local notation "e" => padicLocalizationEquiv p

local instance : Module ℚ_[p] W := QpExtension.qpModule p hp

local instance : IsLocalizedModule S (RationalizedCartier.integralMap p hp) := by
  change IsLocalizedModule S (LocalizedModule.mkLinearMap S V)
  infer_instance

/-- Rationalization of the actual interior image in the actual completed
closed-exact quotient. The integral quotient image is already identified
with its five coordinates by the checked residue equivalence. -/
abbrev RationalizedQuotient := LocalizedModule S J

instance quotientQpModule : Module ℚ_[p] (RationalizedQuotient p hp) :=
  Module.compHom (RationalizedQuotient p hp) (e).symm.toRingHom

local instance : Module ℚ_[p] (RationalizedQuotient p hp) := quotientQpModule p hp

/-- Cache exactly the scalar action of the actual rationalized quotient module. -/
instance (priority := 1001) quotientQpSMul : SMul ℚ_[p] (RationalizedQuotient p hp) :=
  (quotientQpModule p hp).toDistribMulAction.toMulAction.toSMul

/-- Scalar notation has this actual quotient as its explicit result type. -/
instance (priority := 1001) quotientQpHSMul :
    HSMul ℚ_[p] (RationalizedQuotient p hp) (RationalizedQuotient p hp) :=
  ⟨@SMul.smul ℚ_[p] (RationalizedQuotient p hp) (quotientQpSMul p hp)⟩

theorem quotient_qp_smul (a : ℚ_[p]) (q : RationalizedQuotient p hp) :
    (a • q : RationalizedQuotient p hp) =
      ((e).symm a • q : RationalizedQuotient p hp) := rfl

set_option maxHeartbeats 1600000 in
instance quotientIntegralQpTower : IsScalarTower ℤ_[p] ℚ_[p] (RationalizedQuotient p hp) := by
  refine @IsScalarTower.of_algebraMap_smul ℤ_[p] ℚ_[p] (RationalizedQuotient p hp)
    (inferInstance : CommSemiring ℤ_[p]) (inferInstance : Semiring ℚ_[p])
    (inferInstance : Algebra ℤ_[p] ℚ_[p])
    (quotientQpModule p hp).toDistribMulAction.toMulAction
    (inferInstance : SMul ℤ_[p] (RationalizedQuotient p hp)) ?_
  intro a q
  calc
    (algebraMap ℤ_[p] ℚ_[p] a • q : RationalizedQuotient p hp) =
        ((e).symm (algebraMap ℤ_[p] ℚ_[p] a) • q : RationalizedQuotient p hp) :=
      quotient_qp_smul p hp (algebraMap ℤ_[p] ℚ_[p] a) q
    _ = (algebraMap ℤ_[p] (ScalarLocalization p) a • q : RationalizedQuotient p hp) :=
      congrArg (fun c : ScalarLocalization p => (c • q : RationalizedQuotient p hp))
        ((e).symm.commutes a)
    _ = (a • q : RationalizedQuotient p hp) :=
      IsScalarTower.algebraMap_smul (ScalarLocalization p) a q

local instance : IsScalarTower ℤ_[p] ℚ_[p] W := QpExtension.integralQpTower p hp
local instance : IsScalarTower ℤ_[p] ℚ_[p] (RationalizedQuotient p hp) :=
  quotientIntegralQpTower p hp

local instance : LinearMap.CompatibleSMul W (RationalizedQuotient p hp) ℤ_[p] ℚ_[p] :=
  LinearMap.IsScalarTower.compatibleSMul

def integralQuotientMap : J →ₗ[ℤ_[p]] RationalizedQuotient p hp :=
  LocalizedModule.mkLinearMap S J

local instance : IsLocalizedModule S (integralQuotientMap p hp) := by
  change IsLocalizedModule S (LocalizedModule.mkLinearMap S J)
  infer_instance

/-- Quotient projection of the actual completed strict module, retaining its
actual closed-exact quotient representative rather than just its coordinates. -/
def integralProjection : V →ₗ[ℤ_[p]] J :=
  (ActualQuotient.interiorQuotientInclusion p hp).rangeRestrict

theorem integralProjection_cartier (x : V) :
    integralProjection p hp (InteriorConstruction.completedCartier p hp x) =
      ActualQuotient.actualInteriorQuotientOperator p hp hp7 hp19
        (integralProjection p hp x) := by
  apply Subtype.ext
  exact (ActualQuotient.quotient_interior_intertwines p hp hp7 hp19 x).symm

/-- The actual quotient projection extended to the same literal Qp module
on which QpExtension.cartierQp acts. -/
def quotientProjection : W →ₗ[ℚ_[p]] RationalizedQuotient p hp where
  toFun := LocalizedModule.map S (integralProjection p hp)
  map_add' x y := map_add (LocalizedModule.map S (integralProjection p hp)) x y
  map_smul' a x := by
    change LocalizedModule.map S (integralProjection p hp) ((e).symm a • x) =
      (e).symm a • LocalizedModule.map S (integralProjection p hp) x
    exact map_smul (LocalizedModule.map S (integralProjection p hp)) ((e).symm a) x

@[simp] theorem quotientProjection_integral (x : V) :
    quotientProjection p hp (RationalizedCartier.integralMap p hp x) =
      integralQuotientMap p hp (integralProjection p hp x) :=
  LocalizedModule.map_mk S (integralProjection p hp) x 1

set_option maxHeartbeats 1600000 in
theorem quotientProjection_surjective : Function.Surjective (quotientProjection p hp) :=
  LocalizedModule.map_surjective S (integralProjection p hp)
    (LinearMap.surjective_rangeRestrict (ActualQuotient.interiorQuotientInclusion p hp))

/-- The actual Qp-linear quotient projection's kernel, with both modules fixed. -/
def projectionKernel : Submodule ℚ_[p] W :=
  LinearMap.ker (R := ℚ_[p]) (R₂ := ℚ_[p]) (M := W)
    (M₂ := RationalizedQuotient p hp) (quotientProjection p hp)

/-- The same target is an actual quotient of the rationalized strict module
by the kernel of its actual closed-exact quotient projection. -/
def strictQuotientEquiv :=
  LinearMap.quotKerEquivOfSurjective (R := ℚ_[p]) (M := W)
    (M₂ := RationalizedQuotient p hp) (quotientProjection p hp)
    (quotientProjection_surjective p hp)

/-- Cartier induced on the rationalization of the actual quotient image. -/
def cartierQuotientQp : RationalizedQuotient p hp →ₗ[ℚ_[p]] RationalizedQuotient p hp where
  toFun := LocalizedModule.map S (ActualQuotient.actualInteriorQuotientOperator p hp hp7 hp19)
  map_add' x y := map_add
    (LocalizedModule.map S (ActualQuotient.actualInteriorQuotientOperator p hp hp7 hp19)) x y
  map_smul' a x := by
    change LocalizedModule.map S (ActualQuotient.actualInteriorQuotientOperator p hp hp7 hp19)
        ((e).symm a • x) = (e).symm a •
      LocalizedModule.map S (ActualQuotient.actualInteriorQuotientOperator p hp hp7 hp19) x
    exact map_smul
      (LocalizedModule.map S (ActualQuotient.actualInteriorQuotientOperator p hp hp7 hp19))
      ((e).symm a) x

@[simp] theorem cartierQuotientQp_integral (q : J) :
    cartierQuotientQp p hp hp7 hp19 (integralQuotientMap p hp q) =
      integralQuotientMap p hp
        (ActualQuotient.actualInteriorQuotientOperator p hp hp7 hp19 q) :=
  LocalizedModule.map_mk S (ActualQuotient.actualInteriorQuotientOperator p hp hp7 hp19) q 1

theorem quotientProjection_intertwines :
    (quotientProjection p hp).comp (QpExtension.cartierQp p hp) =
      (cartierQuotientQp p hp hp7 hp19).comp (quotientProjection p hp) := by
  apply LinearMap.restrictScalars_injective ℤ_[p]
  apply IsLocalizedModule.linearMap_ext S (RationalizedCartier.integralMap p hp)
    (integralQuotientMap p hp)
  ext x
  change quotientProjection p hp
      (QpExtension.cartierQp p hp (RationalizedCartier.integralMap p hp x)) =
    cartierQuotientQp p hp hp7 hp19
      (quotientProjection p hp (RationalizedCartier.integralMap p hp x))
  calc
    quotientProjection p hp
        (QpExtension.cartierQp p hp (RationalizedCartier.integralMap p hp x)) =
        integralQuotientMap p hp
          (integralProjection p hp (InteriorConstruction.completedCartier p hp x)) :=
      (congrArg (quotientProjection p hp) (QpExtension.cartierQp_integral p hp x)).trans
        (quotientProjection_integral p hp (InteriorConstruction.completedCartier p hp x))
    _ = integralQuotientMap p hp
        (ActualQuotient.actualInteriorQuotientOperator p hp hp7 hp19
          (integralProjection p hp x)) :=
      congrArg (integralQuotientMap p hp) (integralProjection_cartier p hp hp7 hp19 x)
    _ = cartierQuotientQp p hp hp7 hp19
        (quotientProjection p hp (RationalizedCartier.integralMap p hp x)) :=
      (cartierQuotientQp_integral p hp hp7 hp19 (integralProjection p hp x)).symm.trans
        (congrArg (cartierQuotientQp p hp hp7 hp19)
          (quotientProjection_integral p hp x)).symm

/-- The literal Qp coordinate module is itself the localization of Zp^5.
Finite common denominators follow from the actual scalar localization. -/
instance coeVectorIsLocalized : IsLocalizedModule S (InverseTraceCoordinates.coeVector p) where
  map_units := InverseTraceCoordinates.scalarEnd_isUnit p
  surj v := by
    obtain ⟨b, hb⟩ := IsLocalizedModule.exist_integer_multiples_of_finite S
      (Algebra.linearMap ℤ_[p] ℚ_[p]) v
    choose a ha using hb
    refine ⟨(a, b), ?_⟩
    ext i
    change ((b : ℤ_[p]) : ℚ_[p]) * v i = (a i : ℚ_[p])
    have hi : (b : ℤ_[p]) • v i = (a i : ℚ_[p]) := by
      simpa only [Algebra.linearMap_apply, PadicInt.algebraMap_apply] using (ha i).symm
    have hs : ((b : ℤ_[p]) : ℚ_[p]) * v i = (b : ℤ_[p]) • v i := by
      simpa only [PadicInt.algebraMap_apply, smul_eq_mul] using
        (IsScalarTower.algebraMap_smul ℚ_[p] (b : ℤ_[p]) (v i))
    exact hs.trans hi
  exists_of_eq := by
    intro x y h
    refine ⟨1, ?_⟩
    have hxy : x = y := by
      ext i
      exact PadicInt.ext (congrFun h i)
    rw [hxy]

/-- An actual Qp-linear equivalence from the rationalized quotient, obtained
by localizing the actual integral quotient equivalence. -/
def gammaQuotientEquiv : RationalizedQuotient p hp ≃ₗ[ℚ_[p]] (Fin 5 → ℚ_[p]) :=
  IsLocalizedModule.mapEquiv S (integralQuotientMap p hp)
    (InverseTraceCoordinates.coeVector p) ℚ_[p]
    (ActualQuotient.actualInteriorQuotientEquiv p hp hp7 hp19)

@[simp] theorem gammaQuotientEquiv_integral (q : J) :
    gammaQuotientEquiv p hp hp7 hp19 (integralQuotientMap p hp q) =
      InverseTraceCoordinates.coeVector p
        (ActualQuotient.actualInteriorQuotientEquiv p hp hp7 hp19 q) := by
  change IsLocalizedModule.map S (integralQuotientMap p hp)
    (InverseTraceCoordinates.coeVector p)
    (ActualQuotient.actualInteriorQuotientEquiv p hp hp7 hp19).toLinearMap
    (integralQuotientMap p hp q) = _
  exact IsLocalizedModule.map_apply S (integralQuotientMap p hp)
    (InverseTraceCoordinates.coeVector p)
    (ActualQuotient.actualInteriorQuotientEquiv p hp hp7 hp19).toLinearMap q

/-- The printed H transport, with its literal factorial inverse in Qp. -/
def factorialCoordinates : (Fin 5 → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin 5 → ℚ_[p]) where
  toFun v i := (i.val.factorial : ℚ_[p]) * v i
  invFun v i := (i.val.factorial : ℚ_[p])⁻¹ * v i
  map_add' x y := by ext i; simp only [Pi.add_apply, mul_add]
  map_smul' a x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  left_inv v := by
    ext i
    change (i.val.factorial : ℚ_[p])⁻¹ * ((i.val.factorial : ℚ_[p]) * v i) = v i
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero i.val), one_mul]
  right_inv v := by
    ext i
    change (i.val.factorial : ℚ_[p]) * ((i.val.factorial : ℚ_[p])⁻¹ * v i) = v i
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero i.val), one_mul]

def rawQuotientEquiv : RationalizedQuotient p hp ≃ₗ[ℚ_[p]] (Fin 5 → ℚ_[p]) :=
  (gammaQuotientEquiv p hp hp7 hp19).trans (factorialCoordinates p)

def rawQuotientProjection : W →ₗ[ℚ_[p]] (Fin 5 → ℚ_[p]) :=
  (rawQuotientEquiv p hp hp7 hp19).toLinearMap.comp (quotientProjection p hp)

set_option maxHeartbeats 1600000 in
/-- The existing inverse-trace projection has its actual quotient provenance:
first the actual quotient image, then its coordinate equivalence, then H. -/
theorem rawQuotientProjection_integral (x : V) :
    rawQuotientProjection p hp hp7 hp19 (RationalizedCartier.integralMap p hp x) =
      InverseTraceCoordinates.coeVector p (InverseTraceCoordinates.rawProjection p hp hp7 hp19 x) := by
  let j : J := integralProjection p hp x
  let c : Fin 5 → ℤ_[p] := ActualQuotient.actualInteriorQuotientEquiv p hp hp7 hp19 j
  let v : Fin 11 → ℤ_[p] := constantCoordinatesZp p hp hp7 hp19
    (completedInteriorInclusion (Parameter.integralTenth p hp) (p : ℤ_[p]) x)
  have hgamma : gammaQuotientEquiv p hp hp7 hp19
      (quotientProjection p hp (RationalizedCartier.integralMap p hp x)) =
      InverseTraceCoordinates.coeVector p c :=
    (congrArg (gammaQuotientEquiv p hp hp7 hp19)
      (quotientProjection_integral p hp x)).trans
        (gammaQuotientEquiv_integral p hp hp7 hp19 j)
  have hcoords : c = moduleInteriorProjection v :=
    (ActualQuotient.actualInteriorQuotientEquiv_coordinates p hp hp7 hp19 j).trans
      (congrArg (moduleInteriorProjection (R := ℤ_[p]))
        (constantQuotientZpEquiv_mk p hp hp7 hp19
          (completedInteriorInclusion (Parameter.integralTenth p hp) (p : ℤ_[p]) x)))
  have hnormalized : factorialCoordinates p
      (InverseTraceCoordinates.coeVector p (moduleInteriorProjection v)) =
      InverseTraceCoordinates.coeVector p (InverseTraceCoordinates.rawProjection p hp hp7 hp19 x) := by
    ext i
    change (i.val.factorial : ℚ_[p]) * (v (Fin.castAdd 6 i) : ℚ_[p]) =
      (((i.val.factorial : ℤ_[p]) * v (Fin.castAdd 6 i) : ℤ_[p]) : ℚ_[p])
    rw [PadicInt.coe_mul, PadicInt.coe_natCast]
  exact (congrArg (factorialCoordinates p) hgamma).trans
    ((congrArg (fun w : Fin 5 → ℤ_[p] => factorialCoordinates p
      (InverseTraceCoordinates.coeVector p w)) hcoords).trans hnormalized)

theorem rawQuotientProjection_eq :
    (rawQuotientProjection p hp hp7 hp19).restrictScalars ℤ_[p] =
      InverseTraceCoordinates.rationalizedProjection p hp hp7 hp19 := by
  apply IsLocalizedModule.linearMap_ext S (RationalizedCartier.integralMap p hp)
    (InverseTraceCoordinates.coeVector p)
  apply LinearMap.ext
  intro x
  exact (rawQuotientProjection_integral p hp hp7 hp19 x).trans
    (InverseTraceCoordinates.rationalizedProjection_integral p hp hp7 hp19 x).symm

theorem rawQuotientProjection_apply (x : W) :
    rawQuotientProjection p hp hp7 hp19 x =
      InverseTraceCoordinates.rationalizedProjection p hp hp7 hp19 x :=
  DFunLike.congr_fun (rawQuotientProjection_eq p hp hp7 hp19) x

def gammaMatrixQp : Matrix (Fin 5) (Fin 5) ℚ_[p] :=
  fun i r => (ActualMatrix.actualGammaMatrix p hp hp7 hp19 i r : ℚ_[p])

/-- The actual raw-coordinate matrix, cast from the concretely constructed
integral H conjugation. No supplied matrix premise occurs here. -/
def phiMatrixQp : Matrix (Fin 5) (Fin 5) ℚ_[p] :=
  fun i r => (ActualMatrix.actualPhiMatrix p hp hp7 hp19 i r : ℚ_[p])

theorem coeVector_mulVec (A : Matrix (Fin 5) (Fin 5) ℤ_[p]) (v : Fin 5 → ℤ_[p]) :
    InverseTraceCoordinates.coeVector p (A.mulVec v) =
      Matrix.mulVec ((fun i r => (A i r : ℚ_[p])) : Matrix (Fin 5) (Fin 5) ℚ_[p])
        (InverseTraceCoordinates.coeVector p v) := by
  ext i
  change ((∑ r, A i r * v r : ℤ_[p]) : ℚ_[p]) = ∑ r, (A i r : ℚ_[p]) * (v r : ℚ_[p])
  rw [PadicInt.coe_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact PadicInt.coe_mul _ _

theorem gammaMatrixQp_integral_action (c : Fin 5 → ℤ_[p]) :
    InverseTraceCoordinates.coeVector p (ActualMatrix.actual5 p hp hp7 hp19 c) =
      (gammaMatrixQp p hp hp7 hp19).mulVec (InverseTraceCoordinates.coeVector p c) := by
  change InverseTraceCoordinates.coeVector p (ActualMatrix.actual5 p hp hp7 hp19 c) =
    Matrix.mulVec ((fun i r => (ActualMatrix.actualGammaMatrix p hp hp7 hp19 i r : ℚ_[p])) :
      Matrix (Fin 5) (Fin 5) ℚ_[p])
      (InverseTraceCoordinates.coeVector p c)
  rw [← coeVector_mulVec]
  congr 1
  change ActualMatrix.actual5 p hp hp7 hp19 c =
    (LinearMap.toMatrix' (ActualMatrix.actual5 p hp hp7 hp19)).mulVec c
  exact (LinearMap.toMatrix'_mulVec _ c).symm

theorem gamma_coordinate_conjugacy :
    (gammaQuotientEquiv p hp hp7 hp19).toLinearMap.comp
        (cartierQuotientQp p hp hp7 hp19) =
      (gammaMatrixQp p hp hp7 hp19).mulVecLin.comp
        (gammaQuotientEquiv p hp hp7 hp19).toLinearMap := by
  apply LinearMap.restrictScalars_injective ℤ_[p]
  apply IsLocalizedModule.linearMap_ext S (integralQuotientMap p hp)
    (InverseTraceCoordinates.coeVector p)
  apply LinearMap.ext
  intro q
  change gammaQuotientEquiv p hp hp7 hp19
      (cartierQuotientQp p hp hp7 hp19 (integralQuotientMap p hp q)) =
    (gammaMatrixQp p hp hp7 hp19).mulVec
      (gammaQuotientEquiv p hp hp7 hp19 (integralQuotientMap p hp q))
  have h1 := congrArg (gammaQuotientEquiv p hp hp7 hp19)
    (cartierQuotientQp_integral p hp hp7 hp19 q)
  have h2 := gammaQuotientEquiv_integral p hp hp7 hp19
    (ActualQuotient.actualInteriorQuotientOperator p hp hp7 hp19 q)
  have h3 := congrArg (InverseTraceCoordinates.coeVector p)
    (ActualQuotient.actual5_interior_quotient p hp hp7 hp19 q).symm
  have h4 := gammaMatrixQp_integral_action p hp hp7 hp19
    (ActualQuotient.actualInteriorQuotientEquiv p hp hp7 hp19 q)
  have h5 := congrArg (Matrix.mulVec (gammaMatrixQp p hp hp7 hp19))
    (gammaQuotientEquiv_integral p hp hp7 hp19 q).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

theorem gamma_coordinate_action (q : RationalizedQuotient p hp) :
    gammaQuotientEquiv p hp hp7 hp19 (cartierQuotientQp p hp hp7 hp19 q) =
      (gammaMatrixQp p hp hp7 hp19).mulVec (gammaQuotientEquiv p hp hp7 hp19 q) :=
  DFunLike.congr_fun (gamma_coordinate_conjugacy p hp hp7 hp19) q

theorem factorialCoordinates_actual_matrix (v : Fin 5 → ℚ_[p]) :
    factorialCoordinates p ((gammaMatrixQp p hp hp7 hp19).mulVec v) =
      (phiMatrixQp p hp hp7 hp19).mulVec (factorialCoordinates p v) := by
  ext i
  change (i.val.factorial : ℚ_[p]) *
      (∑ r, (ActualMatrix.actualGammaMatrix p hp hp7 hp19 i r : ℚ_[p]) * v r) =
    ∑ r, (ActualMatrix.actualPhiMatrix p hp hp7 hp19 i r : ℚ_[p]) *
      ((r.val.factorial : ℚ_[p]) * v r)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [ActualMatrix.actualPhiMatrix_entries, PadicInt.coe_mul, PadicInt.coe_mul,
    PadicInt.coe_natCast, ActualMatrix.inverseFactorialZp_coe]
  have hr : (r.val.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r.val
  calc
    _ = ((i.val.factorial : ℚ_[p]) *
        (ActualMatrix.actualGammaMatrix p hp hp7 hp19 i r : ℚ_[p])) * 1 * v r := by ring
    _ = ((i.val.factorial : ℚ_[p]) *
        (ActualMatrix.actualGammaMatrix p hp hp7 hp19 i r : ℚ_[p])) *
        ((r.val.factorial : ℚ_[p])⁻¹ * (r.val.factorial : ℚ_[p])) * v r := by
      rw [inv_mul_cancel₀ hr]
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
theorem raw_coordinate_action (q : RationalizedQuotient p hp) :
    rawQuotientEquiv p hp hp7 hp19 (cartierQuotientQp p hp hp7 hp19 q) =
      (phiMatrixQp p hp hp7 hp19).mulVec (rawQuotientEquiv p hp hp7 hp19 q) := by
  exact (congrArg (factorialCoordinates p)
    (gamma_coordinate_action p hp hp7 hp19 q)).trans
      (factorialCoordinates_actual_matrix p hp hp7 hp19
        (gammaQuotientEquiv p hp hp7 hp19 q))

set_option maxHeartbeats 1600000 in
theorem cartier_rawProjection (x : W) :
    rawQuotientProjection p hp hp7 hp19 (QpExtension.cartierQp p hp x) =
      (phiMatrixQp p hp hp7 hp19).mulVec (rawQuotientProjection p hp hp7 hp19 x) := by
  have h : quotientProjection p hp (QpExtension.cartierQp p hp x) =
      cartierQuotientQp p hp hp7 hp19 (quotientProjection p hp x) :=
    DFunLike.congr_fun (quotientProjection_intertwines p hp hp7 hp19) x
  exact (congrArg (rawQuotientEquiv p hp hp7 hp19) h).trans
    (raw_coordinate_action p hp hp7 hp19 (quotientProjection p hp x))

def rawPoleQuotient (n : ℕ) (A : numeratorFiltration ℤ_[p] n) : RationalizedQuotient p hp :=
  quotientProjection p hp (RationalizedCartier.rawPole p hp n A)

set_option maxHeartbeats 1600000 in
theorem rawPoleQuotient_eq (n : ℕ) (A : numeratorFiltration ℤ_[p] n) :
    rawPoleQuotient p hp n A = ((n.factorial : ℚ_[p])⁻¹ •
      integralQuotientMap p hp (integralProjection p hp
        (ofModule (p : ℤ_[p]) (InteriorConstruction.numeratorToInterior p hp n A))) :
        RationalizedQuotient p hp) := by
  let a : ℚ_[p] := (n.factorial : ℚ_[p])⁻¹
  let x : V := ofModule (p : ℤ_[p]) (InteriorConstruction.numeratorToInterior p hp n A)
  have hraw : RationalizedCartier.rawPole p hp n A =
      (a • RationalizedCartier.integralMap p hp x : W) :=
    QpExtension.rawPole_qp p hp n A
  have hs := (quotientProjection p hp).map_smul a (RationalizedCartier.integralMap p hp x)
  have hi := quotientProjection_integral p hp x
  exact (congrArg (quotientProjection p hp) hraw).trans
    (hs.trans (congrArg (fun q : RationalizedQuotient p hp => (a • q : RationalizedQuotient p hp)) hi))

/-- The finite raw pullback sum is now an element of the actual rationalized
strict quotient, through the proved quotient projection. -/
def finitePullbackQuotient (N : ℕ) (r : Fin 5) : RationalizedQuotient p hp :=
  quotientProjection p hp (InverseTraceConstruction.finitePullback p hp N r)

set_option maxHeartbeats 1600000 in
theorem finitePullbackQuotient_eq (N : ℕ) (r : Fin 5) :
    finitePullbackQuotient p hp N r =
      ∑ k ∈ Finset.range N, ((InverseTraceConstruction.inputCoefficient p r k : ℚ_[p]) •
        rawPoleQuotient p hp (InverseTraceConstruction.inputIndex p r k)
          (InverseTraceConstruction.inputNumerator p hp r k) : RationalizedQuotient p hp) := by
  let term : ℕ → W := fun k =>
    algebraMap ℤ_[p] (RationalizedCartier.Coeff p) (InverseTraceConstruction.inputCoefficient p r k) •
      RationalizedCartier.rawPole p hp (InverseTraceConstruction.inputIndex p r k)
        (InverseTraceConstruction.inputNumerator p hp r k)
  have hsum : quotientProjection p hp (∑ k ∈ Finset.range N, term k) =
      ∑ k ∈ Finset.range N, quotientProjection p hp (term k) :=
    map_sum (quotientProjection p hp).toAddMonoidHom term (Finset.range N)
  have hterms : (∑ k ∈ Finset.range N, quotientProjection p hp (term k)) =
      ∑ k ∈ Finset.range N, ((InverseTraceConstruction.inputCoefficient p r k : ℚ_[p]) •
        rawPoleQuotient p hp (InverseTraceConstruction.inputIndex p r k)
          (InverseTraceConstruction.inputNumerator p hp r k) : RationalizedQuotient p hp) := by
    apply Finset.sum_congr rfl
    intro k _
    let c : ℤ_[p] := InverseTraceConstruction.inputCoefficient p r k
    let x : W := RationalizedCartier.rawPole p hp (InverseTraceConstruction.inputIndex p r k)
      (InverseTraceConstruction.inputNumerator p hp r k)
    have hscalar : (algebraMap ℤ_[p] (RationalizedCartier.Coeff p) c • x : W) =
        ((c : ℚ_[p]) • x : W) :=
      (IsScalarTower.algebraMap_smul (RationalizedCartier.Coeff p) c x).trans
        (QpExtension.qp_smul_integral p hp c x).symm
    exact (congrArg (quotientProjection p hp) hscalar).trans
      ((quotientProjection p hp).map_smul (c : ℚ_[p]) x)
  exact hsum.trans hterms

end
end WPCompletedCartier.ActualRationalizedQuotient
