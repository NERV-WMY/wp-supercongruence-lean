import WPCompletedCartier.ActualMatrix
import WPCompletedCartier.ClosedExact
import WPCompletedCartier.DerivativeDescent

namespace WPCompletedCartier.ActualQuotient

noncomputable section
open WPResidueQuotient WPResidueQuotient.Adic
open WPResidueQuotient.ActualCompletion
open WPCompletedCartier.ActualMatrix

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

local notation "u" => Parameter.integralTenth p hp
local notation "V" => ActualSeries.Completed p hp
local notation "T" => LinearMap.range (constantCompletedExactInclusion p hp)
local notation "Q" => V ⧸ T
local notation "e" => constantQuotientZpEquiv p hp hp7 hp19

/-- Cartier on the actual completed closed-exact quotient. Its descent is
instantiated with the proved derivative identity of the constructed map. -/
def actualQuotientOperator : Q →ₗ[ℤ_[p]] Q :=
  ClosedExact.quotientOperator p hp hp7 hp19 (CartierConstruction.cartier p hp)
    (DerivativeDescent.cartier_derivative p hp)

@[simp] theorem actualQuotientOperator_mk (x : V) :
    actualQuotientOperator p hp hp7 hp19 (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (CartierConstruction.completedCartier p hp x) := rfl

set_option maxHeartbeats 1600000 in
theorem section_quotient (c : Fin 11 → ℤ_[p]) :
    (Submodule.Quotient.mk (constantSectionZp p hp hp7 hp19 c) : Q) = (e).symm c := by
  have hs : e (Submodule.Quotient.mk (constantSectionZp p hp hp7 hp19 c) : Q) = c :=
    (constantQuotientZpEquiv_mk p hp hp7 hp19
      (constantSectionZp p hp hp7 hp19 c)).trans
        (constantCoordinatesZp_section p hp hp7 hp19 c)
  exact ((e).symm_apply_apply
    (Submodule.Quotient.mk (constantSectionZp p hp hp7 hp19 c) : Q)).symm.trans
      (congrArg (e).symm hs)

set_option maxHeartbeats 1600000 in
/-- The concrete eleven-coordinate operator is the conjugate of Cartier
on the actual quotient, rather than an independently supplied endomorphism. -/
theorem actual11_quotient (c : Fin 11 → ℤ_[p]) :
    actual11 p hp hp7 hp19 c =
      e (actualQuotientOperator p hp hp7 hp19 ((e).symm c)) := by
  have hQ : (Submodule.Quotient.mk (CartierConstruction.completedCartier p hp
      (constantSectionZp p hp hp7 hp19 c)) : Q) =
      actualQuotientOperator p hp hp7 hp19 ((e).symm c) :=
    (actualQuotientOperator_mk p hp hp7 hp19
      (constantSectionZp p hp hp7 hp19 c)).symm.trans
        (congrArg (actualQuotientOperator p hp hp7 hp19)
          (section_quotient p hp hp7 hp19 c))
  exact (constantQuotientZpEquiv_mk p hp hp7 hp19
    (CartierConstruction.completedCartier p hp
      (constantSectionZp p hp hp7 hp19 c))).symm.trans (congrArg e hQ)

set_option maxHeartbeats 1600000 in
theorem quotient_coordinates (q : Q) :
    e (actualQuotientOperator p hp hp7 hp19 q) = actual11 p hp hp7 hp19 (e q) := by
  exact ((actual11_quotient p hp hp7 hp19 (e q)).trans
    (congrArg (fun z : Q => e (actualQuotientOperator p hp hp7 hp19 z))
      ((e).symm_apply_apply q))).symm

theorem quotient_coordinate_conjugacy :
    (e).toLinearMap.comp (actualQuotientOperator p hp hp7 hp19) =
      (actual11 p hp hp7 hp19).comp (e).toLinearMap := by
  apply LinearMap.ext
  exact quotient_coordinates p hp hp7 hp19

/-- The image of the actual completed interior inclusion inside the actual
closed-exact quotient. No injectivity of the interior inclusion is required. -/
def interiorQuotientInclusion : InteriorSeries.Completed p hp →ₗ[ℤ_[p]] Q :=
  (T).mkQ.comp (completedInteriorInclusion u (p : ℤ_[p]))

def interiorQuotientImage : Submodule ℤ_[p] Q :=
  LinearMap.range (interiorQuotientInclusion p hp)

theorem quotient_interior_intertwines (x : InteriorSeries.Completed p hp) :
    actualQuotientOperator p hp hp7 hp19 (interiorQuotientInclusion p hp x) =
      interiorQuotientInclusion p hp (InteriorConstruction.completedCartier p hp x) := by
  change actualQuotientOperator p hp hp7 hp19
    (Submodule.Quotient.mk (completedInteriorInclusion u (p : ℤ_[p]) x)) = _
  rw [actualQuotientOperator_mk]
  apply congrArg Submodule.Quotient.mk
  exact (DFunLike.congr_fun (InteriorConstruction.completedCartier_intertwines p hp) x).symm

theorem actualQuotientOperator_preserves_interior :
    interiorQuotientImage p hp ≤
      (interiorQuotientImage p hp).comap (actualQuotientOperator p hp hp7 hp19) := by
  rintro q ⟨x, rfl⟩
  exact ⟨InteriorConstruction.completedCartier p hp x,
    (quotient_interior_intertwines p hp hp7 hp19 x).symm⟩

def actualInteriorQuotientOperator :
    interiorQuotientImage p hp →ₗ[ℤ_[p]] interiorQuotientImage p hp :=
  ((actualQuotientOperator p hp hp7 hp19).comp
    (interiorQuotientImage p hp).subtype).codRestrict _
      (fun q => actualQuotientOperator_preserves_interior p hp hp7 hp19 q.property)

theorem interiorQuotientImage_coordinates :
    (interiorQuotientImage p hp).map (e).toLinearMap =
      (LinearMap.range (completedInteriorInclusion u (p : ℤ_[p]))).map
        (constantCoordinatesZp p hp hp7 hp19) := by
  ext c
  constructor
  · rintro ⟨q, ⟨x, rfl⟩, rfl⟩
    refine ⟨completedInteriorInclusion u (p : ℤ_[p]) x,
      LinearMap.mem_range_self _ x, ?_⟩
    change constantCoordinatesZp p hp hp7 hp19 (completedInteriorInclusion u (p : ℤ_[p]) x) =
      e (Submodule.Quotient.mk (completedInteriorInclusion u (p : ℤ_[p]) x))
    exact (constantQuotientZpEquiv_mk p hp hp7 hp19 _).symm
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    refine ⟨interiorQuotientInclusion p hp x, LinearMap.mem_range_self _ x, ?_⟩
    exact constantQuotientZpEquiv_mk p hp hp7 hp19 _

/-- The previously established actual interior coordinate equivalence now
applies to the actual quotient image, not merely to a truncation of Zp^11. -/
def actualInteriorQuotientEquiv :
    interiorQuotientImage p hp ≃ₗ[ℤ_[p]] (Fin 5 → ℤ_[p]) :=
  ((e).submoduleMap (interiorQuotientImage p hp)).trans
    ((LinearEquiv.ofEq _ _ (interiorQuotientImage_coordinates p hp hp7 hp19)).trans
      (constantInteriorZpEquiv p hp hp7 hp19))

set_option maxHeartbeats 1600000 in
theorem actualInteriorQuotientEquiv_coordinates (q : interiorQuotientImage p hp) :
    actualInteriorQuotientEquiv p hp hp7 hp19 q = moduleInteriorProjection (e q.val) := by
  have hprojection (c : Actual.interiorCoordinates ℤ_[p]) :
      interiorCoordinatesEquiv c = moduleInteriorProjection c.val := rfl
  simp only [actualInteriorQuotientEquiv, constantInteriorZpEquiv,
    LinearEquiv.trans_apply, hprojection, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.submoduleMap_apply]

set_option maxHeartbeats 1600000 in
theorem actualInteriorQuotientEquiv_inclusion (q : interiorQuotientImage p hp) :
    moduleInteriorInclusion (actualInteriorQuotientEquiv p hp hp7 hp19 q) = e q.val := by
  have hImage : (interiorQuotientImage p hp).map (e).toLinearMap =
      Actual.interiorCoordinates ℤ_[p] :=
    (interiorQuotientImage_coordinates p hp hp7 hp19).trans
      (constantInteriorZp_image p hp hp7 hp19)
  have hm : e q.val ∈ (interiorQuotientImage p hp).map (e).toLinearMap :=
    ⟨q.val, q.property, rfl⟩
  have hc : e q.val ∈ Actual.interiorCoordinates ℤ_[p] := hImage ▸ hm
  have hl : moduleInteriorInclusion (moduleInteriorProjection (e q.val)) = e q.val :=
    congrArg (fun z : Actual.interiorCoordinates ℤ_[p] => z.val)
      ((interiorCoordinatesEquiv (R := ℤ_[p])).symm_apply_apply ⟨e q.val, hc⟩)
  exact (congrArg moduleInteriorInclusion
    (actualInteriorQuotientEquiv_coordinates p hp hp7 hp19 q)).trans hl

set_option maxHeartbeats 1600000 in
/-- The five-coordinate matrix acts on the actual completed interior image
through its established equivalence, with no abstract commutation premise. -/
theorem actual5_interior_quotient (q : interiorQuotientImage p hp) :
    actual5 p hp hp7 hp19 (actualInteriorQuotientEquiv p hp hp7 hp19 q) =
      actualInteriorQuotientEquiv p hp hp7 hp19
        (actualInteriorQuotientOperator p hp hp7 hp19 q) := by
  calc
    actual5 p hp hp7 hp19 (actualInteriorQuotientEquiv p hp hp7 hp19 q) =
        moduleInteriorProjection (actual11 p hp hp7 hp19
          (moduleInteriorInclusion (actualInteriorQuotientEquiv p hp hp7 hp19 q))) := rfl
    _ = moduleInteriorProjection (actual11 p hp hp7 hp19 (e q.val)) :=
      congrArg (fun c : Fin 11 → ℤ_[p] =>
        moduleInteriorProjection (actual11 p hp hp7 hp19 c))
          (actualInteriorQuotientEquiv_inclusion p hp hp7 hp19 q)
    _ = moduleInteriorProjection (e (actualQuotientOperator p hp hp7 hp19 q.val)) :=
      congrArg moduleInteriorProjection (quotient_coordinates p hp hp7 hp19 q.val).symm
    _ = actualInteriorQuotientEquiv p hp hp7 hp19
        (actualInteriorQuotientOperator p hp hp7 hp19 q) :=
      (actualInteriorQuotientEquiv_coordinates p hp hp7 hp19
        (actualInteriorQuotientOperator p hp hp7 hp19 q)).symm

theorem interior_coordinate_conjugacy :
    (actualInteriorQuotientEquiv p hp hp7 hp19).toLinearMap.comp
        (actualInteriorQuotientOperator p hp hp7 hp19) =
      (actual5 p hp hp7 hp19).comp (actualInteriorQuotientEquiv p hp hp7 hp19).toLinearMap := by
  apply LinearMap.ext
  intro q
  exact (actual5_interior_quotient p hp hp7 hp19 q).symm

end
end WPCompletedCartier.ActualQuotient
