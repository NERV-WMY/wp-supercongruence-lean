import WPCompletedCartier.InteriorSeries
import WPCompletedCartier.CartierConstruction

namespace WPCompletedCartier.InteriorConstruction

noncomputable section
open scoped BigOperators
open WPResidueQuotient WPResidueQuotient.Adic WPResidueQuotient.ActualCompletion
open WPCompletedCartier.InteriorSeries

section Presentation

variable {R T : Type*} [CommRing R] [AddCommGroup T] [Module R T]

abbrev InteriorIndex := {i : ℕ × Exponents // canonicalDegreeNat i.2 ≤ i.1}
abbrev InteriorPresentation (R : Type*) [CommRing R] := InteriorIndex →₀ R

def toClosedIndex (i : InteriorIndex) : ClosedIndex :=
  ⟨i.val, i.property.trans (Nat.le_succ i.val.1)⟩

def presentationGenerator (u : R) (i : InteriorIndex) : ActualRing u :=
  WPCompletedCartier.presentationGenerator u (toClosedIndex i)

def presentationMap (u : R) : InteriorPresentation R →ₗ[R] ActualRing u :=
  Finsupp.linearCombination R (presentationGenerator u)

theorem presentationGenerator_mem (u : R) (i : InteriorIndex) :
    presentationGenerator u i ∈ FInterior u := by
  rw [FInterior_eq_canonical_span]
  exact Submodule.subset_span ⟨i.val.2, i.val.1, i.property, rfl⟩

theorem presentationMap_mem (u : R) (v : InteriorPresentation R) :
    presentationMap u v ∈ FInterior u := by
  classical
  change v.sum (fun i r => r • presentationGenerator u i) ∈ FInterior u
  exact (FInterior u).sum_mem (fun i _ =>
    (FInterior u).smul_mem (v i) (presentationGenerator_mem u i))

def presentationToInterior (u : R) : InteriorPresentation R →ₗ[R] FInterior u :=
  (presentationMap u).codRestrict (FInterior u) (presentationMap_mem u)

theorem presentationToInterior_eq_sum (u : R) (v : InteriorPresentation R) :
    presentationToInterior u v =
      ∑ i ∈ v.support, v i •
        (⟨presentationGenerator u i, presentationGenerator_mem u i⟩ : FInterior u) := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  rfl

theorem presentationMap_range (u : R) :
    LinearMap.range (presentationMap u) = FInterior u := by
  rw [presentationMap, Finsupp.range_linearCombination, FInterior_eq_canonical_span]
  congr 1
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val.2, i.val.1, i.property, rfl⟩
  · rintro ⟨x, n, hx, rfl⟩
    exact ⟨⟨(n, x), hx⟩, rfl⟩

theorem presentationToInterior_surjective (u : R) :
    Function.Surjective (presentationToInterior u) := by
  intro g
  have hg : g.val ∈ LinearMap.range (presentationMap u) :=
    (presentationMap_range u).symm ▸ g.property
  obtain ⟨v, hv⟩ := hg
  exact ⟨v, Subtype.ext hv⟩

def commonNumeratorGenerator (u : R) (M : ℕ) (i : InteriorIndex) :
    WPResidueQuotient.LaurentPolynomial R :=
  WPCompletedCartier.commonNumeratorGenerator u M (toClosedIndex i)

def commonNumerator (u : R) (M : ℕ) :
    InteriorPresentation R →ₗ[R] WPResidueQuotient.LaurentPolynomial R :=
  Finsupp.linearCombination R (commonNumeratorGenerator u M)

theorem commonNumeratorGenerator_supported (u : R) (M : ℕ) (i : InteriorIndex)
    (hi : i.val.1 + 1 ≤ M) :
    commonNumeratorGenerator u M i ∈ numeratorFiltration R (M - 1) := by
  have hs := numeratorFiltration_mul_f_pow u i.val.1 (M - (i.val.1 + 1))
    (single_mem_numeratorFiltration i.val.2 (1 : R) i.val.1 i.property)
  have hd : i.val.1 + (M - (i.val.1 + 1)) = M - 1 := by omega
  rw [hd] at hs
  exact (numeratorFiltration R (M - 1)).smul_mem _ hs

theorem presentationGenerator_common_pole (u : R) (M : ℕ) (i : InteriorIndex)
    (hi : i.val.1 + 1 ≤ M) :
    presentationGenerator u i = poleLinearMap u M (commonNumeratorGenerator u M i) :=
  WPCompletedCartier.presentationGenerator_common_pole u M (toClosedIndex i) hi

theorem presentationMap_common_pole (u : R) (M : ℕ) (v : InteriorPresentation R)
    (hM : ∀ i ∈ v.support, i.val.1 + 1 ≤ M) :
    presentationMap u v = poleLinearMap u M (commonNumerator u M v) := by
  classical
  change (∑ i ∈ v.support, v i • presentationGenerator u i) =
    poleLinearMap u M (∑ i ∈ v.support, v i • commonNumeratorGenerator u M i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, presentationGenerator_common_pole u M i (hM i hi)]

theorem presentation_relation_iff [IsDomain R] (u : R) (M : ℕ)
    (v : InteriorPresentation R) (hM : ∀ i ∈ v.support, i.val.1 + 1 ≤ M) :
    presentationMap u v = 0 ↔ commonNumerator u M v = 0 := by
  rw [presentationMap_common_pole u M v hM, poleLinearMap_eq_zero_iff]

def commonPoleBound (v : InteriorPresentation R) : ℕ :=
  1 + ∑ i ∈ v.support, i.val.1

theorem le_commonPoleBound (v : InteriorPresentation R) (i : InteriorIndex)
    (hi : i ∈ v.support) : i.val.1 + 1 ≤ commonPoleBound v := by
  have h : i.val.1 ≤ ∑ j ∈ v.support, j.val.1 :=
    Finset.single_le_sum (fun j _ => Nat.zero_le j.val.1) hi
  unfold commonPoleBound
  omega

theorem all_actual_relations_are_common_numerators [IsDomain R] (u : R)
    (v : InteriorPresentation R) :
    presentationMap u v = 0 ↔ commonNumerator u (commonPoleBound v) v = 0 :=
  presentation_relation_iff u _ v (le_commonPoleBound v)

theorem presentationToInterior_kernel (u : R) :
    LinearMap.ker (presentationToInterior u) = LinearMap.ker (presentationMap u) := by
  ext v
  change presentationToInterior u v = 0 ↔ presentationMap u v = 0
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- Descent uses the kernel of the literal strict factorial presentation. -/
def liftActualPresentation (u : R) (L : InteriorPresentation R →ₗ[R] T)
    (hL : LinearMap.ker (presentationMap u) ≤ LinearMap.ker L) : FInterior u →ₗ[R] T :=
  ((LinearMap.ker (presentationToInterior u)).liftQ L
    (by rw [presentationToInterior_kernel]; exact hL)).comp
      ((presentationToInterior u).quotKerEquivOfSurjective
        (presentationToInterior_surjective u)).symm.toLinearMap

@[simp] theorem liftActualPresentation_apply (u : R)
    (L : InteriorPresentation R →ₗ[R] T)
    (hL : LinearMap.ker (presentationMap u) ≤ LinearMap.ker L)
    (v : InteriorPresentation R) :
    liftActualPresentation u L hL (presentationToInterior u v) = L v := by
  simp only [liftActualPresentation, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

end Presentation

variable (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)

def indexNumerator (i : InteriorIndex) : numeratorFiltration ℤ_[p] i.val.1 :=
  ⟨AddMonoidAlgebra.single i.val.2 1,
    single_mem_numeratorFiltration _ _ _ i.property⟩

def indexImage (i : InteriorIndex) : Completed p hp7 :=
  generatorImage p hp7 i.val.1 (indexNumerator p i)

def presentationImage : InteriorPresentation ℤ_[p] →ₗ[ℤ_[p]] Completed p hp7 :=
  Finsupp.linearCombination ℤ_[p] (indexImage p hp7)

theorem presentationImage_kills_actual_relations :
    LinearMap.ker (presentationMap (Parameter.integralTenth p hp7)) ≤
      LinearMap.ker (presentationImage p hp7) := by
  classical
  intro v hv
  change presentationMap (Parameter.integralTenth p hp7) v = 0 at hv
  change presentationImage p hp7 v = 0
  let M := commonPoleBound v
  have hM : 1 ≤ M := by
    dsimp [M, commonPoleBound]
    omega
  have hMp : M ≤ p * M := by
    have hp : 1 ≤ p := (Fact.out : p.Prime).pos
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right M hp
  let E := clearedSeriesMap p hp7 M M hM hM hMp
  let J : InteriorIndex → numeratorFiltration ℤ_[p] (M - 1) := fun i =>
    if hi : i.val.1 + 1 ≤ M then
      (i.val.1.factorial : ℤ_[p]) •
        raiseNumerator p hp7 (i.val.1 + 1) M (by omega) hi (indexNumerator p i)
    else 0
  have hJ (i : InteriorIndex) (hi : i ∈ v.support) :
      (J i).val = commonNumeratorGenerator (Parameter.integralTenth p hp7) M i := by
    dsimp only [J]
    rw [dif_pos (le_commonPoleBound v i hi)]
    rfl
  have hB : (∑ i ∈ v.support, v i • J i) = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
    change (∑ i ∈ v.support, v i • (J i).val) = 0
    calc
      _ = commonNumerator (Parameter.integralTenth p hp7) M v := by
        change _ = ∑ i ∈ v.support,
          v i • commonNumeratorGenerator (Parameter.integralTenth p hp7) M i
        apply Finset.sum_congr rfl
        intro i hi
        rw [hJ i hi]
      _ = 0 := (all_actual_relations_are_common_numerators
        (Parameter.integralTenth p hp7) v).mp hv
  have hscale (i : InteriorIndex) (hi : i ∈ v.support) :
      ((M - 1).factorial : ℤ_[p]) • indexImage p hp7 i = E (J i) := by
    have hmi := le_commonPoleBound v i hi
    have hheight : ActualSeries.height p i.val.1 ≤ M :=
      (ActualSeries.height_le_pole p i.val.1).trans hmi
    dsimp only [J, E, indexImage]
    rw [dif_pos hmi, map_smul, clearedSeriesMap_common_pole]
    exact generatorImage_factorial_cleared p hp7 i.val.1 M (indexNumerator p i) hheight
  apply completed_factorial_cancel p hp7 (M - 1)
  change ((M - 1).factorial : ℤ_[p]) • presentationImage p hp7 v =
    ((M - 1).factorial : ℤ_[p]) • 0
  rw [smul_zero]
  change ((M - 1).factorial : ℤ_[p]) •
    (∑ i ∈ v.support, v i • indexImage p hp7 i) = 0
  calc
    _ = E (∑ i ∈ v.support, v i • J i) := by
      rw [Finset.smul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = v i • (((M - 1).factorial : ℤ_[p]) • indexImage p hp7 i) :=
          smul_comm _ _ _
        _ = v i • E (J i) := by rw [hscale i hi]
        _ = E (v i • J i) := (map_smul E _ _).symm
    _ = 0 := by rw [hB, map_zero]

def cartier : FInterior (Parameter.integralTenth p hp7) →ₗ[ℤ_[p]] Completed p hp7 :=
  liftActualPresentation (Parameter.integralTenth p hp7) (presentationImage p hp7)
    (presentationImage_kills_actual_relations p hp7)

theorem cartier_presentation (v : InteriorPresentation ℤ_[p]) :
    cartier p hp7 (presentationToInterior (Parameter.integralTenth p hp7) v) =
      presentationImage p hp7 v :=
  liftActualPresentation_apply _ _ _ _

theorem cartier_index (i : InteriorIndex) :
    cartier p hp7
      ⟨presentationGenerator (Parameter.integralTenth p hp7) i,
        presentationGenerator_mem _ i⟩ = indexImage p hp7 i := by
  have hs := cartier_presentation p hp7 (Finsupp.single i 1)
  have harg : presentationToInterior (Parameter.integralTenth p hp7) (Finsupp.single i 1) =
      ⟨presentationGenerator (Parameter.integralTenth p hp7) i,
        presentationGenerator_mem _ i⟩ := by
    apply Subtype.ext
    change presentationMap (Parameter.integralTenth p hp7) (Finsupp.single i 1) = _
    simp only [presentationMap, Finsupp.linearCombination_single, one_smul]
  rw [harg] at hs
  simpa only [presentationImage, Finsupp.linearCombination_single, one_smul] using hs

def numeratorToInterior (n : ℕ) :
    numeratorFiltration ℤ_[p] n →ₗ[ℤ_[p]] FInterior (Parameter.integralTenth p hp7) :=
  ((factorialNumeratorMap (Parameter.integralTenth p hp7) n).comp
    (numeratorFiltration ℤ_[p] n).subtype).codRestrict _
      (fun A => factorialNumeratorMap_mem_interior _ _ A.property)

def generatorMap (n : ℕ) : numeratorFiltration ℤ_[p] n →ₗ[ℤ_[p]] Completed p hp7 :=
  (NumericalTerms.factorialRatio (n + 1) (ActualSeries.height p n) : ℤ_[p]) •
    (clearedSeriesMap p hp7 (n + 1) (ActualSeries.height p n) (by omega)
      (ActualSeries.height_positive p n) (ActualSeries.height_admissible p n))

theorem cartier_numerator (n : ℕ) (A : numeratorFiltration ℤ_[p] n) :
    cartier p hp7 (numeratorToInterior p hp7 n A) = generatorImage p hp7 n A := by
  let L := (cartier p hp7).comp (numeratorToInterior p hp7 n)
  let E := generatorMap p hp7 n
  have hgen (x : Exponents) (hx : canonicalDegreeNat x ≤ n) :
      L ⟨AddMonoidAlgebra.single x 1, single_mem_numeratorFiltration x 1 _ hx⟩ =
        E ⟨AddMonoidAlgebra.single x 1, single_mem_numeratorFiltration x 1 _ hx⟩ := by
    exact cartier_index p hp7 ⟨(n, x), hx⟩
  have hP := A.property
  change A.val ∈ AddMonoidAlgebra.supported ℤ_[p] ℤ_[p]
    {x | canonicalDegreeNat x ≤ n} at hP
  rw [AddMonoidAlgebra.supported_eq_span_single] at hP
  have H : ∀ hA : A.val ∈ numeratorFiltration ℤ_[p] n,
      L ⟨A.val, hA⟩ = E ⟨A.val, hA⟩ := by
    generalize hAeq : A.val = Q at hP ⊢
    clear hAeq
    induction hP using Submodule.span_induction with
    | mem Q hQ =>
        obtain ⟨x, hx, rfl⟩ := hQ
        intro hA
        exact hgen x hx
    | zero => intro hA; exact (map_zero L).trans (map_zero E).symm
    | add P Q hP hQ ihP ihQ =>
        intro hA
        change L (⟨P, by simpa only [numeratorFiltration,
          AddMonoidAlgebra.supported_eq_span_single] using hP⟩ +
          ⟨Q, by simpa only [numeratorFiltration,
            AddMonoidAlgebra.supported_eq_span_single] using hQ⟩) = _
        rw [map_add, ihP, ihQ]
        exact (map_add E _ _).symm
    | smul c P hP ihP =>
        intro hA
        change L (c • ⟨P, by simpa only [numeratorFiltration,
          AddMonoidAlgebra.supported_eq_span_single] using hP⟩) = _
        rw [map_smul, ihP]
        exact (map_smul E c _).symm
  exact H A.property

theorem generatorImage_sub_five_mem (n : ℕ) (A : numeratorFiltration ℤ_[p] n) :
    generatorImage p hp7 n A - ofModule (p : ℤ_[p])
      (∑ k ∈ Finset.range 5, NumericalTerms.interiorTerm p hp7 A.val
        (n + 1) (ActualSeries.height p n) k (by omega)
          (ActualSeries.height_admissible p n)
          (by simpa only [Nat.add_sub_cancel] using A.property)) ∈
      powerSubmodule (M := Completed p hp7) (p : ℤ_[p]) 5 := by
  let a := fun k => NumericalTerms.interiorTerm p hp7 A.val
    (n + 1) (ActualSeries.height p n) k (by omega)
      (ActualSeries.height_admissible p n)
      (by simpa only [Nat.add_sub_cancel] using A.property)
  have ha : AdicSeries.EventuallyDivisible (p : ℤ_[p]) a := by
    intro t
    exact ⟨6 * t + 1, fun k hk => NumericalTerms.interiorTerm_eventual
      p hp7 _ _ _ _ _ _ t k hk⟩
  have he : generatorImage p hp7 n A = AdicSeries.sum (p : ℤ_[p]) a ha :=
    (AdicSeries.sum_unique _ _ _ _ (generatorImage_converges p hp7 n A)).symm
  rw [he]
  apply AdicSeries.sum_sub_partialSum_mem_powerSubmodule (p : ℤ_[p])
    (AdicSeries.actualInterior_smul_injective (Parameter.integralTenth p hp7)
      (p : ℤ_[p]) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)) 5 5 a ha
  exact fun k hk => NumericalTerms.interiorTerm_five p hp7 _ _ _ _ _ _ k hk

theorem indexImage_inclusion (i : InteriorIndex) :
    completedInteriorInclusion (Parameter.integralTenth p hp7) (p : ℤ_[p])
      (indexImage p hp7 i) = CartierConstruction.indexImage p hp7 (toClosedIndex i) :=
  generatorImage_inclusion p hp7 i.val.1 (indexNumerator p i)

set_option maxHeartbeats 800000 in
theorem cartier_inclusion (g : FInterior (Parameter.integralTenth p hp7)) :
    completedInteriorInclusion (Parameter.integralTenth p hp7) (p : ℤ_[p])
      (cartier p hp7 g) =
      CartierConstruction.cartier p hp7
        (actualInteriorInclusion (Parameter.integralTenth p hp7) g) := by
  classical
  obtain ⟨v, rfl⟩ := presentationToInterior_surjective (Parameter.integralTenth p hp7) g
  rw [cartier_presentation, presentationToInterior_eq_sum]
  change completedInteriorInclusion _ _ (∑ i ∈ v.support, v i • indexImage p hp7 i) = _
  rw [map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, map_smul, map_smul, indexImage_inclusion]
  exact congrArg (fun z => v i • z)
    (CartierConstruction.cartier_index p hp7 (toClosedIndex i)).symm

def completedCartier : Completed p hp7 →ₗ[ℤ_[p]] Completed p hp7 :=
  AdicSeries.extension (p : ℤ_[p]) (cartier p hp7)

theorem completedCartier_ofModule (g : FInterior (Parameter.integralTenth p hp7)) :
    completedCartier p hp7 (ofModule (p : ℤ_[p]) g) = cartier p hp7 g :=
  AdicSeries.extension_ofModule _ _ _

theorem continuous_completedCartier : Continuous (completedCartier p hp7) :=
  AdicSeries.continuous_extension _ _

/-- Intertwining follows from density; no injectivity of the completed
interior inclusion is assumed or needed. -/
theorem completedCartier_intertwines :
    (completedInteriorInclusion (Parameter.integralTenth p hp7) (p : ℤ_[p])).comp
      (completedCartier p hp7) =
      (CartierConstruction.completedCartier p hp7).comp
        (completedInteriorInclusion (Parameter.integralTenth p hp7) (p : ℤ_[p])) := by
  apply LinearMap.ext
  have heq := (denseRange_ofModule (M := Module p hp7) (p : ℤ_[p])).equalizer
    ((continuous_completeMap (p : ℤ_[p])
      (actualInteriorInclusion (Parameter.integralTenth p hp7))).comp
        (continuous_completedCartier p hp7))
    ((CartierConstruction.continuous_completedCartier p hp7).comp
      (continuous_completeMap (p : ℤ_[p])
        (actualInteriorInclusion (Parameter.integralTenth p hp7))))
    (funext (fun g => by
      change completedInteriorInclusion _ _
          (completedCartier p hp7 (ofModule (p : ℤ_[p]) g)) =
        CartierConstruction.completedCartier p hp7
          (completeMap (p : ℤ_[p]) (actualInteriorInclusion _) (ofModule (p : ℤ_[p]) g))
      rw [completedCartier_ofModule, completeMap_ofModule,
        CartierConstruction.completedCartier_ofModule]
      exact cartier_inclusion p hp7 g))
  exact congrFun heq

end

end WPCompletedCartier.InteriorConstruction
