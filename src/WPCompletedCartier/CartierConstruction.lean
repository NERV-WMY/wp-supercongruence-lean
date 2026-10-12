import WPCompletedCartier.ActualSeries
import WPCompletedCartier.PresentationDescent

namespace WPCompletedCartier.CartierConstruction

noncomputable section
open scoped BigOperators
open WPResidueQuotient WPResidueQuotient.Adic
open WPCompletedCartier.ActualSeries

variable (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)

def indexNumerator (i : ClosedIndex) : numeratorFiltration ℤ_[p] (i.val.1 + 1) :=
  ⟨AddMonoidAlgebra.single i.val.2 1,
    single_mem_numeratorFiltration _ _ _ i.property⟩

def indexImage (i : ClosedIndex) : Completed p hp7 :=
  generatorImage p hp7 i.val.1 (indexNumerator p i)

def presentationImage : ClosedPresentation ℤ_[p] →ₗ[ℤ_[p]] Completed p hp7 :=
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
  let E := clearedSeriesMap p hp7 M M hM hMp
  let J : ClosedIndex → numeratorFiltration ℤ_[p] M := fun i =>
    if hi : i.val.1 + 1 ≤ M then
      (i.val.1.factorial : ℤ_[p]) •
        raiseNumerator p hp7 (i.val.1 + 1) M hi (indexNumerator p i)
    else 0
  have hJ (i : ClosedIndex) (hi : i ∈ v.support) :
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
  have hscale (i : ClosedIndex) (hi : i ∈ v.support) :
      ((M - 1).factorial : ℤ_[p]) • indexImage p hp7 i = E (J i) := by
    have hmi := le_commonPoleBound v i hi
    have hheight : height p i.val.1 ≤ M := (height_le_pole p i.val.1).trans hmi
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

def cartier : FClosed (Parameter.integralTenth p hp7) →ₗ[ℤ_[p]] Completed p hp7 :=
  liftActualPresentation (Parameter.integralTenth p hp7) (presentationImage p hp7)
    (presentationImage_kills_actual_relations p hp7)

theorem cartier_presentation (v : ClosedPresentation ℤ_[p]) :
    cartier p hp7 (presentationToClosed (Parameter.integralTenth p hp7) v) =
      presentationImage p hp7 v :=
  liftActualPresentation_apply _ _ _ _

def numeratorToClosed (n : ℕ) :
    numeratorFiltration ℤ_[p] (n + 1) →ₗ[ℤ_[p]]
      FClosed (Parameter.integralTenth p hp7) :=
  ((factorialNumeratorMap (Parameter.integralTenth p hp7) n).comp
    (numeratorFiltration ℤ_[p] (n + 1)).subtype).codRestrict _
      (fun A => factorialNumeratorMap_mem_closed _ _ A.property)

def generatorMap (n : ℕ) :
    numeratorFiltration ℤ_[p] (n + 1) →ₗ[ℤ_[p]] Completed p hp7 :=
  (NumericalTerms.factorialRatio (n + 1) (height p n) : ℤ_[p]) •
    clearedSeriesMap p hp7 (n + 1) (height p n)
      (height_positive p n) (height_admissible p n)

theorem cartier_index (i : ClosedIndex) :
    cartier p hp7
      ⟨presentationGenerator (Parameter.integralTenth p hp7) i,
        presentationGenerator_mem _ i⟩ = indexImage p hp7 i := by
  have hs := cartier_presentation p hp7 (Finsupp.single i 1)
  have harg : presentationToClosed (Parameter.integralTenth p hp7) (Finsupp.single i 1) =
      ⟨presentationGenerator (Parameter.integralTenth p hp7) i,
        presentationGenerator_mem _ i⟩ := by
    apply Subtype.ext
    change presentationMap (Parameter.integralTenth p hp7) (Finsupp.single i 1) = _
    simp only [presentationMap, Finsupp.linearCombination_single, one_smul]
  rw [harg] at hs
  simpa only [presentationImage, Finsupp.linearCombination_single, one_smul] using hs

theorem cartier_numerator (n : ℕ) (A : numeratorFiltration ℤ_[p] (n + 1)) :
    cartier p hp7 (numeratorToClosed p hp7 n A) = generatorImage p hp7 n A := by
  let L := (cartier p hp7).comp (numeratorToClosed p hp7 n)
  let E := generatorMap p hp7 n
  have hgen (x : Exponents) (hx : canonicalDegreeNat x ≤ n + 1) :
      L ⟨AddMonoidAlgebra.single x 1, single_mem_numeratorFiltration x 1 _ hx⟩ =
        E ⟨AddMonoidAlgebra.single x 1, single_mem_numeratorFiltration x 1 _ hx⟩ := by
    exact cartier_index p hp7 ⟨(n, x), hx⟩
  have hP := A.property
  change A.val ∈ AddMonoidAlgebra.supported ℤ_[p] ℤ_[p]
    {x | canonicalDegreeNat x ≤ n + 1} at hP
  rw [AddMonoidAlgebra.supported_eq_span_single] at hP
  have H : ∀ hA : A.val ∈ numeratorFiltration ℤ_[p] (n + 1),
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

theorem generatorImage_sub_five_mem (n : ℕ)
    (A : numeratorFiltration ℤ_[p] (n + 1)) :
    generatorImage p hp7 n A - ofModule (p : ℤ_[p])
      (∑ k ∈ Finset.range 5, NumericalTerms.closedTerm p hp7 A.val
        (n + 1) (height p n) k (height_positive p n)
          (height_admissible p n) A.property) ∈
      powerSubmodule (M := Completed p hp7) (p : ℤ_[p]) 5 := by
  let a := fun k => NumericalTerms.closedTerm p hp7 A.val
    (n + 1) (height p n) k (height_positive p n)
      (height_admissible p n) A.property
  have ha : AdicSeries.EventuallyDivisible (p : ℤ_[p]) a := by
    intro t
    exact ⟨6 * t + 1, fun k hk => NumericalTerms.closedTerm_eventual
      p hp7 _ _ _ _ _ _ t k hk⟩
  have he : generatorImage p hp7 n A = AdicSeries.sum (p : ℤ_[p]) a ha :=
    (AdicSeries.sum_unique _ _ _ _ (generatorImage_converges p hp7 n A)).symm
  rw [he]
  apply AdicSeries.sum_sub_partialSum_mem_powerSubmodule (p : ℤ_[p])
    (AdicSeries.actualClosed_smul_injective (Parameter.integralTenth p hp7)
      (p : ℤ_[p]) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)) 5 5 a ha
  exact fun k hk => NumericalTerms.closedTerm_five p hp7 _ _ _ _ _ _ k hk

def completedCartier : Completed p hp7 →ₗ[ℤ_[p]] Completed p hp7 :=
  AdicSeries.extension (p : ℤ_[p]) (cartier p hp7)

theorem completedCartier_ofModule (g : FClosed (Parameter.integralTenth p hp7)) :
    completedCartier p hp7 (ofModule (p : ℤ_[p]) g) = cartier p hp7 g :=
  AdicSeries.extension_ofModule _ _ _

theorem continuous_completedCartier : Continuous (completedCartier p hp7) :=
  AdicSeries.continuous_extension _ _

end

end WPCompletedCartier.CartierConstruction
