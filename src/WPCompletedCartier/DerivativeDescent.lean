import WPCompletedCartier.CartierConstruction
import WPCompletedCartier.DerivativeCompatibility

namespace WPCompletedCartier.DerivativeDescent

noncomputable section
open scoped BigOperators
open WPResidueQuotient WPResidueQuotient.Adic
open WPCompletedCartier.NumericalTerms WPCompletedCartier.ActualSeries
open WPCompletedCartier.CartierConstruction WPCompletedCartier.DerivativeCompatibility

variable (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)

local notation "u" => Parameter.integralTenth p hp7

theorem normalizedSum_eq_clearedSeriesMap (h : ℕ) (hh : 1 ≤ h)
    (B : numeratorFiltration ℤ_[p] (p * h)) :
    normalizedSum p hp7 h hh B = clearedSeriesMap p hp7 (p * h) h hh le_rfl B := rfl

/-- Transport a filtered numerator without unfolding the completed series. -/
theorem clearedSeriesMap_transport (m1 m2 h : ℕ) (he : m1 = m2)
    (hh : 1 ≤ h) (h1 : m1 ≤ p * h) (h2 : m2 ≤ p * h)
    (A1 : numeratorFiltration ℤ_[p] m1) (A2 : numeratorFiltration ℤ_[p] m2)
    (hval : A1.val = A2.val) :
    clearedSeriesMap p hp7 m1 h hh h1 A1 =
      clearedSeriesMap p hp7 m2 h hh h2 A2 := by
  subst m2
  have hA : A1 = A2 := Subtype.ext hval
  subst A2
  rfl

theorem pole_bound (n : ℕ) : n + 1 ≤ p * (n + 1) := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).pos
  simpa only [Nat.one_mul] using Nat.mul_le_mul_right (n + 1) hp

def raisedInput (n : ℕ) (A : numeratorFiltration ℤ_[p] (n + 1)) :
    numeratorFiltration ℤ_[p] (p * (n + 1)) :=
  raiseNumerator p hp7 (n + 1) (p * (n + 1)) (pole_bound p n) A

theorem cartier_numerator_eq_normalizedSum (n : ℕ)
    (A : numeratorFiltration ℤ_[p] (n + 1)) :
    cartier p hp7 (numeratorToClosed p hp7 n A) =
      normalizedSum p hp7 (n + 1) (by omega) (raisedInput p hp7 n A) := by
  rw [cartier_numerator]
  apply completed_factorial_cancel p hp7 n
  change (n.factorial : ℤ_[p]) • generatorImage p hp7 n A =
    (n.factorial : ℤ_[p]) • normalizedSum p hp7 (n + 1) _ (raisedInput p hp7 n A)
  rw [normalizedSum_eq_clearedSeriesMap]
  unfold raisedInput
  rw [clearedSeriesMap_common_pole]
  simpa only [Nat.add_sub_cancel] using generatorImage_factorial_cleared
    p hp7 n (n + 1) A (height_le_pole p n)

theorem numeratorToClosed_as_normalized_pole (n : ℕ)
    (A : numeratorFiltration ℤ_[p] (n + 1)) :
    (numeratorToClosed p hp7 n A).val =
      (n.factorial : ℤ_[p]) • poleLinearMap u (p * (n + 1)) (raisedInput p hp7 n A).val := by
  change factorialNumeratorMap u n A.val = _
  rw [factorialNumeratorMap_as_pole, map_smul]
  have hr := poleLinearMap_raise u (n + 1) (p * (n + 1) - (n + 1)) A.val
  rw [Nat.add_sub_of_le (pole_bound p n)] at hr
  change (n.factorial : ℤ_[p]) • poleLinearMap u (n + 1) A.val =
    (n.factorial : ℤ_[p]) • poleLinearMap u (p * (n + 1))
      (A.val * torusPolynomial u ^ (p * (n + 1) - (n + 1)))
  rw [hr]

def derivativeIndex (n : ℕ) : ℕ := p * (n + 1 + 1) - 1

theorem derivativeIndex_succ (n : ℕ) : derivativeIndex p n + 1 = p * (n + 1 + 1) := by
  have hp := (Fact.out : p.Prime).pos
  have hn : 0 < p * (n + 1 + 1) := Nat.mul_pos hp (by omega)
  unfold derivativeIndex
  omega

def derivativeInput (i : Fin 5) (n : ℕ)
    (A : numeratorFiltration ℤ_[p] (n + 1)) :
    numeratorFiltration ℤ_[p] (derivativeIndex p n + 1) :=
  ⟨derivativeNumerator p hp7 i (n + 1) (raisedInput p hp7 n A).val, by
    rw [derivativeIndex_succ]
    exact derivativeNumerator_supported p hp7 i (n + 1) _ (raisedInput p hp7 n A).property⟩

theorem derivative_actual_scaled (i : Fin 5) (n : ℕ)
    (A : numeratorFiltration ℤ_[p] (n + 1)) :
    ((derivativeIndex p n).factorial : ℤ_[p]) •
      DClosed u i (numeratorToClosed p hp7 n A) =
      (n.factorial : ℤ_[p]) • numeratorToClosed p hp7 (derivativeIndex p n)
        (derivativeInput p hp7 i n A) := by
  apply Subtype.ext
  change ((derivativeIndex p n).factorial : ℤ_[p]) •
    actualD u i (numeratorToClosed p hp7 n A).val =
      (n.factorial : ℤ_[p]) • factorialNumeratorMap u (derivativeIndex p n)
        (derivativeInput p hp7 i n A).val
  rw [numeratorToClosed_as_normalized_pole, Derivation.map_smul,
    actualD_normalized_pole p hp7 i (n + 1) (by omega),
    factorialNumeratorMap_as_pole, map_smul]
  simp only [derivativeInput, derivativeIndex_succ]
  exact smul_comm _ _ _

theorem derivativeIndex_height (n : ℕ) :
    height p (derivativeIndex p n) ≤ n + 1 + 1 := by
  have hp := (Fact.out : p.Prime).pos
  have ht : derivativeIndex p n < (n + 1 + 1) * p := by
    have hs := derivativeIndex_succ p n
    rw [Nat.mul_comm] at hs
    omega
  have hdiv : derivativeIndex p n / p < n + 1 + 1 :=
    (Nat.div_lt_iff_lt_mul hp).mpr ht
  unfold height
  omega

set_option maxHeartbeats 800000 in
theorem cartier_derivativeInput_cleared (i : Fin 5) (n : ℕ)
    (A : numeratorFiltration ℤ_[p] (n + 1)) :
    ((n + 1).factorial : ℤ_[p]) •
      cartier p hp7 (numeratorToClosed p hp7 (derivativeIndex p n)
        (derivativeInput p hp7 i n A)) =
      ((derivativeIndex p n).factorial : ℤ_[p]) •
        normalizedSum p hp7 (n + 1 + 1) (by omega)
          (derivativeFilteredNumerator p hp7 i (n + 1) (raisedInput p hp7 n A)) := by
  have hh : 1 ≤ n + 1 + 1 := by omega
  have hbound : derivativeIndex p n + 1 ≤ p * (n + 1 + 1) :=
    (derivativeIndex_succ p n).le
  have hs : ((n + 1).factorial : ℤ_[p]) •
      generatorImage p hp7 (derivativeIndex p n) (derivativeInput p hp7 i n A) =
        ((derivativeIndex p n).factorial : ℤ_[p]) •
          clearedSeriesMap p hp7 (derivativeIndex p n + 1) (n + 1 + 1)
            hh hbound (derivativeInput p hp7 i n A) := by
    simpa only [Nat.add_sub_cancel] using generatorImage_factorial_cleared
      p hp7 (derivativeIndex p n) (n + 1 + 1) (derivativeInput p hp7 i n A)
        (derivativeIndex_height p n)
  have hseries : clearedSeriesMap p hp7 (derivativeIndex p n + 1) (n + 1 + 1)
        hh hbound (derivativeInput p hp7 i n A) =
      normalizedSum p hp7 (n + 1 + 1) hh
        (derivativeFilteredNumerator p hp7 i (n + 1) (raisedInput p hp7 n A)) := by
    have ht := clearedSeriesMap_transport p hp7 (derivativeIndex p n + 1)
      (p * (n + 1 + 1)) (n + 1 + 1) (derivativeIndex_succ p n) hh hbound le_rfl
      (derivativeInput p hp7 i n A)
      (derivativeFilteredNumerator p hp7 i (n + 1) (raisedInput p hp7 n A)) rfl
    exact ht.trans (normalizedSum_eq_clearedSeriesMap p hp7 (n + 1 + 1) hh
      (derivativeFilteredNumerator p hp7 i (n + 1) (raisedInput p hp7 n A))).symm
  calc
    _ = ((n + 1).factorial : ℤ_[p]) •
        generatorImage p hp7 (derivativeIndex p n) (derivativeInput p hp7 i n A) :=
      congrArg (fun z : Completed p hp7 => ((n + 1).factorial : ℤ_[p]) • z)
        (cartier_numerator p hp7 (derivativeIndex p n) (derivativeInput p hp7 i n A))
    _ = _ := hs.trans (congrArg
      (fun z : Completed p hp7 => ((derivativeIndex p n).factorial : ℤ_[p]) • z) hseries)

/-- Actual module commutation on every factorial numerator. Both finite
factorials are cancelled only in the checked actual completion. -/
theorem cartier_numerator_derivative (i : Fin 5) (n : ℕ)
    (A : numeratorFiltration ℤ_[p] (n + 1)) :
    cartier p hp7 (DClosed u i (numeratorToClosed p hp7 n A)) =
      (p : ℤ_[p]) • completeMap (p : ℤ_[p]) (DClosed u i)
        (cartier p hp7 (numeratorToClosed p hp7 n A)) := by
  let d := completeMap (p : ℤ_[p]) (DClosed u i)
  let E := normalizedSum p hp7 (n + 1) (by omega) (raisedInput p hp7 n A)
  let E' := normalizedSum p hp7 (n + 1 + 1) (by omega)
    (derivativeFilteredNumerator p hp7 i (n + 1) (raisedInput p hp7 n A))
  have hE : cartier p hp7 (numeratorToClosed p hp7 n A) = E :=
    cartier_numerator_eq_normalizedSum p hp7 n A
  have hE' : E' = (((n + 1 : ℕ) : ℤ_[p]) * (p : ℤ_[p])) • d E :=
    normalizedSum_derivative p hp7 i (n + 1) (by omega) (raisedInput p hp7 n A)
  have hscale := congrArg (cartier p hp7) (derivative_actual_scaled p hp7 i n A)
  simp only [map_smul] at hscale
  have hq := cartier_derivativeInput_cleared p hp7 i n A
  have hf : ((n + 1).factorial : ℤ_[p]) = ((n + 1 : ℕ) : ℤ_[p]) * (n.factorial : ℤ_[p]) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
  apply completed_factorial_cancel p hp7 (n + 1)
  apply completed_factorial_cancel p hp7 (derivativeIndex p n)
  change ((derivativeIndex p n).factorial : ℤ_[p]) •
      (((n + 1).factorial : ℤ_[p]) • cartier p hp7 (DClosed u i (numeratorToClosed p hp7 n A))) =
    ((derivativeIndex p n).factorial : ℤ_[p]) •
      (((n + 1).factorial : ℤ_[p]) • ((p : ℤ_[p]) • d (cartier p hp7 (numeratorToClosed p hp7 n A))))
  calc
    _ = ((n + 1).factorial : ℤ_[p]) •
        (((derivativeIndex p n).factorial : ℤ_[p]) •
          cartier p hp7 (DClosed u i (numeratorToClosed p hp7 n A))) := smul_comm _ _ _
    _ = ((n + 1).factorial : ℤ_[p]) •
        ((n.factorial : ℤ_[p]) • cartier p hp7
          (numeratorToClosed p hp7 (derivativeIndex p n) (derivativeInput p hp7 i n A))) := by rw [hscale]
    _ = (n.factorial : ℤ_[p]) •
        (((n + 1).factorial : ℤ_[p]) • cartier p hp7
          (numeratorToClosed p hp7 (derivativeIndex p n) (derivativeInput p hp7 i n A))) := smul_comm _ _ _
    _ = (n.factorial : ℤ_[p]) • (((derivativeIndex p n).factorial : ℤ_[p]) • E') := by rw [hq]
    _ = _ := by
      rw [hE', hE, hf]
      simp only [smul_smul]
      congr 1
      ring

theorem presentationToClosed_sum (v : ClosedPresentation ℤ_[p]) :
    presentationToClosed u v = ∑ i ∈ v.support,
      v i • (⟨presentationGenerator u i, presentationGenerator_mem u i⟩ : FClosed u) := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  rfl

/-- The actual operator, not a supplied map with a commutation field. -/
theorem cartier_derivative (i : Fin 5) (g : FClosed u) :
    cartier p hp7 (DClosed u i g) =
      (p : ℤ_[p]) • completeMap (p : ℤ_[p]) (DClosed u i) (cartier p hp7 g) := by
  let L := (cartier p hp7).comp (DClosed u i)
  let T := (p : ℤ_[p]) • ((completeMap (p : ℤ_[p]) (DClosed u i)).comp (cartier p hp7))
  have hindex (j : ClosedIndex) :
      L ⟨presentationGenerator u j, presentationGenerator_mem u j⟩ =
        T ⟨presentationGenerator u j, presentationGenerator_mem u j⟩ := by
    exact cartier_numerator_derivative p hp7 i j.val.1 (indexNumerator p j)
  change L g = T g
  obtain ⟨v, rfl⟩ := presentationToClosed_surjective u g
  rw [presentationToClosed_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, map_smul, hindex]

theorem completedCartier_derivative (i : Fin 5) :
    (completedCartier p hp7).comp (completeMap (p : ℤ_[p]) (DClosed u i)) =
      (p : ℤ_[p]) • ((completeMap (p : ℤ_[p]) (DClosed u i)).comp (completedCartier p hp7)) :=
  AdicSeries.extension_intertwines (p : ℤ_[p]) (p : ℤ_[p]) (cartier p hp7) (DClosed u i)
    (cartier_derivative p hp7 i)

theorem completedCartier_derivative_apply (i : Fin 5) (g : Completed p hp7) :
    completedCartier p hp7 (completeMap (p : ℤ_[p]) (DClosed u i) g) =
      (p : ℤ_[p]) • completeMap (p : ℤ_[p]) (DClosed u i) (completedCartier p hp7 g) :=
  DFunLike.congr_fun (completedCartier_derivative p hp7 i) g

end

end WPCompletedCartier.DerivativeDescent
