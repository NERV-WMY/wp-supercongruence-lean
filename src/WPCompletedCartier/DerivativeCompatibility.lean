import WPCompletedCartier.NumericalTerms
import WPCompletedCartier.FiniteCompatibility
import WPCompletedCartier.AdicSeries
import WPResidueQuotient.VertexExact

namespace WPCompletedCartier.DerivativeCompatibility

noncomputable section
open scoped BigOperators
open WPResidueQuotient WPCompletedCartier.NumericalTerms
open WPResidueQuotient.Adic

section ActualDifferentiation

variable {R : Type*} [CommRing R]

/-- The actual localized logarithmic derivative retains the denominator
derivative, including its sign and its next factorial pole. -/
theorem actualD_factorialNumeratorMap (u : R) (i : Fin 5) (n : ℕ)
    (Q : WPResidueQuotient.LaurentPolynomial R) :
    actualD u i (factorialNumeratorMap u n Q) =
      factorialNumeratorMap u n (logarithmicDerivation (coordinateWeight i) Q) -
        factorialNumeratorMap u (n + 1)
          (Q * logarithmicDerivation (coordinateWeight i) (torusPolynomial u)) := by
  rw [factorialNumeratorMap_apply, Derivation.leibniz,
    actualD_algebraMap_numerator, actualD_factorialPole,
    factorialNumeratorMap_apply, factorialNumeratorMap_apply, map_mul,
    logarithmicDerivation_f]
  simp only [map_neg, map_mul, map_sub, actualVertex]
  rw [← IsScalarTower.algebraMap_apply R
    (WPResidueQuotient.LaurentPolynomial R) (ActualRing u)]
  ring

theorem actualD_gammaNumeratorMap (u : R) (i : Fin 5) (h : ℕ) (hh : 1 ≤ h)
    (Q : WPResidueQuotient.LaurentPolynomial R) :
    actualD u i (gammaNumeratorMap u h Q) =
      gammaNumeratorMap u h (logarithmicDerivation (coordinateWeight i) Q) -
        gammaNumeratorMap u (h + 1)
          (Q * logarithmicDerivation (coordinateWeight i) (torusPolynomial u)) := by
  rw [gammaNumeratorMap_eq_factorial u h hh,
    gammaNumeratorMap_eq_factorial u (h + 1) (by omega)]
  simpa only [Nat.add_sub_cancel, Nat.sub_add_cancel hh] using
    actualD_factorialNumeratorMap u i (h - 1) Q

theorem logarithmicPoleNumerator_eq (u : R) (i : Fin 5) (m : ℕ)
    (B : WPResidueQuotient.LaurentPolynomial R) :
    logarithmicPoleNumerator u i m B =
      logarithmicDerivation (coordinateWeight i) B * torusPolynomial u -
        (m : R) • (B * logarithmicDerivation (coordinateWeight i) (torusPolynomial u)) := by
  unfold logarithmicPoleNumerator
  rw [logarithmicDerivation_f]
  have hv : (Fin.last 5 : Fin 6) = (5 : Fin 6) := rfl
  rw [hv]
  simp only [Algebra.smul_def]
  ring

theorem actualD_poleLinearMap (u : R) (i : Fin 5) (m : ℕ) (hm : 1 ≤ m)
    (B : WPResidueQuotient.LaurentPolynomial R) :
    actualD u i (poleLinearMap u m B) =
      poleLinearMap u (m + 1)
        (logarithmicDerivation (coordinateWeight i) B * torusPolynomial u -
          (m : R) • (B * logarithmicDerivation (coordinateWeight i) (torusPolynomial u))) := by
  have hs := actualD_poleLinearMap_succ u i (m - 1) B
  rw [Nat.sub_add_cancel hm, logarithmicPoleNumerator_eq] at hs
  have he : m - 1 + 2 = m + 1 := by omega
  rw [he] at hs
  exact hs

end ActualDifferentiation

variable (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)

local notation "u" => Parameter.integralTenth p hp7
local notation "κ" => kappa p (Nat.Prime.pos (Fact.out : p.Prime))
local notation "α" => factorialTail p hp7

def normalizedTerm (h : ℕ) (B : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (k : ℕ) : ActualRing u :=
  α k • gammaNumeratorMap u (h + k) (κ (B * G p hp7 ^ k))

def derivativeNumerator (i : Fin 5) (h : ℕ)
    (B : WPResidueQuotient.LaurentPolynomial ℤ_[p]) :
    WPResidueQuotient.LaurentPolynomial ℤ_[p] :=
  f p hp7 ^ p * logarithmicDerivation (coordinateWeight i) B -
    (h : ℤ_[p]) • (B * logarithmicDerivation (coordinateWeight i) (f p hp7 ^ p))

theorem derivativeNumerator_supported (i : Fin 5) (h : ℕ)
    (B : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hB : B ∈ numeratorFiltration ℤ_[p] (p * h)) :
    derivativeNumerator p hp7 i h B ∈ numeratorFiltration ℤ_[p] (p * (h + 1)) := by
  have hf : f p hp7 ^ p ∈ numeratorFiltration ℤ_[p] p :=
    torusPolynomial_pow_mem_numeratorFiltration u p
  unfold derivativeNumerator
  apply (numeratorFiltration ℤ_[p] (p * (h + 1))).sub_mem
  · have hm := numeratorFiltration_mul hf
      (logarithmicDerivation_preserves_numeratorFiltration (coordinateWeight i) _ hB)
    convert hm using 1
    ring
  · apply (numeratorFiltration ℤ_[p] (p * (h + 1))).smul_mem
    have hm := numeratorFiltration_mul hB
      (logarithmicDerivation_preserves_numeratorFiltration (coordinateWeight i) _ hf)
    convert hm using 1
    ring

/-- Differentiating the actual divided error retains both occurrences of p. -/
theorem derivative_denominator_error (i : Fin 5) :
    logarithmicDerivation (coordinateWeight i) (f p hp7 ^ p) =
      (p : ℤ_[p]) • phi p (logarithmicDerivation (coordinateWeight i) (f p hp7)) -
        (p : ℤ_[p]) • logarithmicDerivation (coordinateWeight i) (G p hp7) := by
  have hg := congrArg (logarithmicDerivation (coordinateWeight i)) (G_scaled p hp7)
  rw [Derivation.map_smul, map_sub, logarithmicDerivation_phi] at hg
  exact (eq_sub_iff_add_eq).mpr (by
    rw [add_comm]
    exact (eq_sub_iff_add_eq).mp hg)

/-- The normalized differentiated numerator is an equality of actual
localized fractions, before Cartier or completion is applied. -/
theorem actualD_normalized_pole (i : Fin 5) (h : ℕ) (hh : 1 ≤ h)
    (B : WPResidueQuotient.LaurentPolynomial ℤ_[p]) :
    actualD u i (poleLinearMap u (p * h) B) =
      poleLinearMap u (p * (h + 1)) (derivativeNumerator p hp7 i h B) := by
  have hp := (Fact.out : p.Prime).pos
  have hph : 1 ≤ p * h := Nat.mul_pos hp hh
  let Q := logarithmicDerivation (coordinateWeight i) B * f p hp7 -
    ((p * h : ℕ) : ℤ_[p]) •
      (B * logarithmicDerivation (coordinateWeight i) (f p hp7))
  have hPow : f p hp7 ^ p = f p hp7 ^ (p - 1) * f p hp7 := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  have hD : logarithmicDerivation (coordinateWeight i) (f p hp7 ^ p) =
      (p : ℤ_[p]) • (f p hp7 ^ (p - 1) * logarithmicDerivation (coordinateWeight i) (f p hp7)) := by
    rw [Derivation.leibniz_pow]
    simp only [Algebra.smul_def, Algebra.algebraMap_self_apply, map_natCast]
    rw [_root_.eq_natCast (algebraMap ℕ (WPResidueQuotient.LaurentPolynomial ℤ_[p])) p]
  have hH : derivativeNumerator p hp7 i h B = Q * f p hp7 ^ (p - 1) := by
    unfold derivativeNumerator Q
    rw [hD, hPow]
    simp only [Algebra.smul_def, Nat.cast_mul, map_mul]
    ring
  rw [actualD_poleLinearMap u i (p * h) hph B, hH]
  have hs := poleLinearMap_raise u (p * h + 1) (p - 1) Q
  have he : p * h + 1 + (p - 1) = p * (h + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [he] at hs
  exact hs.symm

theorem normalizedTerm_derivative (i : Fin 5) (h : ℕ) (hh : 1 ≤ h)
    (B : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (k : ℕ) :
    (p : ℤ_[p]) • actualD u i (normalizedTerm p hp7 h B k) =
      α k • gammaNumeratorMap u (h + k)
        (κ (logarithmicDerivation (coordinateWeight i) (B * G p hp7 ^ k))) -
      ((p : ℤ_[p]) * α k) • gammaNumeratorMap u (h + k + 1)
        (κ (B * G p hp7 ^ k) * logarithmicDerivation (coordinateWeight i) (f p hp7)) := by
  unfold normalizedTerm
  rw [Derivation.map_smul, actualD_gammaNumeratorMap u i (h + k) (by omega)]
  have hk := kappa_logarithmicDerivation (R := ℤ_[p]) p
    (Fact.out : p.Prime).pos (coordinateWeight i) (B * G p hp7 ^ k)
  rw [hk, map_smul]
  simp only [smul_sub, smul_smul]
  rw [mul_comm (α k) (p : ℤ_[p])]
  simp only [f]

theorem selected_derivativeNumerator (i : Fin 5) (h k : ℕ)
    (B : WPResidueQuotient.LaurentPolynomial ℤ_[p]) :
    κ (derivativeNumerator p hp7 i h B * G p hp7 ^ k) =
      f p hp7 * κ (logarithmicDerivation (coordinateWeight i) B * G p hp7 ^ k) -
      (p : ℤ_[p]) • κ (logarithmicDerivation (coordinateWeight i) B * G p hp7 ^ (k + 1)) -
      ((h : ℤ_[p]) * (p : ℤ_[p])) •
        (κ (B * G p hp7 ^ k) * logarithmicDerivation (coordinateWeight i) (f p hp7)) +
      ((h : ℤ_[p]) * (p : ℤ_[p])) •
        κ (B * G p hp7 ^ k * logarithmicDerivation (coordinateWeight i) (G p hp7)) := by
  have hG : f p hp7 ^ p = phi p (f p hp7) - (p : ℤ_[p]) • G p hp7 := by
    exact (eq_sub_iff_add_eq).mpr (by
      rw [add_comm]
      exact (eq_sub_iff_add_eq).mp (G_scaled p hp7))
  have he : derivativeNumerator p hp7 i h B * G p hp7 ^ k =
      (logarithmicDerivation (coordinateWeight i) B * G p hp7 ^ k) * phi p (f p hp7) -
        (p : ℤ_[p]) • (logarithmicDerivation (coordinateWeight i) B * G p hp7 ^ (k + 1)) -
        ((h : ℤ_[p]) * (p : ℤ_[p])) •
          ((B * G p hp7 ^ k) * phi p (logarithmicDerivation (coordinateWeight i) (f p hp7))) +
        ((h : ℤ_[p]) * (p : ℤ_[p])) •
          (B * G p hp7 ^ k * logarithmicDerivation (coordinateWeight i) (G p hp7)) := by
    unfold derivativeNumerator
    rw [derivative_denominator_error, hG, pow_succ]
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [he, map_add, map_sub, map_sub, map_smul, map_smul, map_smul,
    kappa_mul_phi, kappa_mul_phi]
  rw [mul_comm (κ (logarithmicDerivation (coordinateWeight i) B * G p hp7 ^ k))]

set_option maxHeartbeats 800000 in
theorem logarithmic_product_power (i : Fin 5) (B : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (k : ℕ) :
    logarithmicDerivation (coordinateWeight i) (B * G p hp7 ^ k) =
      logarithmicDerivation (coordinateWeight i) B * G p hp7 ^ k +
        (k : ℤ_[p]) •
          (B * G p hp7 ^ (k - 1) * logarithmicDerivation (coordinateWeight i) (G p hp7)) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow]
  simp only [Algebra.smul_def, Algebra.algebraMap_self_apply, map_natCast]
  rw [_root_.eq_natCast (algebraMap ℕ (WPResidueQuotient.LaurentPolynomial ℤ_[p])) k]
  ring

def boundaryRaw (i : Fin 5) (h : ℕ) (B : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (k : ℕ) : ActualRing u :=
  α k • gammaNumeratorMap u (h + k)
    (κ (logarithmicDerivation (coordinateWeight i) B * G p hp7 ^ k -
      (h : ℤ_[p]) •
        (B * G p hp7 ^ (k - 1) * logarithmicDerivation (coordinateWeight i) (G p hp7))))

/-- The finite differentiated-series identity. Its only nonzero remainder
is a factorial-tail boundary; no commutation of an operator is assumed. -/
theorem normalizedTerm_derivative_telescoping (i : Fin 5) (h : ℕ) (hh : 1 ≤ h)
    (B : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (k : ℕ) :
    normalizedTerm p hp7 (h + 1) (derivativeNumerator p hp7 i h B) k =
      ((h : ℤ_[p]) * (p : ℤ_[p])) • actualD u i (normalizedTerm p hp7 h B k) +
        (k : ℤ_[p]) • boundaryRaw p hp7 i h B k -
        ((k + 1 : ℕ) : ℤ_[p]) • boundaryRaw p hp7 i h B (k + 1) := by
  rw [mul_smul, normalizedTerm_derivative p hp7 i h hh]
  unfold normalizedTerm boundaryRaw
  have he : h + 1 + k = h + k + 1 := by omega
  have hj : h + (k + 1) = h + k + 1 := by omega
  rw [he]
  simp only [Nat.add_sub_cancel]
  rw [hj]
  have hα (z : ActualRing u) :
      ((k + 1 : ℕ) : ℤ_[p]) • (α (k + 1) • z) = (p : ℤ_[p]) • (α k • z) := by
    simp only [smul_smul]
    rw [show ((k + 1 : ℕ) : ℤ_[p]) * α (k + 1) = (p : ℤ_[p]) * α k by
      simpa only [Nat.cast_add, Nat.cast_one] using factorialTail_recurrence p hp7 k]
  rw [hα, selected_derivativeNumerator, logarithmic_product_power]
  simp only [map_add, map_sub, map_smul]
  simp only [f]
  rw [gammaNumeratorMap_raise u (h + k) (by omega)]
  simp only [Nat.cast_add, smul_add, smul_sub, smul_smul]
  module

def normalizedClosedTerm (h : ℕ) (hh : 1 ≤ h)
    (B : numeratorFiltration ℤ_[p] (p * h)) (k : ℕ) : FClosed u :=
  clearedClosedTerm p hp7 B.val (p * h) h k hh le_rfl B.property

theorem normalizedClosedTerm_val (h : ℕ) (hh : 1 ≤ h)
    (B : numeratorFiltration ℤ_[p] (p * h)) (k : ℕ) :
    (normalizedClosedTerm p hp7 h hh B k).val = normalizedTerm p hp7 h B.val k := by
  unfold normalizedClosedTerm clearedClosedTerm NumericalTerms.clearedTerm normalizedTerm
  rw [gammaNumeratorMap_eq_factorial u (h + k) (by omega)]
  simp only [NumericalTerms.selectedNumerator, Nat.sub_self, pow_zero, mul_one]

theorem normalizedClosedTerm_eventual (h : ℕ) (hh : 1 ≤ h)
    (B : numeratorFiltration ℤ_[p] (p * h)) :
    AdicSeries.EventuallyDivisible (p : ℤ_[p])
      (normalizedClosedTerm p hp7 h hh B) := by
  intro n
  exact ⟨6 * n + 1, fun k hk => clearedClosedTerm_eventual p hp7 B.val
    (p * h) h hh le_rfl B.property n k hk⟩

theorem boundaryNumerator_supported (i : Fin 5) (h k : ℕ) (hk : 1 ≤ k)
    (B : numeratorFiltration ℤ_[p] (p * h)) :
    κ (logarithmicDerivation (coordinateWeight i) B.val * G p hp7 ^ k -
      (h : ℤ_[p]) • (B.val * G p hp7 ^ (k - 1) *
        logarithmicDerivation (coordinateWeight i) (G p hp7))) ∈
      numeratorFiltration ℤ_[p] (h + k) := by
  apply kappa_supported
  apply (numeratorFiltration ℤ_[p] (p * (h + k))).sub_mem
  · have hb := numeratorFiltration_mul
      (logarithmicDerivation_preserves_numeratorFiltration (coordinateWeight i) _ B.property)
      (numeratorFiltration_pow p (G_supported p hp7) k)
    convert hb using 1
    ring
  · apply (numeratorFiltration ℤ_[p] (p * (h + k))).smul_mem
    have hb := numeratorFiltration_mul
      (numeratorFiltration_mul B.property
        (numeratorFiltration_pow p (G_supported p hp7) (k - 1)))
      (logarithmicDerivation_preserves_numeratorFiltration (coordinateWeight i) _ (G_supported p hp7))
    have he : p * h + (k - 1) * p + p = p * (h + k) := by
      calc
        _ = p * h + (k - 1 + 1) * p := by ring
        _ = p * h + k * p := by rw [Nat.sub_add_cancel hk]
        _ = _ := by ring
    simpa only [he] using hb

def boundaryClosedTerm (i : Fin 5) (h : ℕ) (hh : 1 ≤ h)
    (B : numeratorFiltration ℤ_[p] (p * h)) (k : ℕ) : FClosed u :=
  if hk : 1 ≤ k then
    ⟨boundaryRaw p hp7 i h B.val k, by
      apply (FClosed u).smul_mem
      rw [gammaNumeratorMap_eq_factorial u (h + k) (by omega)]
      apply factorialNumeratorMap_mem_closed
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ h + k)] using
        boundaryNumerator_supported p hp7 i h k hk B⟩
  else 0

theorem boundaryClosedTerm_scaled_val (i : Fin 5) (h : ℕ) (hh : 1 ≤ h)
    (B : numeratorFiltration ℤ_[p] (p * h)) (k : ℕ) :
    (k : ℤ_[p]) • (boundaryClosedTerm p hp7 i h hh B k).val =
      (k : ℤ_[p]) • boundaryRaw p hp7 i h B.val k := by
  by_cases hk : 1 ≤ k
  · simp only [boundaryClosedTerm, dif_pos hk]
  · have hk0 : k = 0 := by omega
    subst k
    simp

theorem boundaryClosedTerm_eventual (i : Fin 5) (h : ℕ) (hh : 1 ≤ h)
    (B : numeratorFiltration ℤ_[p] (p * h)) :
    AdicSeries.EventuallyDivisible (p : ℤ_[p])
      (boundaryClosedTerm p hp7 i h hh B) := by
  intro n
  refine ⟨6 * n + 1, ?_⟩
  intro k hk
  have hk1 : 1 ≤ k := by omega
  obtain ⟨z, hz⟩ := (mem_powerSubmodule _ _ _).mp (factorialTail_eventual p hp7 n k hk)
  let Q := κ (logarithmicDerivation (coordinateWeight i) B.val * G p hp7 ^ k -
    (h : ℤ_[p]) • (B.val * G p hp7 ^ (k - 1) * logarithmicDerivation (coordinateWeight i) (G p hp7)))
  let q : FClosed u := ⟨gammaNumeratorMap u (h + k) Q, by
    rw [gammaNumeratorMap_eq_factorial u (h + k) (by omega)]
    apply factorialNumeratorMap_mem_closed
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ h + k)] using
      boundaryNumerator_supported p hp7 i h k hk1 B⟩
  refine ⟨z • q, ?_⟩
  apply Subtype.ext
  change (p : ℤ_[p]) ^ n • (z • q.val) = (boundaryClosedTerm p hp7 i h hh B k).val
  simp only [boundaryClosedTerm, dif_pos hk1, boundaryRaw]
  rw [← mul_smul]
  change ((p : ℤ_[p]) ^ n • z) • q.val = α k • q.val
  rw [hz]

def normalizedSum (h : ℕ) (hh : 1 ≤ h)
    (B : numeratorFiltration ℤ_[p] (p * h)) : Completion (p : ℤ_[p]) (FClosed u) :=
  AdicSeries.sum (p : ℤ_[p]) (normalizedClosedTerm p hp7 h hh B)
    (normalizedClosedTerm_eventual p hp7 h hh B)

def derivativeFilteredNumerator (i : Fin 5) (h : ℕ)
    (B : numeratorFiltration ℤ_[p] (p * h)) :
    numeratorFiltration ℤ_[p] (p * (h + 1)) :=
  ⟨derivativeNumerator p hp7 i h B.val,
    derivativeNumerator_supported p hp7 i h B.val B.property⟩

theorem normalizedClosedTerm_derivative_telescoping (i : Fin 5) (h : ℕ) (hh : 1 ≤ h)
    (B : numeratorFiltration ℤ_[p] (p * h)) (k : ℕ) :
    normalizedClosedTerm p hp7 (h + 1) (by omega)
        (derivativeFilteredNumerator p hp7 i h B) k =
      ((h : ℤ_[p]) * (p : ℤ_[p])) • DClosed u i (normalizedClosedTerm p hp7 h hh B k) +
        (k : ℤ_[p]) • boundaryClosedTerm p hp7 i h hh B k -
        ((k + 1 : ℕ) : ℤ_[p]) • boundaryClosedTerm p hp7 i h hh B (k + 1) := by
  apply Subtype.ext
  change (normalizedClosedTerm p hp7 (h + 1) _ _ k).val =
    ((h : ℤ_[p]) * (p : ℤ_[p])) • actualD u i (normalizedClosedTerm p hp7 h hh B k).val +
      (k : ℤ_[p]) • (boundaryClosedTerm p hp7 i h hh B k).val -
      ((k + 1 : ℕ) : ℤ_[p]) • (boundaryClosedTerm p hp7 i h hh B (k + 1)).val
  rw [normalizedClosedTerm_val, normalizedClosedTerm_val,
    boundaryClosedTerm_scaled_val, boundaryClosedTerm_scaled_val]
  exact normalizedTerm_derivative_telescoping p hp7 i h hh B.val k

theorem normalizedSum_derivative (i : Fin 5) (h : ℕ) (hh : 1 ≤ h)
    (B : numeratorFiltration ℤ_[p] (p * h)) :
    normalizedSum p hp7 (h + 1) (by omega) (derivativeFilteredNumerator p hp7 i h B) =
      ((h : ℤ_[p]) * (p : ℤ_[p])) •
        completeMap (p : ℤ_[p]) (DClosed u i) (normalizedSum p hp7 h hh B) := by
  let a := fun k => DClosed u i (normalizedClosedTerm p hp7 h hh B k)
  let b := normalizedClosedTerm p hp7 (h + 1) (by omega)
    (derivativeFilteredNumerator p hp7 i h B)
  let c := boundaryClosedTerm p hp7 i h hh B
  have ha := AdicSeries.eventuallyDivisible_map (p : ℤ_[p]) _
    (normalizedClosedTerm_eventual p hp7 h hh B) (DClosed u i)
  have hb := normalizedClosedTerm_eventual p hp7 (h + 1) (by omega)
    (derivativeFilteredNumerator p hp7 i h B)
  have hc := boundaryClosedTerm_eventual p hp7 i h hh B
  have hs : AdicSeries.sum (p : ℤ_[p]) b hb =
      ((h : ℤ_[p]) * (p : ℤ_[p])) • AdicSeries.sum (p : ℤ_[p]) a ha := by
    apply AdicSeries.sum_eq_of_finite_telescoping (p : ℤ_[p]) _
      (fun K => -(K : ℤ_[p])) a b c ha hb hc
    apply Filter.Eventually.of_forall
    intro K
    have htel := normalized_pascal_telescoping 0 K c
    simp only [zero_add, zero_nsmul, zero_sub] at htel
    have he : AdicSeries.partialSum b K =
        ((h : ℤ_[p]) * (p : ℤ_[p])) • AdicSeries.partialSum a K - K • c K := by
      unfold AdicSeries.partialSum
      calc
        _ = ((h : ℤ_[p]) * (p : ℤ_[p])) • (∑ k ∈ Finset.range K, a k) +
            ∑ k ∈ Finset.range K, (k • c k - (k + 1) • c (k + 1)) := by
          rw [Finset.smul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          dsimp only [a, b, c]
          rw [normalizedClosedTerm_derivative_telescoping p hp7 i h hh B k]
          simp only [Nat.cast_smul_eq_nsmul]
          abel
        _ = _ := by rw [htel]; abel
    simpa only [Nat.cast_smul_eq_nsmul, neg_smul, sub_eq_add_neg] using he
  unfold normalizedSum
  rw [AdicSeries.completeMap_sum]
  exact hs

end

end WPCompletedCartier.DerivativeCompatibility
