import WPReview.ResidueNumeratorOperators

noncomputable section

namespace WPReview.ResidueClosedConnection

open scoped BigOperators
open WPResidueQuotient
open WPReview.ResidueNumeratorOperators

variable (K : Type*) [CommRing K]

abbrev Coeff := ResidueConnection.Coeff K
abbrev Residue := ResidueConnection.Residue K
abbrev Space := (Fin 5 → Coeff K) × (Fin 6 → Coeff K)

def boundarySection (h6 : IsUnit (6 : K)) : (Fin 6 → Coeff K) →ₗ[Coeff K] Residue K :=
  Fintype.linearCombination (Coeff K) (ActualConnection.correctedBoundary K h6)

theorem boundarySection_apply (h6 : IsUnit (6 : K)) (v : Fin 6 → Coeff K) :
    boundarySection K h6 v =
      ∑ i : Fin 6, v i • ActualConnection.correctedBoundary K h6 i :=
  Fintype.linearCombination_apply _ _ _

def boundaryNabla : (Fin 6 → Coeff K) →ₗ[K] (Fin 6 → Coeff K) :=
  (LinearMap.pi (fun i : Fin 6 =>
    (Parameter.theta (K := K)).toLinearMap.comp (LinearMap.proj i))) - LinearMap.id

theorem boundaryNabla_apply (v : Fin 6 → Coeff K) (i : Fin 6) :
    boundaryNabla K v i = (Parameter.theta (K := K)) (v i) - v i := rfl

theorem boundarySection_connection (h6 : IsUnit (6 : K)) (v : Fin 6 → Coeff K) :
    ActualConnection.quotientTheta K (boundarySection K h6 v) =
      boundarySection K h6 (boundaryNabla K v) := by
  rw [boundarySection_apply, map_sum, boundarySection_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ActualConnection.quotientTheta_smul,
    ActualConnection.quotientTheta_correctedBoundary_actual K h6]
  simp only [boundaryNabla_apply, smul_neg, sub_smul]
  rfl

def fullSection (h6 : IsUnit (6 : K)) : Space K →ₗ[Coeff K] Residue K :=
  (ResidueConnection.gammaSection K).comp (LinearMap.fst _ _ _) +
    (boundarySection K h6).comp (LinearMap.snd _ _ _)

theorem fullSection_apply (h6 : IsUnit (6 : K)) (v : Space K) :
    fullSection K h6 v = ResidueConnection.gammaSection K v.1 +
      boundarySection K h6 v.2 := rfl

def fullNabla : Space K →ₗ[K] Space K :=
  (ResidueConnection.gammaNabla K).prodMap (boundaryNabla K)

theorem fullSection_connection (h6 : IsUnit (6 : K)) (v : Space K) :
    ActualConnection.quotientTheta K (fullSection K h6 v) =
      fullSection K h6 (fullNabla K v) := by
  rw [fullSection_apply, map_add, ResidueConnection.gammaSection_connection K h6,
    boundarySection_connection K h6, fullSection_apply]
  rfl

theorem actual_boundary_eq_family (i : Fin 6) :
    ActualConnection.qBoundary K i =
      Actual.elevenQuotientFamily (ActualConnection.parameter K) (Fin.natAdd 5 i) := by
  rw [Actual.elevenQuotientFamily_right]
  rfl

theorem rawSection_append (v : Fin 5 → Coeff K) (w : Fin 6 → Coeff K) :
    Actual.elevenQuotientSection (ActualConnection.parameter K) (Fin.append v w) =
      ResidueConnection.gammaSection K v +
        ∑ i : Fin 6, w i • ActualConnection.qBoundary K i := by
  rw [Actual.elevenQuotientSection_apply, Fin.sum_univ_add (a := 5) (b := 6),
    ResidueConnection.gammaSection_apply]
  simp only [Fin.append_left, Fin.append_right, Actual.elevenQuotientFamily_left,
    ← ResidueConnection.actual_qGamma_eq_family, ← actual_boundary_eq_family]

theorem fullSection_raw (h6 : IsUnit (6 : K)) (v : Space K) :
    fullSection K h6 v =
      Actual.elevenQuotientSection (ActualConnection.parameter K)
        (Fin.append
          (v.1 - Pi.single 0 (ActualConnection.boundaryScalar K h6 * ∑ i, v.2 i)) v.2) := by
  rw [fullSection_apply, boundarySection_apply, rawSection_append,
    map_sub, ResidueConnection.gammaSection_apply]
  simp only [ActualConnection.correctedBoundary, smul_sub, smul_smul,
    Finset.sum_sub_distrib]
  have hs : (∑ i : Fin 6,
      (v.2 i * ActualConnection.boundaryScalar K h6) • ActualConnection.qGamma K 0) =
      (ActualConnection.boundaryScalar K h6 * ∑ i, v.2 i) •
        ActualConnection.qGamma K 0 := by
    rw [← Finset.sum_smul, ← Finset.sum_mul, mul_comm]
  rw [hs]
  classical
  have hsingle : ResidueConnection.gammaSection K
      (Pi.single (0 : Fin 5) (ActualConnection.boundaryScalar K h6 * ∑ j, v.2 j)) =
      (ActualConnection.boundaryScalar K h6 * ∑ j, v.2 j) •
        ActualConnection.qGamma K 0 := by
    rw [ResidueConnection.gammaSection, Fintype.linearCombination_apply_single]
    rfl
  rw [hsingle]
  abel

def startedClassOperators (base : Fin 6 → ℕ) (x : Residue K) :
    List (Fin 6) → Residue K
  | [] => x
  | i :: w => ActualConnection.quotientTheta K (startedClassOperators base x w) -
      (6 * ((base i + wordExponent w i : ℕ) : Coeff K)) • startedClassOperators base x w

theorem add_wordExponent (base : Fin 6 → ℕ) (i : Fin 6) (w : List (Fin 6)) :
    addNumeratorExponent (base + wordExponent w) i = base + wordExponent (i :: w) := by
  simp only [wordExponent, addNumeratorExponent]
  abel

/-- The same exact raising identity also applies to a genuine closed
boundary seed; its total-degree shift is accounted for at every step. -/
theorem started_word_numerator (base : Fin 6 → ℕ) (n : ℕ)
    (hb : (∑ i, base i) ≤ n + 1) (w : List (Fin 6)) :
    scaledNumerator K (base + wordExponent w) (n + w.length)
        (by simp only [Pi.add_apply, Finset.sum_add_distrib, wordExponent_sum]; omega) =
      startedClassOperators K base (scaledNumerator K base n hb) w := by
  induction w with
  | nil =>
    have hz : base + wordExponent ([] : List (Fin 6)) = base := by
      funext i
      simp [wordExponent]
    simp only [hz, List.length_nil, Nat.add_zero, startedClassOperators]
  | cons i w ih =>
    have hs := scaled_numerator_raising K (base + wordExponent w) i (n + w.length)
      (by simp only [Pi.add_apply, Finset.sum_add_distrib, wordExponent_sum]; omega)
    rw [ih] at hs
    simpa only [add_wordExponent, List.length_cons, Nat.add_assoc,
      Pi.add_apply, startedClassOperators] using hs

def startedCoordinateOperators (base : Fin 6 → ℕ) (v : Space K) :
    List (Fin 6) → Space K
  | [] => v
  | i :: w => fullNabla K (startedCoordinateOperators base v w) -
      (6 * ((base i + wordExponent w i : ℕ) : Coeff K)) •
        startedCoordinateOperators base v w

theorem started_coordinate_transport (h6 : IsUnit (6 : K))
    (base : Fin 6 → ℕ) (v : Space K) (w : List (Fin 6)) :
    fullSection K h6 (startedCoordinateOperators K base v w) =
      startedClassOperators K base (fullSection K h6 v) w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [startedCoordinateOperators, startedClassOperators, map_sub, map_smul]
    rw [← fullSection_connection K h6, ih]

def boundaryStart (h6 : IsUnit (6 : K)) (i : Fin 6) : Space K :=
  (Pi.single 0 (ActualConnection.boundaryScalar K h6), Pi.single i 1)

theorem fullSection_boundaryStart (h6 : IsUnit (6 : K)) (i : Fin 6) :
    fullSection K h6 (boundaryStart K h6 i) = ActualConnection.qBoundary K i := by
  classical
  rw [fullSection_apply]
  change ResidueConnection.gammaSection K (Pi.single 0 (ActualConnection.boundaryScalar K h6)) +
    boundarySection K h6 (Pi.single i 1) = _
  rw [ResidueConnection.gammaSection, boundarySection,
    Fintype.linearCombination_apply_single, Fintype.linearCombination_apply_single, one_smul]
  simp only [ActualConnection.correctedBoundary, Fin.val_zero]
  abel

theorem numerator_boundary_single (i : Fin 6) :
    qNumerator K (Pi.single i 1) 0 (by simp) = ActualConnection.qBoundary K i := by
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  change numeratorGenerator (ActualConnection.parameter K) (Pi.single i 1) 0 =
    b (ActualConnection.parameter K) i
  have he : Pi.single i 1 = addNumeratorExponent (0 : Fin 6 → ℕ) i := by
    simp [addNumeratorExponent]
  rw [he, numeratorGenerator_add]
  simp only [Pi.zero_apply, Nat.cast_zero, ActualConnection.actualMonomial_zero,
    one_mul, factorialPole, Nat.factorial_zero, Nat.cast_one, b, Nat.zero_add, pow_one]

theorem actual_boundary_word_coordinates (h6 : IsUnit (6 : K)) (i : Fin 6)
    (w : List (Fin 6)) :
    fullSection K h6
      (startedCoordinateOperators K (Pi.single i 1)
        ((6 * ActualConnection.parameter K) • boundaryStart K h6 i) w) =
      scaledNumerator K (Pi.single i 1 + wordExponent w) w.length
        (by simp only [Pi.add_apply, Finset.sum_add_distrib, wordExponent_sum]; simp; omega) := by
  rw [started_coordinate_transport K h6, map_smul, fullSection_boundaryStart]
  have hs := started_word_numerator K (Pi.single i 1) 0 (by simp) w
  have hstart : scaledNumerator K (Pi.single i 1) 0 (by simp) =
      (6 * ActualConnection.parameter K) • ActualConnection.qBoundary K i := by
    simp [scaledNumerator, numerator_boundary_single, ResidueNumeratorOperators.parameter]
  rw [hstart] at hs
  simpa only [Nat.zero_add] using hs.symm

def boundaryWordCoordinates (h6 : IsUnit (6 : K)) (i : Fin 6)
    (w : List (Fin 6)) : Space K :=
  (ActualConnection.boundaryScalar K h6) ^ (w.length + 1) •
    startedCoordinateOperators K (Pi.single i 1)
      ((6 * ActualConnection.parameter K) • boundaryStart K h6 i) w

theorem actual_unscaled_boundary_word_coordinates (h6 : IsUnit (6 : K))
    (i : Fin 6) (w : List (Fin 6)) :
    fullSection K h6 (boundaryWordCoordinates K h6 i w) =
      qNumerator K (Pi.single i 1 + wordExponent w) w.length
        (by simp only [Pi.add_apply, Finset.sum_add_distrib, wordExponent_sum]; simp; omega) := by
  have hsum : (∑ j : Fin 6, ((Pi.single i 1 : Fin 6 → ℕ) + wordExponent w) j) = w.length + 1 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, wordExponent_sum]
    simp
    omega
  rw [boundaryWordCoordinates, map_smul, actual_boundary_word_coordinates K h6,
    scaledNumerator]
  simp only [hsum]
  rw [smul_smul, ← mul_pow,
    mul_comm (ActualConnection.boundaryScalar K h6),
    ActualConnection.six_parameter_mul_boundaryScalar, one_pow, one_smul]

section Integral

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)

include hp in
theorem integral_rawSection_injective :
    Function.Injective (Actual.elevenQuotientSection (ActualConnection.parameter ℤ_[p])) := by
  exact (Actual.integralQuotientEquiv p hp).injective

theorem integral_fullSection_injective :
    Function.Injective (fullSection ℤ_[p] (Parameter.padic_six_unit p hp)) := by
  intro v w h
  rw [fullSection_raw, fullSection_raw] at h
  have he := integral_rawSection_injective p hp h
  have hr : v.2 = w.2 := by
    funext i
    simpa only [Fin.append_right] using congrFun he (Fin.natAdd 5 i)
  apply Prod.ext
  · funext i
    have hi := congrFun he (Fin.castAdd 6 i)
    simp only [Fin.append_left, Pi.sub_apply, hr] at hi
    exact sub_left_injective hi
  · exact hr

set_option maxHeartbeats 1000000 in
theorem integral_fullSection_surjective :
    Function.Surjective (fullSection ℤ_[p] (Parameter.padic_six_unit p hp)) := by
  intro x
  obtain ⟨c, hc⟩ := (Actual.integralQuotientEquiv p hp).surjective x
  let left : Fin 5 → Coeff ℤ_[p] := fun i => c (Fin.castAdd 6 i)
  let right : Fin 6 → Coeff ℤ_[p] := fun i => c (Fin.natAdd 5 i)
  let b : Coeff ℤ_[p] := ActualConnection.boundaryScalar ℤ_[p]
    (Parameter.padic_six_unit p hp) * ∑ i, right i
  refine ⟨(left + Pi.single 0 b, right), ?_⟩
  rw [fullSection_raw]
  change Actual.elevenQuotientSection (ActualConnection.parameter ℤ_[p])
    (Fin.append (left + Pi.single 0 b - Pi.single 0 b) right) = x
  rw [add_sub_cancel_right]
  have he : Fin.append left right = c := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; exact Fin.append_left _ _ _
    · intro j; exact Fin.append_right _ _ _
  rw [he]
  exact hc

/-- This equivalence uses the actual eleven-class residue proof. The six
corrected boundary classes have actual eigenvalue -1. -/
def integralFullEquiv : Space ℤ_[p] ≃ₗ[Coeff ℤ_[p]] Residue ℤ_[p] :=
  LinearEquiv.ofBijective (fullSection ℤ_[p] (Parameter.padic_six_unit p hp))
    ⟨integral_fullSection_injective p hp, integral_fullSection_surjective p hp⟩

theorem integralFullEquiv_connection (v : Space ℤ_[p]) :
    ActualConnection.quotientTheta ℤ_[p] (integralFullEquiv p hp v) =
      integralFullEquiv p hp (fullNabla ℤ_[p] v) :=
  fullSection_connection ℤ_[p] (Parameter.padic_six_unit p hp) v

theorem integral_actual_unscaled_boundary_word_coordinates (i : Fin 6)
    (w : List (Fin 6)) (v : Space ℤ_[p]) :
    qNumerator ℤ_[p] (Pi.single i 1 + wordExponent w) w.length
        (by simp only [Pi.add_apply, Finset.sum_add_distrib, wordExponent_sum]; simp; omega) =
      fullSection ℤ_[p] (Parameter.padic_six_unit p hp) v ↔
        boundaryWordCoordinates ℤ_[p] (Parameter.padic_six_unit p hp) i w = v := by
  rw [← actual_unscaled_boundary_word_coordinates ℤ_[p] (Parameter.padic_six_unit p hp)]
  exact (integral_fullSection_injective p hp).eq_iff

end Integral

end WPReview.ResidueClosedConnection
