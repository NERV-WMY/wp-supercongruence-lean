import WPReview.ResidueConnection

noncomputable section

namespace WPReview.ResidueNumeratorOperators

open scoped BigOperators
open WPResidueQuotient

variable (K : Type*) [CommRing K]

abbrev Coeff := ActualConnection.Coeff K
abbrev parameter := ActualConnection.parameter K

def numeratorClosed (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ i, a i) ≤ n + 1) :
    FClosed (parameter K) :=
  ⟨numeratorGenerator (parameter K) a n,
    numeratorGenerator_mem_closed (parameter K) a n ha⟩

def qNumerator (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ i, a i) ≤ n + 1) :
    ClosedResidueQuotient (parameter K) :=
  Submodule.Quotient.mk (numeratorClosed K a n ha)

theorem thetaClosed_numerator (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n + 1) :
    ActualConnection.thetaClosed K (numeratorClosed K a n ha) =
      numeratorClosed K a (n + 1) (by omega) -
        (n + 1 : Coeff K) • numeratorClosed K a n ha := by
  apply Subtype.ext
  simpa only [numeratorClosed, Submodule.coe_sub, Submodule.coe_smul,
    ActualConnection.thetaClosed, LinearMap.coe_mk, AddHom.coe_mk,
    Algebra.smul_def, map_add, map_natCast, map_one] using
      ActualConnection.thetaActual_numeratorGenerator K a n

theorem quotientTheta_numerator (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n + 1) :
    ActualConnection.quotientTheta K (qNumerator K a n ha) =
      qNumerator K a (n + 1) (by omega) -
        (n + 1 : Coeff K) • qNumerator K a n ha := by
  change Submodule.Quotient.mk
    (ActualConnection.thetaClosed K (numeratorClosed K a n ha)) = _
  rw [thetaClosed_numerator]
  rfl

/-- The discarded term is the sum of actual allowed logarithmic derivatives. -/
theorem numeratorClosed_raising (a : Fin 6 → ℕ) (i : Fin 6) (n : ℕ)
    (ha : (∑ j, a j) ≤ n + 1) :
    (6 * parameter K) • numeratorClosed K (addNumeratorExponent a i) (n + 1)
        (by rw [addNumeratorExponent_sum]; omega) =
      ActualConnection.thetaClosed K (numeratorClosed K a n ha) -
        (6 * (a i : Coeff K) - ∑ j : Fin 6, (a j : Coeff K)) •
          numeratorClosed K a n ha +
        ∑ j : Fin 6, DikClosed (parameter K) i j (numeratorClosed K a n ha) := by
  apply Subtype.ext
  simp only [Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_sum, numeratorClosed, DikClosed_coe, Algebra.smul_def]
  change algebraMap (Coeff K) (ActualConnection.Ambient K) (6 * parameter K) *
      numeratorGenerator (parameter K) (addNumeratorExponent a i) (n + 1) =
    ActualConnection.thetaActual K (numeratorGenerator (parameter K) a n) -
      algebraMap (Coeff K) (ActualConnection.Ambient K)
        (6 * (a i : Coeff K) - ∑ j : Fin 6, (a j : Coeff K)) *
          numeratorGenerator (parameter K) a n +
        ∑ j : Fin 6, Dik (parameter K) i j (numeratorGenerator (parameter K) a n)
  rw [ActualConnection.thetaActual_numeratorGenerator]
  simp only [map_mul, map_ofNat, map_sub, map_sum, map_natCast]
  linear_combination numeratorReduction_identity (parameter K) a i n

theorem quotient_numerator_raising (a : Fin 6 → ℕ) (i : Fin 6) (n : ℕ)
    (ha : (∑ j, a j) ≤ n + 1) :
    (6 * parameter K) • qNumerator K (addNumeratorExponent a i) (n + 1)
        (by rw [addNumeratorExponent_sum]; omega) =
      ActualConnection.quotientTheta K (qNumerator K a n ha) -
        (6 * (a i : Coeff K) - ∑ j : Fin 6, (a j : Coeff K)) •
          qNumerator K a n ha := by
  have he : (∑ j : Fin 6, DikClosed (parameter K) i j
      (numeratorClosed K a n ha)) ∈ exactSubmodule (parameter K) :=
    (exactSubmodule (parameter K)).sum_mem
      (fun j _ => DikClosed_mem_exact (parameter K) i j _)
  have hz : Submodule.Quotient.mk
      (∑ j : Fin 6, DikClosed (parameter K) i j (numeratorClosed K a n ha)) =
        (0 : ClosedResidueQuotient (parameter K)) :=
    (Submodule.Quotient.mk_eq_zero (exactSubmodule (parameter K))).mpr he
  have h := congrArg ((exactSubmodule (parameter K)).mkQ)
    (numeratorClosed_raising K a i n ha)
  simpa only [map_add, map_sub, map_smul, Submodule.mkQ_apply,
    hz, add_zero, qNumerator, ActualConnection.quotientTheta_mk] using h

theorem theta_parameterPower (d : ℕ) :
    Parameter.theta ((6 * parameter K) ^ d) =
      (d : Coeff K) * (6 * parameter K) ^ d := by
  have ht : Parameter.theta (6 * parameter K) = 6 * parameter K := by
    have h6 : Parameter.theta (6 : Coeff K) = 0 := by
      exact (Parameter.theta (K := K)).map_natCast 6
    rw [Derivation.leibniz, h6]
    simp only [parameter, ActualConnection.parameter, Parameter.theta_u,
      smul_eq_mul, mul_zero, add_zero]
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, Derivation.leibniz, ih, ht]
    simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring

def scaledNumerator (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ i, a i) ≤ n + 1) :
    ClosedResidueQuotient (parameter K) :=
  (6 * parameter K) ^ (∑ i, a i) • qNumerator K a n ha

/-- Conjugation by the actual parameter power removes the total-degree
shift, leaving the original coordinate operator theta minus 6*a_i. -/
theorem scaled_numerator_raising (a : Fin 6 → ℕ) (i : Fin 6) (n : ℕ)
    (ha : (∑ j, a j) ≤ n + 1) :
    scaledNumerator K (addNumeratorExponent a i) (n + 1)
        (by rw [addNumeratorExponent_sum]; omega) =
      ActualConnection.quotientTheta K (scaledNumerator K a n ha) -
        (6 * (a i : Coeff K)) • scaledNumerator K a n ha := by
  unfold scaledNumerator
  simp only [addNumeratorExponent_sum, pow_succ]
  calc
    _ = (6 * parameter K) ^ (∑ j, a j) •
        ((6 * parameter K) • qNumerator K (addNumeratorExponent a i) (n + 1)
          (by rw [addNumeratorExponent_sum]; omega)) := by rw [smul_smul]
    _ = (6 * parameter K) ^ (∑ j, a j) •
        (ActualConnection.quotientTheta K (qNumerator K a n ha) -
          (6 * (a i : Coeff K) - ∑ j : Fin 6, (a j : Coeff K)) •
            qNumerator K a n ha) := by rw [quotient_numerator_raising]
    _ = _ := by
      have hm (b c t : Coeff K) (x y : ClosedResidueQuotient (parameter K)) :
          t • (y - (c - b) • x) =
            (b * t) • x + t • y - c • (t • x) := by
        simp only [smul_sub, sub_smul, smul_smul]
        rw [mul_comm t c, mul_comm t b]
        abel
      rw [ActualConnection.quotientTheta_smul, theta_parameterPower]
      simpa only [Nat.cast_sum] using hm (∑ j : Fin 6, (a j : Coeff K))
        (6 * (a i : Coeff K)) ((6 * parameter K) ^ (∑ j, a j))
          (qNumerator K a n ha) (ActualConnection.quotientTheta K (qNumerator K a n ha))

theorem scaled_numerator_zero (n : ℕ) :
    scaledNumerator K (fun _ => 0) n (by simp) = ActualConnection.qGamma K n := by
  simp only [scaledNumerator, Finset.sum_const_zero, pow_zero, one_smul]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  simp only [numeratorClosed, ActualConnection.gammaClosed, numeratorGenerator,
    Nat.cast_zero, ActualConnection.actualMonomial_zero, one_mul, Gamma_succ]

def wordExponent : List (Fin 6) → (Fin 6 → ℕ)
  | [] => fun _ => 0
  | i :: w => addNumeratorExponent (wordExponent w) i

theorem wordExponent_sum (w : List (Fin 6)) :
    (∑ i, wordExponent w i) = w.length := by
  induction w with
  | nil => simp [wordExponent]
  | cons i w ih => simp only [wordExponent, addNumeratorExponent_sum, ih, List.length_cons]

theorem wordExponent_append (v w : List (Fin 6)) :
    wordExponent (v ++ w) = wordExponent v + wordExponent w := by
  induction v with
  | nil => simp [wordExponent]; rfl
  | cons i v ih =>
    simp only [List.cons_append, wordExponent, ih, addNumeratorExponent]
    abel

theorem wordExponent_replicate (i : Fin 6) (n : ℕ) :
    wordExponent (List.replicate n i) = Pi.single i n := by
  induction n with
  | zero => simp [wordExponent]; rfl
  | succ n ih =>
    simp only [List.replicate_succ, wordExponent, ih, addNumeratorExponent]
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]

def canonicalWord (a : Fin 6 → ℕ) : List (Fin 6) :=
  List.replicate (a 0) 0 ++ List.replicate (a 1) 1 ++
    List.replicate (a 2) 2 ++ List.replicate (a 3) 3 ++
    List.replicate (a 4) 4 ++ List.replicate (a 5) 5

theorem canonicalWord_exponent (a : Fin 6 → ℕ) :
    wordExponent (canonicalWord a) = a := by
  simp only [canonicalWord, wordExponent_append, wordExponent_replicate]
  funext i
  fin_cases i <;> simp

theorem canonicalWord_length (a : Fin 6 → ℕ) :
    (canonicalWord a).length = ∑ i, a i := by
  rw [← wordExponent_sum, canonicalWord_exponent]

def classOperators (x : ClosedResidueQuotient (parameter K)) :
    List (Fin 6) → ClosedResidueQuotient (parameter K)
  | [] => x
  | i :: w => ActualConnection.quotientTheta K (classOperators x w) -
      (6 * (wordExponent w i : Coeff K)) • classOperators x w

def poleOperators : ℕ → ClosedResidueQuotient (parameter K)
  | 0 => ActualConnection.qGamma K 0
  | n + 1 => ActualConnection.quotientTheta K (poleOperators n) +
      (n + 1 : Coeff K) • poleOperators n

theorem qGamma_eq_poleOperators (n : ℕ) :
    ActualConnection.qGamma K n = poleOperators K n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [poleOperators, ← ih, ActualConnection.quotientTheta_Gamma]
    simp only [← Nat.cast_smul_eq_nsmul (Coeff K), Nat.cast_add, Nat.cast_one]
    abel

/-- Every vertex word represents its actual admissible factorial class.
The initial pole index is nonnegative, so the scope is strict interior. -/
theorem word_numerator_operators (n : ℕ) (w : List (Fin 6)) :
    scaledNumerator K (wordExponent w) (n + w.length)
        (by rw [wordExponent_sum]; omega) =
      classOperators K (ActualConnection.qGamma K n) w := by
  induction w with
  | nil => simpa only [wordExponent, List.length_nil, Nat.add_zero, classOperators]
      using scaled_numerator_zero K n
  | cons i w ih =>
    have hs := scaled_numerator_raising K (wordExponent w) i (n + w.length)
      (by rw [wordExponent_sum]; omega)
    rw [ih] at hs
    simpa only [wordExponent, List.length_cons, Nat.add_assoc, classOperators] using hs

theorem word_numerator_from_first_pole (n : ℕ) (w : List (Fin 6)) :
    scaledNumerator K (wordExponent w) (n + w.length)
        (by rw [wordExponent_sum]; omega) =
      classOperators K (poleOperators K n) w := by
  rw [word_numerator_operators, qGamma_eq_poleOperators]

def coordinateOperators (v : Fin 5 → ResidueConnection.Coeff K) :
    List (Fin 6) → (Fin 5 → ResidueConnection.Coeff K)
  | [] => v
  | i :: w => ResidueConnection.gammaNabla K (coordinateOperators v w) -
      (6 * (wordExponent w i : Coeff K)) • coordinateOperators v w

theorem actual_coordinate_operator_transport (h6 : IsUnit (6 : K))
    (v : Fin 5 → ResidueConnection.Coeff K) (w : List (Fin 6)) :
    ResidueConnection.gammaSection K (coordinateOperators K v w) =
      classOperators K (ResidueConnection.gammaSection K v) w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [coordinateOperators, classOperators, map_sub, map_smul]
    rw [← ResidueConnection.gammaSection_connection K h6, ih]

def coordinatePoleOperators : ℕ → (Fin 5 → ResidueConnection.Coeff K)
  | 0 => Pi.single 0 1
  | n + 1 => ResidueConnection.gammaNabla K (coordinatePoleOperators n) +
      (n + 1 : Coeff K) • coordinatePoleOperators n

theorem actual_coordinate_pole_transport (h6 : IsUnit (6 : K)) (n : ℕ) :
    ResidueConnection.gammaSection K (coordinatePoleOperators K n) =
      poleOperators K n := by
  induction n with
  | zero => exact ResidueConnection.gammaSection_single K 0
  | succ n ih =>
    simp only [coordinatePoleOperators, poleOperators, map_add, map_smul]
    rw [← ResidueConnection.gammaSection_connection K h6, ih]

/-- The explicit coordinate word is proved to represent the actual rational
class. Every term discarded by raising lies in the specified exact submodule. -/
theorem actual_word_coordinates (h6 : IsUnit (6 : K)) (n : ℕ) (w : List (Fin 6)) :
    ResidueConnection.gammaSection K
        (coordinateOperators K (coordinatePoleOperators K n) w) =
      scaledNumerator K (wordExponent w) (n + w.length)
        (by rw [wordExponent_sum]; omega) := by
  rw [actual_coordinate_operator_transport K h6, actual_coordinate_pole_transport K h6,
    ← word_numerator_from_first_pole]

theorem integral_actual_word_coordinates (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (n : ℕ) (w : List (Fin 6)) (v : Fin 5 → Coeff ℤ_[p]) :
    scaledNumerator ℤ_[p] (wordExponent w) (n + w.length)
        (by rw [wordExponent_sum]; omega) =
      ResidueConnection.gammaSection ℤ_[p] v ↔
        coordinateOperators ℤ_[p] (coordinatePoleOperators ℤ_[p] n) w = v := by
  rw [← actual_word_coordinates ℤ_[p] (Parameter.padic_six_unit p hp)]
  exact (ResidueConnection.integral_gammaSection_injective p).eq_iff

theorem actual_strict_numerator_coordinates (h6 : IsUnit (6 : K))
    (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ i, a i) ≤ n) :
    ResidueConnection.gammaSection K
        (coordinateOperators K (coordinatePoleOperators K (n - ∑ i, a i))
          (canonicalWord a)) =
      scaledNumerator K a n (by omega) := by
  have h := actual_word_coordinates K h6 (n - ∑ i, a i) (canonicalWord a)
  simpa only [canonicalWord_exponent, canonicalWord_length, Nat.sub_add_cancel ha] using h

def strictNumeratorCoordinates (h6 : IsUnit (6 : K)) (a : Fin 6 → ℕ) (n : ℕ) :
    Fin 5 → Coeff K :=
  (ActualConnection.boundaryScalar K h6) ^ (∑ i, a i) •
    coordinateOperators K (coordinatePoleOperators K (n - ∑ i, a i)) (canonicalWord a)

theorem actual_unscaled_strict_numerator_coordinates (h6 : IsUnit (6 : K))
    (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ i, a i) ≤ n) :
    ResidueConnection.gammaSection K (strictNumeratorCoordinates K h6 a n) =
      qNumerator K a n (by omega) := by
  rw [strictNumeratorCoordinates, map_smul,
    actual_strict_numerator_coordinates K h6 a n ha, scaledNumerator, smul_smul,
    ← mul_pow, mul_comm (ActualConnection.boundaryScalar K h6),
    ActualConnection.six_parameter_mul_boundaryScalar, one_pow, one_smul]

theorem integral_actual_strict_numerator_coordinates (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ i, a i) ≤ n)
    (v : Fin 5 → Coeff ℤ_[p]) :
    scaledNumerator ℤ_[p] a n (by omega) = ResidueConnection.gammaSection ℤ_[p] v ↔
      coordinateOperators ℤ_[p] (coordinatePoleOperators ℤ_[p] (n - ∑ i, a i))
          (canonicalWord a) = v := by
  rw [← actual_strict_numerator_coordinates ℤ_[p] (Parameter.padic_six_unit p hp) a n ha]
  exact (ResidueConnection.integral_gammaSection_injective p).eq_iff

theorem integral_actual_unscaled_strict_numerator_coordinates (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ i, a i) ≤ n)
    (v : Fin 5 → Coeff ℤ_[p]) :
    qNumerator ℤ_[p] a n (by omega) = ResidueConnection.gammaSection ℤ_[p] v ↔
      strictNumeratorCoordinates ℤ_[p] (Parameter.padic_six_unit p hp) a n = v := by
  rw [← actual_unscaled_strict_numerator_coordinates ℤ_[p]
    (Parameter.padic_six_unit p hp) a n ha]
  exact (ResidueConnection.integral_gammaSection_injective p).eq_iff

end WPReview.ResidueNumeratorOperators
