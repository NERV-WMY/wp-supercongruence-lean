import WPFieldAssembly.ActualBpairLowHConicPrimitive
import WPFieldAssembly.ActualBpairLowHQuadratic

open scoped Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1200000

private theorem lowH_D_parameter : D (T 1 : K[T;T⁻¹]) = 1 := by
  simpa only [map_one, one_mul, Int.cast_one, Int.reduceSub, T_zero, mul_one] using
    D_monomial (1 : K) 1

private theorem lowH_D_inverse_parameter : D (T (-1) : K[T;T⁻¹]) = -T (-2) := by
  simpa only [map_one, one_mul, Int.cast_neg, Int.cast_one, Int.reduceSub,
    map_neg, neg_mul, map_one, one_mul] using D_monomial (1 : K) (-1)

theorem lowHConicW_derivative : D (lowHConicW : K[T;T⁻¹]) =
    C (1 / 2 : K) * (1 + T (-2)) := by
  rw [lowHConicW, D_C_mul, map_sub, lowH_D_parameter, lowH_D_inverse_parameter, sub_neg_eq_add]

theorem lowHConicT_derivative (η : K) : D (lowHConicT η) =
    C (η / 2) * (1 - T (-2)) := by
  rw [lowHConicT, D_C_mul, map_add, lowH_D_parameter, lowH_D_inverse_parameter]
  ring

/-- Both actual conic points over x=0 are retained, with their separate t signs. -/
theorem lowHConic_two_points (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (η : K) :
    LaurentPolynomial.eval₂ (RingHom.id K) (1 : Kˣ) lowHConicW = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id K) (-1 : Kˣ) lowHConicW = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id K) (1 : Kˣ) (lowHConicT η) = η ∧
      LaurentPolynomial.eval₂ (RingHom.id K) (-1 : Kˣ) (lowHConicT η) = -η := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals simp [lowHConicW, lowHConicT]
  all_goals field_simp [h2]
  all_goals ring

/-- w is a genuine local parameter at each point: its derivative is one on both branches. -/
theorem lowHConicW_two_jacobians (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id K) (1 : Kˣ) (D (lowHConicW : K[T;T⁻¹])) = 1 ∧
      LaurentPolynomial.eval₂ (RingHom.id K) (-1 : Kˣ) (D (lowHConicW : K[T;T⁻¹])) = 1 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  constructor
  all_goals simp [lowHConicW_derivative]
  all_goals field_simp [h2]
  all_goals ring

theorem lowHConicT_two_jacobians (η : K) :
    LaurentPolynomial.eval₂ (RingHom.id K) (1 : Kˣ) (D (lowHConicT η)) = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id K) (-1 : Kˣ) (D (lowHConicT η)) = 0 := by
  simp [lowHConicT_derivative]

/-- The original x=w^2 map has quadratic leading coefficient one at both conic points. -/
theorem lowHConic_x_two_jets (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (η : K) :
    (∀ ε : Kˣ, ε = 1 ∨ ε = -1 →
      LaurentPolynomial.eval₂ (RingHom.id K) ε (lowHConicW ^ 2) = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id K) ε (D (lowHConicW ^ 2)) = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id K) ε (D (D (lowHConicW ^ 2))) = 2) := by
  have hw := lowHConic_two_points p hp η
  have hdw := lowHConicW_two_jacobians (K := K) p hp
  intro ε hε
  have hW : LaurentPolynomial.eval₂ (RingHom.id K) ε (lowHConicW : K[T;T⁻¹]) = 0 := by
    rcases hε with rfl | rfl
    · exact hw.1
    · exact hw.2.1
  have hDW : LaurentPolynomial.eval₂ (RingHom.id K) ε (D (lowHConicW : K[T;T⁻¹])) = 1 := by
    rcases hε with rfl | rfl
    · exact hdw.1
    · exact hdw.2
  simp only [pow_two, D_mul, map_add, map_mul, hW, hDW, zero_mul, mul_zero,
    zero_add, add_zero, mul_one]
  norm_num

end WPFieldAssembly.ActualBpairContraction
