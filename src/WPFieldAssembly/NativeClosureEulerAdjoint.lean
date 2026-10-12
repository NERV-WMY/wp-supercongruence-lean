import WPFieldAssembly.ActualEtaTransport
import WPFieldAssembly.ActualSimplePoleResidue

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPFieldAssembly.ActualSimplePoleResidue WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

/-- The actual Euler source moves the full f carrier to its adjoint under the original residue. -/
theorem actual_f_green_adjoint (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (V : K[T;T⁻¹]) :
    originPole ((ActualThreePhase.fK (K := K) p hp).toLaurent * V * (33 - 12 * T 1)) =
      originPole (V * (33 - 12 * T 1)) -
        ((ActualGreenResidue.HpullK (K := K) p).toLaurent * D V).coeff (-1) := by
  have hE := (ActualGreenResidue.actual_two_Euler_sources (K := K) p hp).1
  have he : (ActualThreePhase.fK (K := K) p hp).toLaurent * V * (33 - 12 * T 1) =
      V * (33 - 12 * T 1) + (WPFiniteZSource.Abar : K[X]).toLaurent *
        (V * D (ActualGreenResidue.HpullK (K := K) p).toLaurent) := by
    linear_combination -V * hE
  have hz : (D (V * (ActualGreenResidue.HpullK (K := K) p).toLaurent)).coeff (-1) = 0 := by
    rw [D_coeff]
    norm_num
  rw [D_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hz
  have hi : (V * D (ActualGreenResidue.HpullK (K := K) p).toLaurent).coeff (-1) =
      -((ActualGreenResidue.HpullK (K := K) p).toLaurent * D V).coeff (-1) := by
    have hc : D V * (ActualGreenResidue.HpullK (K := K) p).toLaurent =
        (ActualGreenResidue.HpullK (K := K) p).toLaurent * D V := by ring
    rw [hc] at hz
    linear_combination hz
  rw [he, originPole_add, originPole_cleared p hp, hi]
  ring

/-- The same exact adjoint is a single marked origin source, without a free Euler value. -/
theorem actual_f_green_marked_adjoint (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (V : K[T;T⁻¹]) :
    originPole ((ActualThreePhase.fK (K := K) p hp).toLaurent * V * (33 - 12 * T 1)) =
      originPole (V * (33 - 12 * T 1) - (WPFiniteZSource.Abar : K[X]).toLaurent *
        ((ActualGreenResidue.HpullK (K := K) p).toLaurent * D V)) := by
  rw [actual_f_green_adjoint p hp V, originPole_sub, originPole_cleared p hp]

end WPFieldAssembly.ActualBpairContraction
