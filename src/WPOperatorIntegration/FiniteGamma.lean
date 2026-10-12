import WPOperatorIntegration.Normalization
import WPResidueFrobenius.Interior
import WPCompletedCartier.InteriorConstruction

noncomputable section

namespace WPOperatorIntegration

open scoped BigOperators Topology
open Filter WPResidueQuotient WPResidueQuotient.ActualCompletion

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)

theorem actual_numerator_inclusion (j : Fin 5) (k : ℕ) :
    WPResidueFrobenius.rawIntegralGenerator p hp (j.val + 1) k (by omega)
      (WPResidueFrobenius.gammaNumerator p)
      (WPResidueFrobenius.gammaNumerator_supported p (j.val + 1)) =
    actualInteriorInclusion (Parameter.integralTenth p hp)
      (WPCompletedCartier.InteriorConstruction.numeratorToInterior p hp
        (WPCompletedCartier.InverseTraceConstruction.inputIndex p j k)
        (WPCompletedCartier.InverseTraceConstruction.inputNumerator p hp j k)) := by
  apply Subtype.ext
  have hindex : j.val + 1 + k = j.val + k + 1 := by omega
  change factorialNumeratorMap (Parameter.integralTenth p hp)
      (p * (j.val + 1 + k) - 1)
      (WPResidueFrobenius.pullbackNumerator p hp
        (WPResidueFrobenius.gammaNumerator p) k) =
    factorialNumeratorMap (Parameter.integralTenth p hp)
      (WPCompletedCartier.InverseTraceConstruction.inputIndex p j k)
      ((WPCompletedCartier.InverseTraceConstruction.inputNumerator p hp j k).val)
  simp only [WPResidueFrobenius.pullbackNumerator, WPResidueFrobenius.gammaNumerator,
    map_one, one_mul, actual_G_eq,
    WPCompletedCartier.InverseTraceConstruction.inputIndex,
    WPCompletedCartier.InverseTraceConstruction.inputHeight,
    WPCompletedCartier.InverseTraceConstruction.inputNumerator, hindex]

def finiteGammaColumn (N : ℕ) (j : Fin 5) : Fin 5 → ℚ_[p] :=
  fun i => ∑ k ∈ Finset.range N, ActualSpecialization.tenthClosedCoordinates ℚ_[p]
    (WPResidueFrobenius.rawPullbackTerm p hp (j.val + 1) k (by omega)
      (WPResidueFrobenius.gammaNumerator p)
      (WPResidueFrobenius.gammaNumerator_supported p (j.val + 1))) (Fin.castAdd 6 i)


variable (hp7 : p ≠ 7) (hp19 : p ≠ 19)

theorem finiteGammaColumn_tendsto (j : Fin 5) :
    Tendsto (fun N => finiteGammaColumn p hp N j) atTop
      (nhds (fun i =>
        (WPResidueFrobenius.gammaRawInteriorMatrix p hp hp7 hp19 i j : ℚ_[p]))) := by
  have hs := (WPResidueFrobenius.rawPullbackCoordinates_hasSum p hp hp7 hp19
    (j.val + 1) (by omega) (WPResidueFrobenius.gammaNumerator p)
    (WPResidueFrobenius.gammaNumerator_supported p (j.val + 1))).tendsto_sum_nat
  have hc : Continuous (fun v : Fin 11 → ℚ_[p] => fun i : Fin 5 => v (Fin.castAdd 6 i)) :=
    continuous_pi (fun i => continuous_apply (Fin.castAdd 6 i))
  apply (hc.tendsto _ |>.comp hs).congr'
  filter_upwards [] with N
  ext i
  simp only [Function.comp_def, finiteGammaColumn, Finset.sum_apply]


end WPOperatorIntegration
