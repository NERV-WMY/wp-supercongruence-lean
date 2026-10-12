import WPCompletedCartier.NumericalTerms
import WPCompletedCartier.AdicSeries
import WPCartierFinite.KernelTail

namespace WPCompletedCartier.InverseTraceTail

noncomputable section
open scoped BigOperators
open WPResidueQuotient WPResidueQuotient.Adic
open WPCompletedCartier.NumericalTerms

variable (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)

abbrev Strict := FInterior (Parameter.integralTenth p hp7)
abbrev StrictCompleted := Completion (p : ℤ_[p]) (Strict p hp7)

theorem selected_power_supported (j : ℕ) :
    kappa p (Fact.out : p.Prime).pos (G p hp7 ^ j) ∈
      numeratorFiltration ℤ_[p] j := by
  apply kappa_supported
  simpa only [Nat.mul_comm] using numeratorFiltration_pow p (G_supported p hp7) j

def selectedFactorial (r : Fin 5) (j : ℕ) : Strict p hp7 :=
  ⟨factorialNumeratorMap (Parameter.integralTenth p hp7) (r.val + j)
    (kappa p (Fact.out : p.Prime).pos (G p hp7 ^ j)),
    factorialNumeratorMap_mem_interior _ _
      (numeratorFiltration_mono (Nat.le_add_left j r.val)
        (selected_power_supported p hp7 j))⟩

include hp7 in
theorem tailScalar_nonnegative (N : ℕ) (hN : 1 ≤ N) (r : Fin 5)
    (j : ℕ) (hNj : N ≤ j) :
    0 ≤ padicValRat p (WPCartierFinite.inverseTraceTailScalar p (r.val + 1) N j) := by
  have h := WPCartierFinite.inverse_trace_tail_uniform_bound p (r.val + 1) N j
    Fact.out hp7 (by omega) (by omega) hN hNj
  have hj : (1 : ℚ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
  have he : (0 : ℚ) ≤
      (padicValRat p (WPCartierFinite.inverseTraceTailScalar p (r.val + 1) N j) : ℚ) := by
    linarith
  exact_mod_cast he

def tailScalar (N : ℕ) (hN : 1 ≤ N) (r : Fin 5) (j : ℕ) (hNj : N ≤ j) : ℤ_[p] :=
  integralRat p (WPCartierFinite.inverseTraceTailScalar p (r.val + 1) N j)
    (tailScalar_nonnegative p hp7 N hN r j hNj)

theorem tailScalar_divisible (N : ℕ) (hN : 1 ≤ N) (r : Fin 5)
    (j : ℕ) (hNj : N ≤ j) (n : ℕ) (hj : 6 * n + 1 ≤ j) :
    tailScalar p hp7 N hN r j hNj ∈ powerSubmodule (p : ℤ_[p]) n := by
  apply integralRat_divisible
  have h := WPCartierFinite.inverse_trace_tail_uniform_bound p (r.val + 1) N j
    Fact.out hp7 (by omega) (by omega) hN hNj
  have hjQ : (6 * n + 1 : ℚ) ≤ j := by exact_mod_cast hj
  have he : (n : ℚ) ≤
      (padicValRat p (WPCartierFinite.inverseTraceTailScalar p (r.val + 1) N j) : ℚ) := by
    nlinarith
  exact_mod_cast he

def tailTerm (N : ℕ) (hN : 1 ≤ N) (r : Fin 5) (t : ℕ) : Strict p hp7 :=
  tailScalar p hp7 N hN r (N + t) (Nat.le_add_right _ _) •
    selectedFactorial p hp7 r (N + t)

theorem tailTerm_divisible (N : ℕ) (hN : 1 ≤ N) (r : Fin 5) (t n : ℕ)
    (hj : 6 * n + 1 ≤ N + t) :
    tailTerm p hp7 N hN r t ∈ powerSubmodule (p : ℤ_[p]) n := by
  obtain ⟨z, hz⟩ := (mem_powerSubmodule _ _ _).mp
    (tailScalar_divisible p hp7 N hN r (N + t) (Nat.le_add_right _ _) n hj)
  refine ⟨z • selectedFactorial p hp7 r (N + t), ?_⟩
  change (p : ℤ_[p]) ^ n • (z • selectedFactorial p hp7 r (N + t)) = _
  rw [← mul_smul]
  change ((p : ℤ_[p]) ^ n • z) • selectedFactorial p hp7 r (N + t) = _
  rw [hz]
  rfl

theorem tailTerm_eventual (N : ℕ) (hN : 1 ≤ N) (r : Fin 5) :
    AdicSeries.EventuallyDivisible (p : ℤ_[p]) (tailTerm p hp7 N hN r) := by
  intro n
  exact ⟨6 * n + 1, fun t ht => tailTerm_divisible p hp7 N hN r t n (by omega)⟩

def tail (N : ℕ) (hN : 1 ≤ N) (r : Fin 5) : StrictCompleted p hp7 :=
  AdicSeries.sum (p : ℤ_[p]) (tailTerm p hp7 N hN r)
    (tailTerm_eventual p hp7 N hN r)

theorem tail_converges (N : ℕ) (hN : 1 ≤ N) (r : Fin 5) :
    Filter.Tendsto
      (fun K => ofModule (p : ℤ_[p])
        (∑ t ∈ Finset.range K, tailTerm p hp7 N hN r t))
      Filter.atTop (nhds (tail p hp7 N hN r)) :=
  AdicSeries.tendsto_partialSum _ _ _

theorem tail_divisible (N : ℕ) (hN : 1 ≤ N) (r : Fin 5) (n : ℕ)
    (hcut : 6 * n + 1 ≤ N) :
    tail p hp7 N hN r ∈ powerSubmodule (M := StrictCompleted p hp7) (p : ℤ_[p]) n := by
  apply AdicSeries.sum_mem_powerSubmodule (p : ℤ_[p])
    (AdicSeries.actualInterior_smul_injective (Parameter.integralTenth p hp7)
      (p : ℤ_[p]) (by exact_mod_cast (Fact.out : p.Prime).ne_zero))
  intro t
  exact tailTerm_divisible p hp7 N hN r t n (by omega)

theorem tail_tendsto_zero (r : Fin 5) :
    Filter.Tendsto (fun N => tail p hp7 (N + 1) (by omega) r)
      Filter.atTop (nhds (0 : StrictCompleted p hp7)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro n
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.Ici_mem_atTop (6 * n)] with N hN
  change 6 * n ≤ N at hN
  obtain ⟨x, hx⟩ := tail_divisible p hp7 (N + 1) (by omega) r n (by omega)
  change (p : ℤ_[p]) ^ n • x = tail p hp7 (N + 1) (by omega) r at hx
  rw [← hx]
  exact (AdicSeries.power_smul_level_zero (p : ℤ_[p]) n (x.val n)).symm

end

end WPCompletedCartier.InverseTraceTail
