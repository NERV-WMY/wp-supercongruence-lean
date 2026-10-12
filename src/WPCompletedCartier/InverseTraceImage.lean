import WPCompletedCartier.InverseTraceAlgebra
import WPCompletedCartier.SeriesRegrouping

namespace WPCompletedCartier.InverseTraceImage

noncomputable section
open scoped BigOperators
open WPResidueQuotient.Adic
open WPCompletedCartier.InverseTraceAlgebra
open WPCompletedCartier.InverseTraceTail

variable (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)

theorem scalar_smul_divisible (n : ℕ) (z : ℤ_[p]) (x : Strict p hp7)
    (hz : z ∈ powerSubmodule (p : ℤ_[p]) n) :
    z • x ∈ powerSubmodule (p : ℤ_[p]) n :=
  map_powerSubmodule (p : ℤ_[p]) n
    ((LinearMap.id : ℤ_[p] →ₗ[ℤ_[p]] ℤ_[p]).smulRight x) hz

def rowTerm (r : Fin 5) (k l : ℕ) : Strict p hp7 :=
  normalizedCoefficient p hp7 r (k + l) k • selectedFactorial p hp7 r (k + l)

theorem rowTerm_eventual (r : Fin 5) (k : ℕ) :
    AdicSeries.EventuallyDivisible (p : ℤ_[p]) (rowTerm p hp7 r k) := by
  intro n
  refine ⟨6 * n + 1, ?_⟩
  intro l hl
  exact scalar_smul_divisible p hp7 n _ _
    (normalizedCoefficient_divisible p hp7 r (k + l) k n (by omega))

def rowSum (r : Fin 5) (k : ℕ) : StrictCompleted p hp7 :=
  AdicSeries.sum (p : ℤ_[p]) (rowTerm p hp7 r k) (rowTerm_eventual p hp7 r k)

theorem rowSum_converges (r : Fin 5) (k : ℕ) :
    Filter.Tendsto
      (fun L => ofModule (p : ℤ_[p])
        (∑ l ∈ Finset.range L, rowTerm p hp7 r k l))
      Filter.atTop (nhds (rowSum p hp7 r k)) :=
  AdicSeries.tendsto_partialSum _ _ _

def shiftedRow (r : Fin 5) (k j : ℕ) : Strict p hp7 :=
  SeriesRegrouping.shift k (rowTerm p hp7 r k) j

theorem shiftedRow_eq_coefficient (r : Fin 5) (k j : ℕ) :
    shiftedRow p hp7 r k j = shiftedCoefficient p hp7 r k j •
      selectedFactorial p hp7 r j := by
  unfold shiftedRow SeriesRegrouping.shift shiftedCoefficient
  split_ifs with hkj
  · unfold rowTerm
    rw [Nat.add_sub_of_le hkj]
  · simp only [zero_smul]

theorem shiftedRow_eventual (r : Fin 5) (k : ℕ) :
    AdicSeries.EventuallyDivisible (p : ℤ_[p]) (shiftedRow p hp7 r k) :=
  SeriesRegrouping.shift_eventual (p : ℤ_[p]) k (rowTerm p hp7 r k)
    (rowTerm_eventual p hp7 r k)

theorem shiftedRow_sum (r : Fin 5) (k : ℕ) :
    AdicSeries.sum (p : ℤ_[p]) (shiftedRow p hp7 r k)
      (shiftedRow_eventual p hp7 r k) = rowSum p hp7 r k :=
  SeriesRegrouping.sum_shift (p : ℤ_[p]) k (rowTerm p hp7 r k)
    (rowTerm_eventual p hp7 r k)

def totalTerm (r : Fin 5) (N j : ℕ) : Strict p hp7 :=
  finiteCoefficient p hp7 r N j • selectedFactorial p hp7 r j

theorem totalTerm_eventual (r : Fin 5) (N : ℕ) :
    AdicSeries.EventuallyDivisible (p : ℤ_[p]) (totalTerm p hp7 r N) := by
  intro n
  exact ⟨N + 6 * n + 1, fun j hj => scalar_smul_divisible p hp7 n _ _
    (finiteCoefficient_divisible p hp7 r N j n hj)⟩

def totalSum (r : Fin 5) (N : ℕ) : StrictCompleted p hp7 :=
  AdicSeries.sum (p : ℤ_[p]) (totalTerm p hp7 r N) (totalTerm_eventual p hp7 r N)

theorem totalSum_converges (r : Fin 5) (N : ℕ) :
    Filter.Tendsto
      (fun J => ofModule (p : ℤ_[p])
        (∑ j ∈ Finset.range J, totalTerm p hp7 r N j))
      Filter.atTop (nhds (totalSum p hp7 r N)) :=
  AdicSeries.tendsto_partialSum _ _ _

theorem totalTerm_eq_sum_shiftedRow (r : Fin 5) (N j : ℕ) :
    totalTerm p hp7 r N j = ∑ k ∈ Finset.range N, shiftedRow p hp7 r k j := by
  unfold totalTerm finiteCoefficient
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro k _hk
  exact (shiftedRow_eq_coefficient p hp7 r k j).symm

/-- The finite row sum is regrouped inside the actual strict completion. -/
theorem finite_rowSum_eq_totalSum (r : Fin 5) (N : ℕ) :
    (∑ k ∈ Finset.range N, rowSum p hp7 r k) = totalSum p hp7 r N := by
  calc
    _ = ∑ k ∈ Finset.range N,
        AdicSeries.sum (p : ℤ_[p]) (shiftedRow p hp7 r k)
          (shiftedRow_eventual p hp7 r k) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact (shiftedRow_sum p hp7 r k).symm
    _ = AdicSeries.sum (p : ℤ_[p])
        (fun j => ∑ k ∈ Finset.range N, shiftedRow p hp7 r k j)
        (SeriesRegrouping.finset_eventual (p : ℤ_[p]) (Finset.range N)
          (shiftedRow p hp7 r) (shiftedRow_eventual p hp7 r)) :=
      (SeriesRegrouping.sum_finset (p : ℤ_[p]) (Finset.range N)
        (shiftedRow p hp7 r) (shiftedRow_eventual p hp7 r)).symm
    _ = totalSum p hp7 r N := by
      change AdicSeries.sum (p : ℤ_[p])
        (fun j => ∑ k ∈ Finset.range N, shiftedRow p hp7 r k j) _ =
        AdicSeries.sum (p : ℤ_[p]) (totalTerm p hp7 r N) _
      congr 1
      funext j
      exact (totalTerm_eq_sum_shiftedRow p hp7 r N j).symm

def headTerm (r : Fin 5) : Strict p hp7 :=
  inverseFactorial p hp7 r • selectedFactorial p hp7 r 0

theorem totalTerm_zero_index (r : Fin 5) (N : ℕ) (hN : 1 ≤ N) :
    totalTerm p hp7 r N 0 = headTerm p hp7 r := by
  unfold totalTerm headTerm
  rw [finiteCoefficient_zero_index p hp7 r N hN]

theorem totalTerm_before (r : Fin 5) (N j : ℕ)
    (hN : 1 ≤ N) (hj : 1 ≤ j) (hjN : j < N) :
    totalTerm p hp7 r N j = 0 := by
  unfold totalTerm
  rw [finiteCoefficient_before p hp7 r N j hN hj hjN, zero_smul]

theorem totalTerm_tail (r : Fin 5) (N t : ℕ) (hN : 1 ≤ N) :
    totalTerm p hp7 r N (N + t) = InverseTraceTail.tailTerm p hp7 N hN r t := by
  unfold totalTerm InverseTraceTail.tailTerm
  rw [finiteCoefficient_tail p hp7 r N (N + t) hN (Nat.le_add_right _ _)]

theorem totalTerm_partialSum (r : Fin 5) (N : ℕ) (hN : 1 ≤ N) :
    AdicSeries.partialSum (totalTerm p hp7 r N) N = headTerm p hp7 r := by
  classical
  unfold AdicSeries.partialSum
  calc
    _ = totalTerm p hp7 r N 0 := by
      apply Finset.sum_eq_single 0
      · intro j hj hj0
        exact totalTerm_before p hp7 r N j hN (by omega) (Finset.mem_range.mp hj)
      · intro h
        exact False.elim (h (Finset.mem_range.mpr (by omega)))
    _ = _ := totalTerm_zero_index p hp7 r N hN

theorem totalSum_eq_head_add_tail (r : Fin 5) (N : ℕ) (hN : 1 ≤ N) :
    totalSum p hp7 r N = ofModule (p : ℤ_[p]) (headTerm p hp7 r) +
      InverseTraceTail.tail p hp7 N hN r := by
  have hs := AdicSeries.sum_eq_partialSum_add_tail (p : ℤ_[p])
    (totalTerm p hp7 r N) (totalTerm_eventual p hp7 r N) N
  change totalSum p hp7 r N = _ at hs
  rw [hs, totalTerm_partialSum p hp7 r N hN]
  congr 1
  change AdicSeries.sum (p : ℤ_[p]) (fun t => totalTerm p hp7 r N (N + t)) _ =
    AdicSeries.sum (p : ℤ_[p]) (InverseTraceTail.tailTerm p hp7 N hN r) _
  congr 1
  funext t
  exact totalTerm_tail p hp7 r N t hN

theorem finite_rowSum_eq_head_add_tail (r : Fin 5) (N : ℕ) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.range N, rowSum p hp7 r k) =
      ofModule (p : ℤ_[p]) (headTerm p hp7 r) + InverseTraceTail.tail p hp7 N hN r := by
  rw [finite_rowSum_eq_totalSum, totalSum_eq_head_add_tail p hp7 r N hN]

theorem totalSum_tendsto_head (r : Fin 5) :
    Filter.Tendsto (fun N => totalSum p hp7 r (N + 1)) Filter.atTop
      (nhds (ofModule (p : ℤ_[p]) (headTerm p hp7 r))) := by
  have he (N : ℕ) : totalSum p hp7 r (N + 1) =
      ofModule (p : ℤ_[p]) (headTerm p hp7 r) +
        InverseTraceTail.tail p hp7 (N + 1) (by omega) r :=
    totalSum_eq_head_add_tail p hp7 r (N + 1) (by omega)
  simp_rw [he]
  simpa only [add_zero] using
    (tendsto_const_nhds.add (InverseTraceTail.tail_tendsto_zero p hp7 r))

theorem finite_rowSum_tendsto_head (r : Fin 5) :
    Filter.Tendsto (fun N => ∑ k ∈ Finset.range (N + 1), rowSum p hp7 r k)
      Filter.atTop (nhds (ofModule (p : ℤ_[p]) (headTerm p hp7 r))) := by
  simp_rw [finite_rowSum_eq_totalSum]
  exact totalSum_tendsto_head p hp7 r

end

end WPCompletedCartier.InverseTraceImage
