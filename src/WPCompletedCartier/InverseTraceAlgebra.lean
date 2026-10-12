import WPCompletedCartier.InverseTraceTail
import WPCompletedCartier.ScalarBridge

namespace WPCompletedCartier.InverseTraceAlgebra

noncomputable section
open scoped BigOperators
open WPResidueQuotient.Adic
open WPCompletedCartier.NumericalTerms

variable (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)

/-- Only the five low factorials are inverted, using their proved units. -/
def inverseFactorial (r : Fin 5) : ℤ_[p] :=
  ↑(ScalarBridge.lowPole_factorial_isUnit p hp7 r).unit⁻¹

theorem inverseFactorial_mul (r : Fin 5) :
    inverseFactorial p hp7 r * (r.val.factorial : ℤ_[p]) = 1 := by
  let hu := ScalarBridge.lowPole_factorial_isUnit p hp7 r
  change ↑hu.unit⁻¹ * (r.val.factorial : ℤ_[p]) = 1
  calc
    _ = ↑hu.unit⁻¹ * (hu.unit : ℤ_[p]) :=
      congrArg (fun z : ℤ_[p] => ↑hu.unit⁻¹ * z) hu.unit_spec.symm
    _ = 1 := Units.inv_mul _

@[simp] theorem inverseFactorial_coe (r : Fin 5) :
    (inverseFactorial p hp7 r : ℚ_[p]) = 1 / (r.val.factorial : ℚ_[p]) := by
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero r.val)).mpr
  have h := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) (inverseFactorial_mul p hp7 r)
  simpa only [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_one] using h

@[simp] theorem factorialTail_zero : factorialTail p hp7 0 = 1 := by
  apply Subtype.ext
  simp only [factorialTail_coe, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    PadicInt.coe_one]

def normalizedCoefficient (r : Fin 5) (j k : ℕ) : ℤ_[p] :=
  (-1 : ℤ_[p]) ^ k * factorialTail p hp7 k * factorialTail p hp7 (j - k) *
    inverseFactorial p hp7 r

def shiftedCoefficient (r : Fin 5) (k j : ℕ) : ℤ_[p] :=
  if k ≤ j then normalizedCoefficient p hp7 r j k else 0

def finiteCoefficient (r : Fin 5) (N j : ℕ) : ℤ_[p] :=
  ∑ k ∈ Finset.range N, shiftedCoefficient p hp7 r k j

def normalizedRational (p r j k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k * WPCartierFinite.factorialTailScalar p k *
    WPCartierFinite.factorialTailScalar p (j - k) / (r.factorial : ℚ)

def finiteRational (p r N j : ℕ) : ℚ :=
  ∑ k ∈ Finset.range N, if k ≤ j then normalizedRational p r j k else 0

@[simp] theorem normalizedCoefficient_coe (r : Fin 5) (j k : ℕ) :
    (normalizedCoefficient p hp7 r j k : ℚ_[p]) =
      (normalizedRational p r.val j k : ℚ_[p]) := by
  simp only [normalizedCoefficient, PadicInt.coe_mul, PadicInt.coe_pow,
    PadicInt.coe_neg, PadicInt.coe_one, factorialTail_coe, inverseFactorial_coe,
    normalizedRational, WPCartierFinite.factorialTailScalar,
    Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
    Rat.cast_natCast]
  ring

@[simp] theorem finiteCoefficient_coe (r : Fin 5) (N j : ℕ) :
    (finiteCoefficient p hp7 r N j : ℚ_[p]) = (finiteRational p r.val N j : ℚ_[p]) := by
  simp only [finiteCoefficient, shiftedCoefficient, PadicInt.coe_sum, finiteRational,
    Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hkj : k ≤ j
  · simpa only [if_pos hkj] using normalizedCoefficient_coe p hp7 r j k
  · simp only [if_neg hkj, PadicInt.coe_zero, Rat.cast_zero]

omit [Fact p.Prime] in
theorem factorial_product_choose (j k : ℕ) (hkj : k ≤ j) :
    WPCartierFinite.factorialTailScalar p k *
      WPCartierFinite.factorialTailScalar p (j - k) =
      WPCartierFinite.factorialTailScalar p j * (j.choose k : ℚ) := by
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hsub : ((j - k).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (j - k)
  have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hchoose : (j.choose k : ℚ) * (k.factorial : ℚ) *
      ((j - k).factorial : ℚ) = (j.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkj
  unfold WPCartierFinite.factorialTailScalar
  rw [div_mul_div_comm, ← pow_add, Nat.add_sub_of_le hkj]
  field_simp [hk, hsub, hj]
  rw [← hchoose]
  ring

omit [Fact p.Prime] in
theorem normalizedRational_eq_kernel (r j k : ℕ) (hkj : k ≤ j) :
    normalizedRational p r j k =
      (p : ℚ) ^ j * WPCartierFinite.traceKernelCoefficient (r + 1) j k /
        ((r + j).factorial : ℚ) := by
  have hprod : ((r + k).choose k : ℚ) * ((r + j).choose (j - k) : ℚ) =
      ((r + j).choose j : ℚ) * (j.choose k : ℚ) := by
    have h := WPCartierFinite.binomial_product (r + 1) j k (by omega) hkj
    have hj' : r + 1 + j - 1 = r + j := by omega
    have hk' : r + 1 + k - 1 = r + k := by omega
    rw [hj', hk'] at h
    exact_mod_cast h
  have htrace : WPCartierFinite.traceKernelCoefficient (r + 1) j k =
      (-1 : ℚ) ^ k * ((r + j).choose j : ℚ) * (j.choose k : ℚ) := by
    unfold WPCartierFinite.traceKernelCoefficient
    have hj' : r + 1 + j - 1 = r + j := by omega
    have hk' : r + 1 + k - 1 = r + k := by omega
    rw [hj', hk']
    calc
      _ = (-1 : ℚ) ^ k * (((r + k).choose k : ℚ) *
          ((r + j).choose (j - k) : ℚ)) := by ring
      _ = _ := by rw [hprod]; ring
  have hchoose : ((r + j).choose j : ℚ) * (j.factorial : ℚ) *
      (r.factorial : ℚ) = ((r + j).factorial : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left j r)
    simpa only [Nat.add_sub_cancel] using (show
      ((r + j).choose j : ℚ) * (j.factorial : ℚ) *
        ((r + j - j).factorial : ℚ) = ((r + j).factorial : ℚ) from by exact_mod_cast h)
  unfold normalizedRational
  rw [mul_assoc ((-1 : ℚ) ^ k), factorial_product_choose p j k hkj, htrace]
  unfold WPCartierFinite.factorialTailScalar
  have hf : ((r + j).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (r + j)
  have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hr : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  field_simp [hf, hj, hr]
  rw [← hchoose]
  ring

omit [Fact p.Prime] in
theorem finiteRational_eq_kernel (r N j : ℕ) (hN : 1 ≤ N) :
    finiteRational p r N j =
      (p : ℚ) ^ j / ((r + j).factorial : ℚ) *
        (((r + j).choose j : ℚ) * WPCartierFinite.alternatingKernel N j) := by
  unfold finiteRational
  calc
    _ = ∑ k ∈ Finset.range N, ((p : ℚ) ^ j / ((r + j).factorial : ℚ)) *
        (if k ≤ j then WPCartierFinite.traceKernelCoefficient (r + 1) j k else 0) := by
      apply Finset.sum_congr rfl
      intro k _hk
      split_ifs with hkj
      · rw [normalizedRational_eq_kernel p r j k hkj]
        ring
      · simp only [mul_zero]
    _ = _ := by
      rw [← Finset.mul_sum,
        WPCartierFinite.finite_kernel_coefficient_sum (r + 1) N j (by omega) hN]
      have hj' : r + 1 + j - 1 = r + j := by omega
      rw [hj']

omit [Fact p.Prime] in
theorem finiteRational_zero_index (r N : ℕ) (hN : 1 ≤ N) :
    finiteRational p r N 0 = 1 / (r.factorial : ℚ) := by
  rw [finiteRational_eq_kernel p r N 0 hN,
    WPCartierFinite.alternating_kernel_zero_index]
  simp

omit [Fact p.Prime] in
theorem finiteRational_before (r N j : ℕ) (hN : 1 ≤ N) (hj : 1 ≤ j) (hjN : j < N) :
    finiteRational p r N j = 0 := by
  rw [finiteRational_eq_kernel p r N j hN,
    WPCartierFinite.alternating_kernel_before N j hj hjN]
  simp

omit [Fact p.Prime] in
theorem finiteRational_tail (r N j : ℕ) (hN : 1 ≤ N) (hNj : N ≤ j) :
    finiteRational p r N j = WPCartierFinite.inverseTraceTailScalar p (r + 1) N j := by
  rw [finiteRational_eq_kernel p r N j hN,
    WPCartierFinite.alternating_kernel_tail N j hN hNj]
  unfold WPCartierFinite.inverseTraceTailScalar
  have hj' : r + 1 + j - 1 = r + j := by omega
  rw [hj']
  ring

theorem finiteCoefficient_zero_index (r : Fin 5) (N : ℕ) (hN : 1 ≤ N) :
    finiteCoefficient p hp7 r N 0 = inverseFactorial p hp7 r := by
  apply Subtype.ext
  rw [finiteCoefficient_coe, finiteRational_zero_index p r.val N hN, inverseFactorial_coe]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]

theorem finiteCoefficient_before (r : Fin 5) (N j : ℕ)
    (hN : 1 ≤ N) (hj : 1 ≤ j) (hjN : j < N) :
    finiteCoefficient p hp7 r N j = 0 := by
  apply Subtype.ext
  rw [finiteCoefficient_coe, finiteRational_before p r.val N j hN hj hjN]
  rfl

theorem finiteCoefficient_tail (r : Fin 5) (N j : ℕ)
    (hN : 1 ≤ N) (hNj : N ≤ j) :
    finiteCoefficient p hp7 r N j = InverseTraceTail.tailScalar p hp7 N hN r j hNj := by
  apply Subtype.ext
  rw [finiteCoefficient_coe, finiteRational_tail p r.val N j hN hNj]
  rfl

theorem finiteCoefficient_cases (r : Fin 5) (N j : ℕ) (hN : 1 ≤ N) :
    finiteCoefficient p hp7 r N j =
      if j = 0 then inverseFactorial p hp7 r else
        if hjN : j < N then 0 else
          InverseTraceTail.tailScalar p hp7 N hN r j (Nat.le_of_not_gt hjN) := by
  split_ifs with hj hjN
  · subst j
    exact finiteCoefficient_zero_index p hp7 r N hN
  · exact finiteCoefficient_before p hp7 r N j hN (by omega) hjN
  · exact finiteCoefficient_tail p hp7 r N j hN (by omega)

@[simp] theorem shiftedCoefficient_eq_zero (r : Fin 5) (k j : ℕ) (hjk : j < k) :
    shiftedCoefficient p hp7 r k j = 0 :=
  if_neg (by omega)

@[simp] theorem finiteCoefficient_empty (r : Fin 5) (j : ℕ) :
    finiteCoefficient p hp7 r 0 j = 0 := by
  simp [finiteCoefficient]

theorem finiteCoefficient_one (r : Fin 5) (j : ℕ) :
    finiteCoefficient p hp7 r 1 j = factorialTail p hp7 j * inverseFactorial p hp7 r := by
  simp [finiteCoefficient, shiftedCoefficient, normalizedCoefficient]

theorem normalizedCoefficient_divisible (r : Fin 5) (j k n : ℕ)
    (hcut : 6 * n + 1 ≤ j - k) :
    normalizedCoefficient p hp7 r j k ∈ powerSubmodule (p : ℤ_[p]) n := by
  have h := (powerSubmodule (p : ℤ_[p]) n).smul_mem
    ((-1 : ℤ_[p]) ^ k * factorialTail p hp7 k * inverseFactorial p hp7 r)
    (factorialTail_eventual p hp7 n (j - k) hcut)
  convert h using 1
  change normalizedCoefficient p hp7 r j k =
    ((-1 : ℤ_[p]) ^ k * factorialTail p hp7 k * inverseFactorial p hp7 r) *
      factorialTail p hp7 (j - k)
  unfold normalizedCoefficient
  ring

theorem shiftedCoefficient_divisible (r : Fin 5) (k j n : ℕ)
    (hcut : k + (6 * n + 1) ≤ j) :
    shiftedCoefficient p hp7 r k j ∈ powerSubmodule (p : ℤ_[p]) n := by
  rw [shiftedCoefficient, if_pos (by omega)]
  exact normalizedCoefficient_divisible p hp7 r j k n (by omega)

theorem shiftedCoefficient_eventual (r : Fin 5) (k : ℕ) :
    AdicSeries.EventuallyDivisible (p : ℤ_[p]) (shiftedCoefficient p hp7 r k) := by
  intro n
  exact ⟨k + (6 * n + 1), fun j hj => shiftedCoefficient_divisible p hp7 r k j n hj⟩

/-- The cutoff is uniform in the finite index k and all five low poles. -/
theorem finiteCoefficient_divisible (r : Fin 5) (N j n : ℕ)
    (hcut : N + 6 * n + 1 ≤ j) :
    finiteCoefficient p hp7 r N j ∈ powerSubmodule (p : ℤ_[p]) n := by
  unfold finiteCoefficient
  apply (powerSubmodule (p : ℤ_[p]) n).sum_mem
  intro k hk
  apply shiftedCoefficient_divisible p hp7 r k j n
  have hkN := Finset.mem_range.mp hk
  omega

theorem finiteCoefficient_eventual (r : Fin 5) (N : ℕ) :
    AdicSeries.EventuallyDivisible (p : ℤ_[p]) (finiteCoefficient p hp7 r N) := by
  intro n
  exact ⟨N + 6 * n + 1, fun j hj => finiteCoefficient_divisible p hp7 r N j n hj⟩

theorem normalizedCoefficient_shift_eventual (r : Fin 5) (k : ℕ) :
    AdicSeries.EventuallyDivisible (p : ℤ_[p])
      (fun t => normalizedCoefficient p hp7 r (k + t) k) := by
  intro n
  refine ⟨6 * n + 1, ?_⟩
  intro t ht
  exact normalizedCoefficient_divisible p hp7 r (k + t) k n (by omega)

end

end WPCompletedCartier.InverseTraceAlgebra
