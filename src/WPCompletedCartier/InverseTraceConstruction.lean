import WPCompletedCartier.RationalizedCartier
import WPCompletedCartier.InverseTraceImage

namespace WPCompletedCartier.InverseTraceConstruction

noncomputable section
open scoped BigOperators
open WPResidueQuotient WPResidueQuotient.Adic
open WPCompletedCartier.NumericalTerms

def inputHeight (r : Fin 5) (k : ℕ) : ℕ := r.val + k + 1
def inputIndex (p : ℕ) (r : Fin 5) (k : ℕ) : ℕ := p * inputHeight r k - 1

variable (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)

local notation "u" => Parameter.integralTenth p hp7
local notation "L" => RationalizedCartier.Coeff p

theorem inputPole (r : Fin 5) (k : ℕ) : inputIndex p r k + 1 = p * inputHeight r k := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  unfold inputIndex inputHeight
  exact Nat.sub_add_cancel (by nlinarith)

def inputNumerator (r : Fin 5) (k : ℕ) : numeratorFiltration ℤ_[p] (inputIndex p r k) :=
  ⟨G p hp7 ^ k, by
    apply numeratorFiltration_mono _ (numeratorFiltration_pow p (G_supported p hp7) k)
    unfold inputIndex inputHeight
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_add]
    rw [Nat.mul_comm k p]
    have hp : 0 < p := (Fact.out : p.Prime).pos
    omega⟩

def inputCoefficient (r : Fin 5) (k : ℕ) : ℤ_[p] :=
  (-1 : ℤ_[p]) ^ k * ((r.val + k).choose k : ℤ_[p]) * (p : ℤ_[p]) ^ k

/-- This is the finite raw sum with actual poles p(r+k), in the localization
of the actual strict completed factorial module. -/
def finitePullback (N : ℕ) (r : Fin 5) : RationalizedCartier.Rationalized p hp7 :=
  ∑ k ∈ Finset.range N, algebraMap ℤ_[p] L (inputCoefficient p r k) •
    RationalizedCartier.rawPole p hp7 (inputIndex p r k) (inputNumerator p hp7 r k)

@[simp] theorem finitePullback_zero (r : Fin 5) : finitePullback p hp7 0 r = 0 := by
  simp only [finitePullback, Finset.range_zero, Finset.sum_empty]

def rowWeight (r : Fin 5) (k : ℕ) : ℤ_[p] :=
  (-1 : ℤ_[p]) ^ k * factorialTail p hp7 k *
    InverseTraceAlgebra.inverseFactorial p hp7 r

theorem factorialTail_mul (k : ℕ) :
    factorialTail p hp7 k * (k.factorial : ℤ_[p]) = (p : ℤ_[p]) ^ k := by
  apply Subtype.ext
  simp only [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_pow, factorialTail_coe]
  exact div_mul_cancel₀ _ (by exact_mod_cast Nat.factorial_ne_zero k)

theorem rowWeight_factorial (r : Fin 5) (k : ℕ) :
    rowWeight p hp7 r k * ((r.val + k).factorial : ℤ_[p]) = inputCoefficient p r k := by
  have hf : ((r.val + k).choose k : ℤ_[p]) * (k.factorial : ℤ_[p]) *
      (r.val.factorial : ℤ_[p]) = ((r.val + k).factorial : ℤ_[p]) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k r.val)
    simpa only [Nat.add_sub_cancel] using (show
      ((r.val + k).choose k : ℤ_[p]) * (k.factorial : ℤ_[p]) *
        ((r.val + k - k).factorial : ℤ_[p]) = ((r.val + k).factorial : ℤ_[p]) from
          by exact_mod_cast h)
  unfold rowWeight inputCoefficient
  rw [← hf]
  calc
    _ = (-1 : ℤ_[p]) ^ k * ((r.val + k).choose k : ℤ_[p]) *
      (factorialTail p hp7 k * (k.factorial : ℤ_[p])) *
      (InverseTraceAlgebra.inverseFactorial p hp7 r * (r.val.factorial : ℤ_[p])) := by ring
    _ = _ := by rw [factorialTail_mul, InverseTraceAlgebra.inverseFactorial_mul, mul_one]

theorem localized_rowWeight (r : Fin 5) (k : ℕ) :
    algebraMap ℤ_[p] L (inputCoefficient p r k) *
        RationalizedCartier.inverseFactorial p (r.val + k) =
      algebraMap ℤ_[p] L (rowWeight p hp7 r k) := by
  apply (RationalizedCartier.factorial_isUnit p (r.val + k)).mul_right_cancel
  rw [mul_assoc, mul_comm (RationalizedCartier.inverseFactorial p (r.val + k)),
    RationalizedCartier.factorial_mul_inverse, mul_one, ← map_mul, rowWeight_factorial]

def normalizedInputSeries (r : Fin 5) (k : ℕ) : InteriorSeries.Completed p hp7 :=
  InteriorSeries.clearedSeriesMap p hp7 (p * inputHeight r k) (inputHeight r k)
    (by have hp : 0 < p := (Fact.out : p.Prime).pos; unfold inputHeight; nlinarith)
    (by unfold inputHeight; omega) (le_refl _)
    ⟨G p hp7 ^ k, (inputNumerator p hp7 r k).property⟩

theorem strictSeries_transport (m1 m2 h : ℕ) (he : m1 = m2)
    (hm1 : 1 ≤ m1) (hm2 : 1 ≤ m2) (hh : 1 ≤ h)
    (h1 : m1 ≤ p * h) (h2 : m2 ≤ p * h)
    (A1 : numeratorFiltration ℤ_[p] (m1 - 1))
    (A2 : numeratorFiltration ℤ_[p] (m2 - 1)) (hval : A1.val = A2.val) :
    InteriorSeries.clearedSeriesMap p hp7 m1 h hm1 hh h1 A1 =
      InteriorSeries.clearedSeriesMap p hp7 m2 h hm2 hh h2 A2 := by
  subst m2
  have hA : A1 = A2 := Subtype.ext hval
  subst A2
  rfl

set_option maxHeartbeats 800000 in
theorem cartier_pullback_term (r : Fin 5) (k : ℕ) :
    RationalizedCartier.cartier p hp7
      (algebraMap ℤ_[p] L (inputCoefficient p r k) •
        RationalizedCartier.rawPole p hp7 (inputIndex p r k) (inputNumerator p hp7 r k)) =
      RationalizedCartier.integralMap p hp7
        (rowWeight p hp7 r k • normalizedInputSeries p hp7 r k) := by
  have hn := inputPole p r k
  have hc := RationalizedCartier.cartier_rawPole_normalized p hp7 (inputIndex p r k)
    (inputHeight r k) (inputNumerator p hp7 r k)
    (by unfold inputHeight; omega) (by rw [hn])
  have hs : InteriorSeries.clearedSeriesMap p hp7 (inputIndex p r k + 1)
      (inputHeight r k) (by omega) (by unfold inputHeight; omega) (by rw [hn])
      ⟨(inputNumerator p hp7 r k).val,
        by simpa only [Nat.add_sub_cancel] using (inputNumerator p hp7 r k).property⟩ =
      normalizedInputSeries p hp7 r k :=
    strictSeries_transport p hp7 (inputIndex p r k + 1) (p * inputHeight r k)
      (inputHeight r k) hn (by omega)
      (by have hp : 0 < p := (Fact.out : p.Prime).pos; unfold inputHeight; nlinarith)
      (by unfold inputHeight; omega) (by rw [hn]) (le_refl _)
      ⟨(inputNumerator p hp7 r k).val,
        by simpa only [Nat.add_sub_cancel] using (inputNumerator p hp7 r k).property⟩
      ⟨G p hp7 ^ k, (inputNumerator p hp7 r k).property⟩ rfl
  have hc' := hc.trans (congrArg (fun x : InteriorSeries.Completed p hp7 =>
    RationalizedCartier.inverseFactorial p (inputHeight r k - 1) •
      RationalizedCartier.integralMap p hp7 x) hs)
  rw [map_smul, hc', smul_smul]
  have hh : inputHeight r k - 1 = r.val + k := by unfold inputHeight; omega
  rw [hh, localized_rowWeight, IsScalarTower.algebraMap_smul, ← map_smul]

theorem rowSum_eq_normalizedInput (r : Fin 5) (k : ℕ) :
    InverseTraceImage.rowSum p hp7 r k =
      rowWeight p hp7 r k • normalizedInputSeries p hp7 r k := by
  let a := fun l => InteriorSeries.clearedTermMap p hp7 (p * inputHeight r k)
    (inputHeight r k)
    (by have hp : 0 < p := (Fact.out : p.Prime).pos; unfold inputHeight; nlinarith)
    (by unfold inputHeight; omega) (le_refl _) l
    ⟨G p hp7 ^ k, (inputNumerator p hp7 r k).property⟩
  have ha := InteriorSeries.clearedTermMap_eventual p hp7 (p * inputHeight r k)
    (inputHeight r k)
    (by have hp : 0 < p := (Fact.out : p.Prime).pos; unfold inputHeight; nlinarith)
    (by unfold inputHeight; omega) (le_refl _)
    ⟨G p hp7 ^ k, (inputNumerator p hp7 r k).property⟩
  have heq : InverseTraceImage.rowTerm p hp7 r k = fun l => rowWeight p hp7 r k • a l := by
    funext l
    apply Subtype.ext
    have hind : inputHeight r k + l - 1 = r.val + (k + l) := by unfold inputHeight; omega
    change InverseTraceAlgebra.normalizedCoefficient p hp7 r (k + l) k •
      factorialNumeratorMap u (r.val + (k + l)) (kappa p (Fact.out : p.Prime).pos
        (G p hp7 ^ (k + l))) = rowWeight p hp7 r k •
      NumericalTerms.clearedTerm p hp7 (G p hp7 ^ k) (p * inputHeight r k)
        (inputHeight r k) l
    simp only [InverseTraceAlgebra.normalizedCoefficient, Nat.add_sub_cancel_left,
      rowWeight, NumericalTerms.clearedTerm, NumericalTerms.selectedNumerator,
      Nat.sub_self, pow_zero, mul_one, ← pow_add, hind, smul_smul]
    congr 1
    ring
  change AdicSeries.sum (p : ℤ_[p]) (InverseTraceImage.rowTerm p hp7 r k) _ =
    rowWeight p hp7 r k • AdicSeries.sum (p : ℤ_[p]) a ha
  simp only [heq]
  exact AdicSeries.sum_smul _ _ _ _

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The computed coefficient cancellation is applied to the actual constructed
operator on the actual finite pullback, without a Frobenius premise. -/
theorem cartier_finitePullback (N : ℕ) (hN : 1 ≤ N) (r : Fin 5) :
    RationalizedCartier.cartier p hp7 (finitePullback p hp7 N r) =
      RationalizedCartier.integralMap p hp7
        (ofModule (p : ℤ_[p])
          (InverseTraceAlgebra.inverseFactorial p hp7 r •
            InverseTraceTail.selectedFactorial p hp7 r 0) +
          InverseTraceTail.tail p hp7 N hN r) := by
  rw [finitePullback, map_sum]
  simp_rw [cartier_pullback_term, ← rowSum_eq_normalizedInput]
  rw [← map_sum, InverseTraceImage.finite_rowSum_eq_head_add_tail p hp7 r N hN]
  rfl

end

end WPCompletedCartier.InverseTraceConstruction
