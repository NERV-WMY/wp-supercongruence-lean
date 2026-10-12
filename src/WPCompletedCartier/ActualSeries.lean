import WPCompletedCartier.NumericalTerms
import WPCompletedCartier.AdicSeries
import WPCompletedCartier.FiniteCompatibility

namespace WPCompletedCartier.ActualSeries

noncomputable section
open scoped BigOperators
open WPResidueQuotient
open WPCompletedCartier.NumericalTerms
open WPResidueQuotient.Adic

variable (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)

abbrev Coeff := ℤ_[p]
abbrev Module := FClosed (Parameter.integralTenth p hp7)
abbrev Completed := Completion (p : ℤ_[p]) (Module p hp7)

def clearedTermMap (m h : ℕ) (hh : 1 ≤ h) (hmh : m ≤ p * h) (k : ℕ) :
    numeratorFiltration ℤ_[p] m →ₗ[ℤ_[p]] Module p hp7 where
  toFun A := ⟨NumericalTerms.clearedTerm p hp7 A.val m h k,
    clearedTerm_mem_closed p hp7 A.val m h k hh hmh A.property⟩
  map_add' A B := by
    apply Subtype.ext
    simp only [NumericalTerms.clearedTerm, NumericalTerms.selectedNumerator,
      Submodule.coe_add, add_mul, map_add, smul_add]
  map_smul' r A := by
    apply Subtype.ext
    simp only [NumericalTerms.clearedTerm, NumericalTerms.selectedNumerator,
      SetLike.val_smul, smul_mul_assoc, map_smul, smul_smul]
    congr 1
    exact mul_comm _ _

theorem clearedTermMap_eventual (m h : ℕ) (hh : 1 ≤ h) (hmh : m ≤ p * h)
    (A : numeratorFiltration ℤ_[p] m) :
    AdicSeries.EventuallyDivisible (p : ℤ_[p])
      (fun k => clearedTermMap p hp7 m h hh hmh k A) := by
  intro n
  refine ⟨6 * n + 1, ?_⟩
  intro k hk
  obtain ⟨z, hz⟩ := (mem_powerSubmodule _ _ _).mp
    (factorialTail_eventual p hp7 n k hk)
  let q : Module p hp7 :=
    ⟨factorialNumeratorMap (Parameter.integralTenth p hp7) (h + k - 1)
      (NumericalTerms.selectedNumerator p hp7 A.val m h k),
      factorialNumeratorMap_mem_closed _ _ (by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ h + k)] using
          selectedNumerator_closed p hp7 A.val m h k hmh A.property)⟩
  refine ⟨z • q, ?_⟩
  apply Subtype.ext
  change (p : ℤ_[p]) ^ n • (z • q.val) = factorialTail p hp7 k • q.val
  rw [← mul_smul]
  change ((p : ℤ_[p]) ^ n • z) • q.val = _
  rw [hz]

def clearedSeriesMap (m h : ℕ) (hh : 1 ≤ h) (hmh : m ≤ p * h) :
    numeratorFiltration ℤ_[p] m →ₗ[ℤ_[p]] Completed p hp7 where
  toFun A := AdicSeries.sum (p : ℤ_[p])
    (fun k => clearedTermMap p hp7 m h hh hmh k A)
    (clearedTermMap_eventual p hp7 m h hh hmh A)
  map_add' A B := by
    simp only [map_add]
    exact AdicSeries.sum_add _ _ _ _ _
  map_smul' r A := by
    simp only [map_smul]
    exact AdicSeries.sum_smul _ _ _ _

theorem clearedSeriesMap_converges (m h : ℕ) (hh : 1 ≤ h) (hmh : m ≤ p * h)
    (A : numeratorFiltration ℤ_[p] m) :
    Filter.Tendsto
      (fun K => ofModule (p : ℤ_[p])
        (∑ k ∈ Finset.range K, clearedTermMap p hp7 m h hh hmh k A))
      Filter.atTop (nhds (clearedSeriesMap p hp7 m h hh hmh A)) :=
  AdicSeries.tendsto_partialSum _ _ _

theorem clearedTerm_eq_generic (A : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (m h k : ℕ) (hh : 1 ≤ h) :
    WPCompletedCartier.clearedTerm (Parameter.integralTenth p hp7)
      (kappa p (Fact.out : p.Prime).pos) (G p hp7) A p m h
      (factorialTail p hp7) k = NumericalTerms.clearedTerm p hp7 A m h k := by
  unfold WPCompletedCartier.clearedTerm
  rw [gammaNumeratorMap_eq_factorial _ (h + k) (by omega)]
  rfl

theorem clearedTermMap_successor (m h : ℕ) (hh : 1 ≤ h) (hmh : m ≤ p * h)
    (A : numeratorFiltration ℤ_[p] m) (k : ℕ) :
    clearedTermMap p hp7 m (h + 1) (by omega)
      (hmh.trans (Nat.mul_le_mul_left p (Nat.le_succ h))) k A =
      (h + k) • clearedTermMap p hp7 m h hh hmh k A -
        (k + 1) • clearedTermMap p hp7 m h hh hmh (k + 1) A := by
  have hG : f p hp7 ^ p = phi p (f p hp7) - (p : ℤ_[p]) • G p hp7 := by
    apply (eq_sub_iff_add_eq).mpr
    simpa only [add_comm] using (eq_sub_iff_add_eq).mp (G_scaled p hp7)
  have hs := WPCompletedCartier.clearedTerm_successor
    (Parameter.integralTenth p hp7) (kappa p (Fact.out : p.Prime).pos)
    (phi p) (G p hp7) A.val p m h (factorialTail p hp7) (by omega) hmh hG
    (fun H => kappa_mul_phi p (Fact.out : p.Prime).pos H (f p hp7))
    (fun k => by simpa only [Nat.cast_add, Nat.cast_one] using
      factorialTail_recurrence p hp7 k) k
  rw [clearedTerm_eq_generic p hp7 _ _ _ _ (by omega),
    clearedTerm_eq_generic p hp7 _ _ _ _ hh,
    clearedTerm_eq_generic p hp7 _ _ _ _ hh] at hs
  apply Subtype.ext
  exact hs

theorem clearedSeriesMap_successor (m h : ℕ) (hh : 1 ≤ h) (hmh : m ≤ p * h)
    (A : numeratorFiltration ℤ_[p] m) :
    clearedSeriesMap p hp7 m (h + 1) (by omega)
      (hmh.trans (Nat.mul_le_mul_left p (Nat.le_succ h))) A =
      (h : ℤ_[p]) • clearedSeriesMap p hp7 m h hh hmh A := by
  let a := fun k => clearedTermMap p hp7 m h hh hmh k A
  let b := fun k => clearedTermMap p hp7 m (h + 1) (by omega)
    (hmh.trans (Nat.mul_le_mul_left p (Nat.le_succ h))) k A
  have ha := clearedTermMap_eventual p hp7 m h hh hmh A
  have hb := clearedTermMap_eventual p hp7 m (h + 1) (by omega)
    (hmh.trans (Nat.mul_le_mul_left p (Nat.le_succ h))) A
  change AdicSeries.sum (p : ℤ_[p]) b hb = (h : ℤ_[p]) • AdicSeries.sum (p : ℤ_[p]) a ha
  apply AdicSeries.sum_eq_of_finite_telescoping (p : ℤ_[p]) (h : ℤ_[p])
    (fun K => -(K : ℤ_[p])) a b a ha hb ha
  apply Filter.Eventually.of_forall
  intro K
  have he : AdicSeries.partialSum b K = h • AdicSeries.partialSum a K - K • a K := by
    unfold AdicSeries.partialSum
    have heq (k : ℕ) : b k = (h + k) • a k - (k + 1) • a (k + 1) :=
      clearedTermMap_successor p hp7 m h hh hmh A k
    simp_rw [heq]
    exact normalized_pascal_telescoping h K a
  simpa only [Nat.cast_smul_eq_nsmul, neg_smul, sub_eq_add_neg] using he

theorem clearedSeriesMap_factorial_transport (m h0 h : ℕ) (hh0 : 1 ≤ h0)
    (hmh0 : m ≤ p * h0) (hh : h0 ≤ h) (A : numeratorFiltration ℤ_[p] m) :
    ((h - 1).factorial : ℤ_[p]) • clearedSeriesMap p hp7 m h0 hh0 hmh0 A =
      ((h0 - 1).factorial : ℤ_[p]) • clearedSeriesMap p hp7 m h
        (hh0.trans hh) (hmh0.trans (Nat.mul_le_mul_left p hh)) A := by
  induction h, hh using Nat.le_induction with
  | base => rfl
  | succ h hh ih =>
      have hh1 : 1 ≤ h := hh0.trans hh
      have hf : ((h + 1 - 1).factorial : ℤ_[p]) =
          (h : ℤ_[p]) * ((h - 1).factorial : ℤ_[p]) := by
        have ht : h - 1 + 1 = h := by omega
        rw [Nat.add_sub_cancel, ← ht, Nat.factorial_succ]
        push_cast
        ring
      rw [hf, mul_smul, ih,
        clearedSeriesMap_successor p hp7 m h hh1
          (hmh0.trans (Nat.mul_le_mul_left p hh)) A]
      simp only [smul_smul]
      congr 1
      ring

def height (n : ℕ) : ℕ := n / p + 1

omit [Fact p.Prime] in
theorem height_positive (n : ℕ) : 1 ≤ height p n := by
  unfold height
  exact Nat.le_add_left 1 (n / p)

omit [Fact p.Prime] in
theorem height_le_pole (n : ℕ) : height p n ≤ n + 1 := by
  have h := Nat.div_le_self n p
  unfold height
  omega

theorem height_admissible (n : ℕ) : n + 1 ≤ p * height p n := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have he := Nat.mod_add_div n p
  have hr := Nat.mod_lt n hp
  unfold height
  rw [Nat.mul_add, Nat.mul_one]
  omega

def generatorImage (n : ℕ) (A : numeratorFiltration ℤ_[p] (n + 1)) :
    Completed p hp7 :=
  (factorialRatio (n + 1) (height p n) : ℤ_[p]) •
    clearedSeriesMap p hp7 (n + 1) (height p n)
      (height_positive p n) (height_admissible p n) A

theorem generatorImage_converges (n : ℕ)
    (A : numeratorFiltration ℤ_[p] (n + 1)) :
    Filter.Tendsto
      (fun K => ofModule (p : ℤ_[p])
        (∑ k ∈ Finset.range K,
          closedTerm p hp7 A.val (n + 1) (height p n) k
            (height_positive p n) (height_admissible p n) A.property))
      Filter.atTop (nhds (generatorImage p hp7 n A)) := by
  have he : ∀ k,
      closedTerm p hp7 A.val (n + 1) (height p n) k
        (height_positive p n) (height_admissible p n) A.property =
      (factorialRatio (n + 1) (height p n) : ℤ_[p]) •
        clearedTermMap p hp7 (n + 1) (height p n)
          (height_positive p n) (height_admissible p n) k A := by
    intro k
    apply Subtype.ext
    change (factorialTail p hp7 k * (factorialRatio (n + 1) (height p n) : ℤ_[p])) •
      factorialNumeratorMap _ _ _ =
        (factorialRatio (n + 1) (height p n) : ℤ_[p]) •
          (factorialTail p hp7 k • factorialNumeratorMap _ _ _)
    rw [smul_smul, mul_comm]
  let a := fun k => closedTerm p hp7 A.val (n + 1) (height p n) k
    (height_positive p n) (height_admissible p n) A.property
  have ha : AdicSeries.EventuallyDivisible (p : ℤ_[p]) a := by
    intro t
    exact ⟨6 * t + 1, fun k hk => closedTerm_eventual p hp7 _ _ _ _ _ _ t k hk⟩
  have hsum : AdicSeries.sum (p : ℤ_[p]) a ha = generatorImage p hp7 n A := by
    change AdicSeries.sum (p : ℤ_[p]) a ha =
      (factorialRatio (n + 1) (height p n) : ℤ_[p]) •
        AdicSeries.sum (p : ℤ_[p])
          (fun k => clearedTermMap p hp7 (n + 1) (height p n)
            (height_positive p n) (height_admissible p n) k A) _
    have heq : a = fun k => (factorialRatio (n + 1) (height p n) : ℤ_[p]) •
        clearedTermMap p hp7 (n + 1) (height p n)
          (height_positive p n) (height_admissible p n) k A := funext he
    simp only [heq]
    exact AdicSeries.sum_smul _ _ _ _
  rw [← hsum]
  exact AdicSeries.tendsto_partialSum _ _ _

theorem generatorImage_factorial_cleared (n h : ℕ)
    (A : numeratorFiltration ℤ_[p] (n + 1)) (hh : height p n ≤ h) :
    ((h - 1).factorial : ℤ_[p]) • generatorImage p hp7 n A =
      (n.factorial : ℤ_[p]) • clearedSeriesMap p hp7 (n + 1) h
        ((height_positive p n).trans hh)
        ((height_admissible p n).trans (Nat.mul_le_mul_left p hh)) A := by
  have ht := clearedSeriesMap_factorial_transport p hp7 (n + 1) (height p n) h
    (height_positive p n) (height_admissible p n) hh A
  have hf : (factorialRatio (n + 1) (height p n) : ℤ_[p]) *
      ((height p n - 1).factorial : ℤ_[p]) = (n.factorial : ℤ_[p]) := by
    exact_mod_cast factorialRatio_mul (n + 1) (height p n) (height_le_pole p n)
  unfold generatorImage
  calc
    _ = (factorialRatio (n + 1) (height p n) : ℤ_[p]) •
        (((h - 1).factorial : ℤ_[p]) •
          clearedSeriesMap p hp7 (n + 1) (height p n)
            (height_positive p n) (height_admissible p n) A) := by
      simp only [smul_smul]
      congr 1
      ring
    _ = _ := by rw [ht, smul_smul, hf]

def raiseNumerator (m M : ℕ) (hmM : m ≤ M) :
    numeratorFiltration ℤ_[p] m →ₗ[ℤ_[p]] numeratorFiltration ℤ_[p] M where
  toFun A := ⟨A.val * f p hp7 ^ (M - m), by
    have hs := numeratorFiltration_mul_f_pow (Parameter.integralTenth p hp7)
      m (M - m) A.property
    simpa only [Nat.add_sub_of_le hmM, f] using hs⟩
  map_add' A B := Subtype.ext (add_mul _ _ _)
  map_smul' r A := Subtype.ext (smul_mul_assoc _ _ _)

theorem clearedTermMap_common_pole (m M h : ℕ) (hmM : m ≤ M)
    (hh : 1 ≤ h) (hMh : M ≤ p * h) (A : numeratorFiltration ℤ_[p] m) (k : ℕ) :
    clearedTermMap p hp7 M h hh hMh k (raiseNumerator p hp7 m M hmM A) =
      clearedTermMap p hp7 m h hh (hmM.trans hMh) k A := by
  apply Subtype.ext
  change factorialTail p hp7 k • factorialNumeratorMap _ (h + k - 1)
      (NumericalTerms.selectedNumerator p hp7 (A.val * f p hp7 ^ (M - m)) M h k) =
    factorialTail p hp7 k • factorialNumeratorMap _ (h + k - 1)
      (NumericalTerms.selectedNumerator p hp7 A.val m h k)
  congr 2
  exact selectedNumerator_common_pole
    (kappa p (Fact.out : p.Prime).pos) (f p hp7) (G p hp7) A.val p m M h k hmM hMh

theorem clearedSeriesMap_common_pole (m M h : ℕ) (hmM : m ≤ M)
    (hh : 1 ≤ h) (hMh : M ≤ p * h) (A : numeratorFiltration ℤ_[p] m) :
    clearedSeriesMap p hp7 M h hh hMh (raiseNumerator p hp7 m M hmM A) =
      clearedSeriesMap p hp7 m h hh (hmM.trans hMh) A := by
  change AdicSeries.sum (p : ℤ_[p])
    (fun k => clearedTermMap p hp7 M h hh hMh k (raiseNumerator p hp7 m M hmM A)) _ =
    AdicSeries.sum (p : ℤ_[p])
      (fun k => clearedTermMap p hp7 m h hh (hmM.trans hMh) k A) _
  congr 1
  funext k
  exact clearedTermMap_common_pole p hp7 m M h hmM hh hMh A k

theorem completed_factorial_cancel (n : ℕ) :
    Function.Injective (fun x : Completed p hp7 => (n.factorial : ℤ_[p]) • x) := by
  obtain ⟨b, e, he⟩ := factorial_clear_p_power p n
  apply AdicSeries.completion_scalar_injective_of_multiple (p : ℤ_[p]) _ b e
    (AdicSeries.actualClosed_smul_injective (Parameter.integralTenth p hp7)
      (p : ℤ_[p]) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)) he

end

end WPCompletedCartier.ActualSeries
