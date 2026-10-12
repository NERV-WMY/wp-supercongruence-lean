import WPCompletedCartier.ActualSeries

namespace WPCompletedCartier.InteriorSeries

noncomputable section
open scoped BigOperators
open WPResidueQuotient WPResidueQuotient.Adic WPResidueQuotient.ActualCompletion
open WPCompletedCartier.NumericalTerms

variable (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)

abbrev Module := FInterior (Parameter.integralTenth p hp7)
abbrev Completed := Completion (p : ℤ_[p]) (Module p hp7)

def clearedTermMap (m h : ℕ) (hm : 1 ≤ m) (_hh : 1 ≤ h)
    (hmh : m ≤ p * h) (k : ℕ) :
    numeratorFiltration ℤ_[p] (m - 1) →ₗ[ℤ_[p]] Module p hp7 where
  toFun A := ⟨NumericalTerms.clearedTerm p hp7 A.val m h k,
    clearedTerm_mem_interior p hp7 A.val m h k hm hmh A.property⟩
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

theorem clearedTermMap_eventual (m h : ℕ) (hm : 1 ≤ m) (hh : 1 ≤ h)
    (hmh : m ≤ p * h) (A : numeratorFiltration ℤ_[p] (m - 1)) :
    AdicSeries.EventuallyDivisible (p : ℤ_[p])
      (fun k => clearedTermMap p hp7 m h hm hh hmh k A) := by
  intro n
  exact ⟨6 * n + 1, fun k hk =>
    clearedInteriorTerm_eventual p hp7 A.val m h hm hmh A.property n k hk⟩

def clearedSeriesMap (m h : ℕ) (hm : 1 ≤ m) (hh : 1 ≤ h) (hmh : m ≤ p * h) :
    numeratorFiltration ℤ_[p] (m - 1) →ₗ[ℤ_[p]] Completed p hp7 where
  toFun A := AdicSeries.sum (p : ℤ_[p])
    (fun k => clearedTermMap p hp7 m h hm hh hmh k A)
    (clearedTermMap_eventual p hp7 m h hm hh hmh A)
  map_add' A B := by
    simp only [map_add]
    exact AdicSeries.sum_add _ _ _ _ _
  map_smul' r A := by
    simp only [map_smul]
    exact AdicSeries.sum_smul _ _ _ _

theorem clearedSeriesMap_converges (m h : ℕ) (hm : 1 ≤ m) (hh : 1 ≤ h)
    (hmh : m ≤ p * h) (A : numeratorFiltration ℤ_[p] (m - 1)) :
    Filter.Tendsto
      (fun K => ofModule (p : ℤ_[p])
        (∑ k ∈ Finset.range K, clearedTermMap p hp7 m h hm hh hmh k A))
      Filter.atTop (nhds (clearedSeriesMap p hp7 m h hm hh hmh A)) :=
  AdicSeries.tendsto_partialSum _ _ _

theorem clearedTermMap_successor (m h : ℕ) (hm : 1 ≤ m) (hh : 1 ≤ h)
    (hmh : m ≤ p * h) (A : numeratorFiltration ℤ_[p] (m - 1)) (k : ℕ) :
    clearedTermMap p hp7 m (h + 1) hm (by omega)
      (hmh.trans (Nat.mul_le_mul_left p (Nat.le_succ h))) k A =
      (h + k) • clearedTermMap p hp7 m h hm hh hmh k A -
        (k + 1) • clearedTermMap p hp7 m h hm hh hmh (k + 1) A := by
  have hG : f p hp7 ^ p = phi p (f p hp7) - (p : ℤ_[p]) • G p hp7 := by
    apply (eq_sub_iff_add_eq).mpr
    simpa only [add_comm] using (eq_sub_iff_add_eq).mp (G_scaled p hp7)
  have hs := WPCompletedCartier.clearedTerm_successor
    (Parameter.integralTenth p hp7) (kappa p (Fact.out : p.Prime).pos)
    (phi p) (G p hp7) A.val p m h (factorialTail p hp7) (by omega) hmh hG
    (fun H => kappa_mul_phi p (Fact.out : p.Prime).pos H (f p hp7))
    (fun k => by simpa only [Nat.cast_add, Nat.cast_one] using
      factorialTail_recurrence p hp7 k) k
  rw [ActualSeries.clearedTerm_eq_generic p hp7 _ _ _ _ (by omega),
    ActualSeries.clearedTerm_eq_generic p hp7 _ _ _ _ hh,
    ActualSeries.clearedTerm_eq_generic p hp7 _ _ _ _ hh] at hs
  apply Subtype.ext
  exact hs

theorem clearedSeriesMap_successor (m h : ℕ) (hm : 1 ≤ m) (hh : 1 ≤ h)
    (hmh : m ≤ p * h) (A : numeratorFiltration ℤ_[p] (m - 1)) :
    clearedSeriesMap p hp7 m (h + 1) hm (by omega)
      (hmh.trans (Nat.mul_le_mul_left p (Nat.le_succ h))) A =
      (h : ℤ_[p]) • clearedSeriesMap p hp7 m h hm hh hmh A := by
  let a := fun k => clearedTermMap p hp7 m h hm hh hmh k A
  let b := fun k => clearedTermMap p hp7 m (h + 1) hm (by omega)
    (hmh.trans (Nat.mul_le_mul_left p (Nat.le_succ h))) k A
  have ha := clearedTermMap_eventual p hp7 m h hm hh hmh A
  have hb := clearedTermMap_eventual p hp7 m (h + 1) hm (by omega)
    (hmh.trans (Nat.mul_le_mul_left p (Nat.le_succ h))) A
  change AdicSeries.sum (p : ℤ_[p]) b hb = (h : ℤ_[p]) • AdicSeries.sum (p : ℤ_[p]) a ha
  apply AdicSeries.sum_eq_of_finite_telescoping (p : ℤ_[p]) (h : ℤ_[p])
    (fun K => -(K : ℤ_[p])) a b a ha hb ha
  apply Filter.Eventually.of_forall
  intro K
  have he : AdicSeries.partialSum b K = h • AdicSeries.partialSum a K - K • a K := by
    unfold AdicSeries.partialSum
    have heq (k : ℕ) : b k = (h + k) • a k - (k + 1) • a (k + 1) :=
      clearedTermMap_successor p hp7 m h hm hh hmh A k
    simp_rw [heq]
    exact normalized_pascal_telescoping h K a
  simpa only [Nat.cast_smul_eq_nsmul, neg_smul, sub_eq_add_neg] using he

theorem clearedSeriesMap_factorial_transport (m h0 h : ℕ) (hm : 1 ≤ m)
    (hh0 : 1 ≤ h0) (hmh0 : m ≤ p * h0) (hh : h0 ≤ h)
    (A : numeratorFiltration ℤ_[p] (m - 1)) :
    ((h - 1).factorial : ℤ_[p]) • clearedSeriesMap p hp7 m h0 hm hh0 hmh0 A =
      ((h0 - 1).factorial : ℤ_[p]) • clearedSeriesMap p hp7 m h hm
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
        clearedSeriesMap_successor p hp7 m h hm hh1
          (hmh0.trans (Nat.mul_le_mul_left p hh)) A]
      simp only [smul_smul]
      congr 1
      ring

def generatorImage (n : ℕ) (A : numeratorFiltration ℤ_[p] n) : Completed p hp7 :=
  (factorialRatio (n + 1) (ActualSeries.height p n) : ℤ_[p]) •
    clearedSeriesMap p hp7 (n + 1) (ActualSeries.height p n) (by omega)
      (ActualSeries.height_positive p n) (ActualSeries.height_admissible p n)
      ⟨A.val, by simpa only [Nat.add_sub_cancel] using A.property⟩

theorem generatorImage_converges (n : ℕ) (A : numeratorFiltration ℤ_[p] n) :
    Filter.Tendsto
      (fun K => ofModule (p : ℤ_[p])
        (∑ k ∈ Finset.range K,
          interiorTerm p hp7 A.val (n + 1) (ActualSeries.height p n) k (by omega)
            (ActualSeries.height_admissible p n)
            (by simpa only [Nat.add_sub_cancel] using A.property)))
      Filter.atTop (nhds (generatorImage p hp7 n A)) := by
  let A' : numeratorFiltration ℤ_[p] (n + 1 - 1) :=
    ⟨A.val, by simpa only [Nat.add_sub_cancel] using A.property⟩
  have he : ∀ k,
      interiorTerm p hp7 A.val (n + 1) (ActualSeries.height p n) k (by omega)
        (ActualSeries.height_admissible p n)
        (by simpa only [Nat.add_sub_cancel] using A.property) =
      (factorialRatio (n + 1) (ActualSeries.height p n) : ℤ_[p]) •
        clearedTermMap p hp7 (n + 1) (ActualSeries.height p n) (by omega)
          (ActualSeries.height_positive p n) (ActualSeries.height_admissible p n) k A' := by
    intro k
    apply Subtype.ext
    exact generatorTerm_eq_ratio_cleared p hp7 A.val _ _ _
  let a := fun k => interiorTerm p hp7 A.val (n + 1) (ActualSeries.height p n) k
    (by omega) (ActualSeries.height_admissible p n)
    (by simpa only [Nat.add_sub_cancel] using A.property)
  have ha : AdicSeries.EventuallyDivisible (p : ℤ_[p]) a := by
    intro t
    exact ⟨6 * t + 1, fun k hk => interiorTerm_eventual p hp7 _ _ _ _ _ _ t k hk⟩
  have hsum : AdicSeries.sum (p : ℤ_[p]) a ha = generatorImage p hp7 n A := by
    change AdicSeries.sum (p : ℤ_[p]) a ha =
      (factorialRatio (n + 1) (ActualSeries.height p n) : ℤ_[p]) •
        AdicSeries.sum (p : ℤ_[p])
          (fun k => clearedTermMap p hp7 (n + 1) (ActualSeries.height p n) (by omega)
            (ActualSeries.height_positive p n) (ActualSeries.height_admissible p n) k A') _
    have heq : a = fun k =>
        (factorialRatio (n + 1) (ActualSeries.height p n) : ℤ_[p]) •
          clearedTermMap p hp7 (n + 1) (ActualSeries.height p n) (by omega)
            (ActualSeries.height_positive p n) (ActualSeries.height_admissible p n) k A' :=
      funext he
    simp only [heq]
    exact AdicSeries.sum_smul _ _ _ _
  rw [← hsum]
  exact AdicSeries.tendsto_partialSum _ _ _

theorem generatorImage_factorial_cleared (n h : ℕ)
    (A : numeratorFiltration ℤ_[p] n) (hh : ActualSeries.height p n ≤ h) :
    ((h - 1).factorial : ℤ_[p]) • generatorImage p hp7 n A =
      (n.factorial : ℤ_[p]) • clearedSeriesMap p hp7 (n + 1) h (by omega)
        ((ActualSeries.height_positive p n).trans hh)
        ((ActualSeries.height_admissible p n).trans (Nat.mul_le_mul_left p hh))
        ⟨A.val, by simpa only [Nat.add_sub_cancel] using A.property⟩ := by
  have ht := clearedSeriesMap_factorial_transport p hp7 (n + 1)
    (ActualSeries.height p n) h (by omega) (ActualSeries.height_positive p n)
    (ActualSeries.height_admissible p n) hh
    ⟨A.val, by simpa only [Nat.add_sub_cancel] using A.property⟩
  have hf : (factorialRatio (n + 1) (ActualSeries.height p n) : ℤ_[p]) *
      ((ActualSeries.height p n - 1).factorial : ℤ_[p]) = (n.factorial : ℤ_[p]) := by
    exact_mod_cast factorialRatio_mul (n + 1) (ActualSeries.height p n)
      (ActualSeries.height_le_pole p n)
  unfold generatorImage
  calc
    _ = (factorialRatio (n + 1) (ActualSeries.height p n) : ℤ_[p]) •
        (((h - 1).factorial : ℤ_[p]) •
          clearedSeriesMap p hp7 (n + 1) (ActualSeries.height p n) (by omega)
            (ActualSeries.height_positive p n) (ActualSeries.height_admissible p n)
            ⟨A.val, by simpa only [Nat.add_sub_cancel] using A.property⟩) := by
      simp only [smul_smul]
      congr 1
      ring
    _ = _ := by rw [ht, smul_smul, hf]

def raiseNumerator (m M : ℕ) (hm : 1 ≤ m) (hmM : m ≤ M) :
    numeratorFiltration ℤ_[p] (m - 1) →ₗ[ℤ_[p]] numeratorFiltration ℤ_[p] (M - 1) where
  toFun A := ⟨A.val * f p hp7 ^ (M - m), by
    have hs := numeratorFiltration_mul_f_pow (Parameter.integralTenth p hp7)
      (m - 1) (M - m) A.property
    have hd : m - 1 + (M - m) = M - 1 := by omega
    simpa only [hd, f] using hs⟩
  map_add' A B := Subtype.ext (add_mul _ _ _)
  map_smul' r A := Subtype.ext (smul_mul_assoc _ _ _)

theorem clearedTermMap_common_pole (m M h : ℕ) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hh : 1 ≤ h) (hMh : M ≤ p * h)
    (A : numeratorFiltration ℤ_[p] (m - 1)) (k : ℕ) :
    clearedTermMap p hp7 M h (hm.trans hmM) hh hMh k
      (raiseNumerator p hp7 m M hm hmM A) =
      clearedTermMap p hp7 m h hm hh (hmM.trans hMh) k A := by
  apply Subtype.ext
  change factorialTail p hp7 k • factorialNumeratorMap _ (h + k - 1)
      (NumericalTerms.selectedNumerator p hp7 (A.val * f p hp7 ^ (M - m)) M h k) =
    factorialTail p hp7 k • factorialNumeratorMap _ (h + k - 1)
      (NumericalTerms.selectedNumerator p hp7 A.val m h k)
  congr 2
  exact selectedNumerator_common_pole
    (kappa p (Fact.out : p.Prime).pos) (f p hp7) (G p hp7) A.val p m M h k hmM hMh

theorem clearedSeriesMap_common_pole (m M h : ℕ) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hh : 1 ≤ h) (hMh : M ≤ p * h) (A : numeratorFiltration ℤ_[p] (m - 1)) :
    clearedSeriesMap p hp7 M h (hm.trans hmM) hh hMh
      (raiseNumerator p hp7 m M hm hmM A) =
      clearedSeriesMap p hp7 m h hm hh (hmM.trans hMh) A := by
  change AdicSeries.sum (p : ℤ_[p])
    (fun k => clearedTermMap p hp7 M h (hm.trans hmM) hh hMh k
      (raiseNumerator p hp7 m M hm hmM A)) _ =
    AdicSeries.sum (p : ℤ_[p])
      (fun k => clearedTermMap p hp7 m h hm hh (hmM.trans hMh) k A) _
  congr 1
  funext k
  exact clearedTermMap_common_pole p hp7 m M h hm hmM hh hMh A k

theorem completed_factorial_cancel (n : ℕ) :
    Function.Injective (fun x : Completed p hp7 => (n.factorial : ℤ_[p]) • x) := by
  obtain ⟨b, e, he⟩ := factorial_clear_p_power p n
  apply AdicSeries.completion_scalar_injective_of_multiple (p : ℤ_[p]) _ b e
    (AdicSeries.actualInterior_smul_injective (Parameter.integralTenth p hp7)
      (p : ℤ_[p]) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)) he

def numeratorToClosed (m : ℕ) :
    numeratorFiltration ℤ_[p] (m - 1) →ₗ[ℤ_[p]] numeratorFiltration ℤ_[p] m :=
  Submodule.inclusion (numeratorFiltration_mono (Nat.sub_le m 1))

theorem clearedTermMap_inclusion (m h : ℕ) (hm : 1 ≤ m) (hh : 1 ≤ h)
    (hmh : m ≤ p * h) (A : numeratorFiltration ℤ_[p] (m - 1)) (k : ℕ) :
    actualInteriorInclusion (Parameter.integralTenth p hp7)
      (clearedTermMap p hp7 m h hm hh hmh k A) =
      ActualSeries.clearedTermMap p hp7 m h hh hmh k (numeratorToClosed p m A) :=
  Subtype.ext rfl

theorem clearedSeriesMap_inclusion (m h : ℕ) (hm : 1 ≤ m) (hh : 1 ≤ h)
    (hmh : m ≤ p * h) (A : numeratorFiltration ℤ_[p] (m - 1)) :
    completedInteriorInclusion (Parameter.integralTenth p hp7) (p : ℤ_[p])
      (clearedSeriesMap p hp7 m h hm hh hmh A) =
      ActualSeries.clearedSeriesMap p hp7 m h hh hmh (numeratorToClosed p m A) := by
  change completeMap (p : ℤ_[p]) (actualInteriorInclusion (Parameter.integralTenth p hp7))
    (AdicSeries.sum (p : ℤ_[p])
      (fun k => clearedTermMap p hp7 m h hm hh hmh k A)
      (clearedTermMap_eventual p hp7 m h hm hh hmh A)) =
    AdicSeries.sum (p : ℤ_[p])
      (fun k => ActualSeries.clearedTermMap p hp7 m h hh hmh k (numeratorToClosed p m A))
      (ActualSeries.clearedTermMap_eventual p hp7 m h hh hmh (numeratorToClosed p m A))
  rw [AdicSeries.completeMap_sum]
  congr 1

theorem generatorImage_inclusion (n : ℕ) (A : numeratorFiltration ℤ_[p] n) :
    completedInteriorInclusion (Parameter.integralTenth p hp7) (p : ℤ_[p])
      (generatorImage p hp7 n A) =
      ActualSeries.generatorImage p hp7 n
        ⟨A.val, numeratorFiltration_mono (Nat.le_succ n) A.property⟩ := by
  unfold generatorImage ActualSeries.generatorImage
  rw [map_smul, clearedSeriesMap_inclusion]
  rfl

end

end WPCompletedCartier.InteriorSeries
