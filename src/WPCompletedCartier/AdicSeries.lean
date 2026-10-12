import WPResidueQuotient.ActualCompletion
import Mathlib.Topology.DenseEmbedding
import Mathlib.RingTheory.Localization.Module

/-!
Series, cancellation, and extension in the actual principal-scalar inverse
limit. These constructions never use a Laurent-series ambient completion.
-/

namespace WPCompletedCartier.AdicSeries

open WPResidueQuotient.Adic
open scoped BigOperators

noncomputable section

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

def projection (p : R) (n : ℕ) : Completion p M →ₗ[R] Level p M n where
  toFun x := x.val n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem continuous_projection (p : R) (n : ℕ) :
    Continuous (projection (M := M) p n) :=
  (continuous_apply n).comp continuous_subtype_val

theorem levelMk_eq_zero_iff (p : R) (n : ℕ) (x : M) :
    levelMk p n x = 0 ↔ x ∈ powerSubmodule p n := by
  change (Submodule.Quotient.mk x : Level p M n) = Submodule.Quotient.mk 0 ↔ _
  simp only [Submodule.Quotient.eq, sub_zero]

theorem power_smul_level_zero (p : R) (n : ℕ) (x : Level p M n) :
    p ^ n • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change levelMk p n (p ^ n • x) = 0
    exact (levelMk_eq_zero_iff p n _).mpr ⟨x, rfl⟩

/-- The precise integral condition used by the series constructor. -/
def EventuallyDivisible (p : R) (a : ℕ → M) : Prop :=
  ∀ n : ℕ, ∃ K : ℕ, ∀ k, K ≤ k → a k ∈ powerSubmodule p n

def partialSum (a : ℕ → M) (K : ℕ) : M := ∑ k ∈ Finset.range K, a k

def levelPartialSum (p : R) (a : ℕ → M) (n K : ℕ) : Level p M n :=
  levelMk p n (partialSum a K)

@[simp] theorem levelPartialSum_succ (p : R) (a : ℕ → M) (n K : ℕ) :
    levelPartialSum p a n (K + 1) = levelPartialSum p a n K + levelMk p n (a K) := by
  simp [levelPartialSum, partialSum, Finset.sum_range_succ]

theorem levelPartialSum_stable (p : R) (a : ℕ → M) (n K L : ℕ)
    (h : ∀ k, K ≤ k → a k ∈ powerSubmodule p n) (hKL : K ≤ L) :
    levelPartialSum p a n L = levelPartialSum p a n K := by
  induction L, hKL using Nat.le_induction with
  | base => rfl
  | succ L hKL ih =>
    rw [levelPartialSum_succ, (levelMk_eq_zero_iff p n _).mpr (h L hKL), add_zero]
    exact ih

def cutoff (p : R) (a : ℕ → M) (ha : EventuallyDivisible p a) (n : ℕ) : ℕ :=
  Classical.choose (ha n)

theorem cutoff_spec (p : R) (a : ℕ → M) (ha : EventuallyDivisible p a)
    (n k : ℕ) (hk : cutoff p a ha n ≤ k) : a k ∈ powerSubmodule p n :=
  Classical.choose_spec (ha n) k hk

def sum (p : R) (a : ℕ → M) (ha : EventuallyDivisible p a) : Completion p M :=
  ⟨fun n => levelPartialSum p a n (cutoff p a ha n), by
    intro n
    let L := max (cutoff p a ha n) (cutoff p a ha (n + 1))
    have h0 := levelPartialSum_stable p a n (cutoff p a ha n) L
      (cutoff_spec p a ha n) (Nat.le_max_left _ _)
    have h1 := levelPartialSum_stable p a (n + 1) (cutoff p a ha (n + 1)) L
      (cutoff_spec p a ha (n + 1)) (Nat.le_max_right _ _)
    change transition p n (levelPartialSum p a (n + 1) (cutoff p a ha (n + 1))) =
      levelPartialSum p a n (cutoff p a ha n)
    rw [← h1, ← h0]
    exact transition_mk p n (partialSum a L)⟩

theorem sum_level_eq (p : R) (a : ℕ → M) (ha : EventuallyDivisible p a)
    (n K : ℕ) (hK : cutoff p a ha n ≤ K) :
    (sum p a ha).val n = levelPartialSum p a n K := by
  exact (levelPartialSum_stable p a n (cutoff p a ha n) K
    (cutoff_spec p a ha n) hK).symm

/-- Actual finite sums converge in the given inverse-limit topology. -/
theorem tendsto_partialSum (p : R) (a : ℕ → M) (ha : EventuallyDivisible p a) :
    Filter.Tendsto (fun K => ofModule p (partialSum a K)) Filter.atTop
      (nhds (sum p a ha)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro n
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.Ici_mem_atTop (cutoff p a ha n)] with K hK
  exact sum_level_eq p a ha n K hK

theorem sum_unique (p : R) (a : ℕ → M) (ha : EventuallyDivisible p a)
    (x : Completion p M)
    (hx : Filter.Tendsto (fun K => ofModule p (partialSum a K))
      Filter.atTop (nhds x)) : sum p a ha = x :=
  tendsto_nhds_unique (tendsto_partialSum p a ha) hx

theorem eventuallyDivisible_add (p : R) (a b : ℕ → M)
    (ha : EventuallyDivisible p a) (hb : EventuallyDivisible p b) :
    EventuallyDivisible p (fun k => a k + b k) := by
  intro n
  obtain ⟨K, hK⟩ := ha n
  obtain ⟨L, hL⟩ := hb n
  exact ⟨max K L, fun k hk => (powerSubmodule p n).add_mem
    (hK k ((Nat.le_max_left _ _).trans hk))
    (hL k ((Nat.le_max_right _ _).trans hk))⟩

theorem eventuallyDivisible_smul (p r : R) (a : ℕ → M)
    (ha : EventuallyDivisible p a) : EventuallyDivisible p (fun k => r • a k) := by
  intro n
  obtain ⟨K, hK⟩ := ha n
  exact ⟨K, fun k hk => (powerSubmodule p n).smul_mem r (hK k hk)⟩

theorem eventuallyDivisible_variable_smul (p : R) (s : ℕ → R) (a : ℕ → M)
    (ha : EventuallyDivisible p a) : EventuallyDivisible p (fun k => s k • a k) := by
  intro n
  obtain ⟨K, hK⟩ := ha n
  exact ⟨K, fun k hk => (powerSubmodule p n).smul_mem (s k) (hK k hk)⟩

/-- A boundary term tends to zero directly from its proved divisibility. -/
theorem tendsto_ofModule_zero (p : R) (a : ℕ → M) (ha : EventuallyDivisible p a) :
    Filter.Tendsto (fun k => ofModule p (a k)) Filter.atTop
      (nhds (0 : Completion p M)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro n
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.Ici_mem_atTop (cutoff p a ha n)] with k hk
  exact ((levelMk_eq_zero_iff p n _).mpr (cutoff_spec p a ha n k hk)).symm

theorem tendsto_variable_smul_boundary_zero (p : R) (s : ℕ → R) (a : ℕ → M)
    (ha : EventuallyDivisible p a) :
    Filter.Tendsto (fun k => ofModule p (s k • a k)) Filter.atTop
      (nhds (0 : Completion p M)) :=
  tendsto_ofModule_zero p _ (eventuallyDivisible_variable_smul p s a ha)

/-- Equality at each eventual finite quotient level identifies the actual
constructed sums. Neither an ambient identity nor a supplied limit is used. -/
theorem sum_eq_of_eventual_level (p r : R) (a b : ℕ → M)
    (ha : EventuallyDivisible p a) (hb : EventuallyDivisible p b)
    (h : ∀ n, ∀ᶠ K in Filter.atTop,
      levelPartialSum p b n K = r • levelPartialSum p a n K) :
    sum p b hb = r • sum p a ha := by
  apply completion_ext p
  intro n
  have hA : ∀ᶠ K in Filter.atTop, cutoff p a ha n ≤ K :=
    Filter.Ici_mem_atTop (cutoff p a ha n)
  have hB : ∀ᶠ K in Filter.atTop, cutoff p b hb n ≤ K :=
    Filter.Ici_mem_atTop (cutoff p b hb n)
  obtain ⟨K, hK, hAK, hBK⟩ := ((h n).and (hA.and hB)).exists
  change (sum p b hb).val n = r • (sum p a ha).val n
  rw [sum_level_eq p b hb n K hBK, sum_level_eq p a ha n K hAK]
  exact hK

/-- Finite telescoping with any integral scalar boundary, including
`s K = (K : R)`, proves the h-increment identity after summation. -/
theorem sum_eq_of_finite_telescoping (p r : R) (s : ℕ → R) (a b c : ℕ → M)
    (ha : EventuallyDivisible p a) (hb : EventuallyDivisible p b)
    (hc : EventuallyDivisible p c)
    (h : ∀ᶠ K in Filter.atTop,
      partialSum b K = r • partialSum a K + s K • c K) :
    sum p b hb = r • sum p a ha := by
  apply sum_eq_of_eventual_level p r a b ha hb
  intro n
  filter_upwards [h, Filter.Ici_mem_atTop (cutoff p c hc n)] with K hK hC
  have hm := congrArg (levelMk p n) hK
  rw [map_add, map_smul, map_smul,
    (levelMk_eq_zero_iff p n _).mpr (cutoff_spec p c hc n K hC),
    smul_zero, add_zero] at hm
  exact hm

theorem sum_add (p : R) (a b : ℕ → M)
    (ha : EventuallyDivisible p a) (hb : EventuallyDivisible p b) :
    sum p (fun k => a k + b k) (eventuallyDivisible_add p a b ha hb) =
      sum p a ha + sum p b hb := by
  apply sum_unique
  have h := (tendsto_partialSum p a ha).add (tendsto_partialSum p b hb)
  simpa [partialSum, Finset.sum_add_distrib, map_add] using h

theorem sum_smul (p r : R) (a : ℕ → M) (ha : EventuallyDivisible p a) :
    sum p (fun k => r • a k) (eventuallyDivisible_smul p r a ha) =
      r • sum p a ha := by
  apply completion_ext p
  intro n
  let K := max (cutoff p (fun k => r • a k) (eventuallyDivisible_smul p r a ha) n)
    (cutoff p a ha n)
  rw [sum_level_eq p _ _ n K (Nat.le_max_left _ _)]
  change _ = r • (sum p a ha).val n
  rw [sum_level_eq p a ha n K (Nat.le_max_right _ _)]
  simp [levelPartialSum, partialSum, Finset.smul_sum]

theorem eventuallyDivisible_map (p : R) (a : ℕ → M)
    (ha : EventuallyDivisible p a) (f : M →ₗ[R] N) :
    EventuallyDivisible p (fun k => f (a k)) := by
  intro n
  obtain ⟨K, hK⟩ := ha n
  exact ⟨K, fun k hk => map_powerSubmodule p n f (hK k hk)⟩

theorem completeMap_sum (p : R) (a : ℕ → M)
    (ha : EventuallyDivisible p a) (f : M →ₗ[R] N) :
    completeMap p f (sum p a ha) =
      sum p (fun k => f (a k)) (eventuallyDivisible_map p a ha f) := by
  symm
  apply sum_unique
  have h := (continuous_completeMap p f).tendsto (sum p a ha)
    |>.comp (tendsto_partialSum p a ha)
  simpa [Function.comp_def, completeMap_ofModule, partialSum, map_sum] using h

/-- Injectivity of the distinguished scalar on the original module suffices.
No separatedness of the original module is needed. -/
theorem completion_smul_injective (p : R)
    (hp : Function.Injective (fun x : M => p • x)) :
    Function.Injective (fun x : Completion p M => p • x) := by
  suffices hz : ∀ x : Completion p M, p • x = 0 → x = 0 by
    intro x y h
    change p • x = p • y at h
    apply sub_eq_zero.mp
    apply hz
    rw [smul_sub, h, sub_self]
  intro x hx
  apply completion_ext p
  intro n
  obtain ⟨y, hy⟩ := (powerSubmodule (M := M) p (n + 1)).mkQ_surjective (x.val (n + 1))
  have hpy : levelMk p (n + 1) (p • y) = 0 := by
    rw [map_smul]
    change p • (powerSubmodule p (n + 1)).mkQ y = 0
    rw [hy]
    exact congrArg (fun z : Completion p M => z.val (n + 1)) hx
  obtain ⟨z, hz⟩ := (levelMk_eq_zero_iff p (n + 1) _).mp hpy
  change p ^ (n + 1) • z = p • y at hz
  have hydiv : p ^ n • z = y := by
    apply hp
    change p • (p ^ n • z) = p • y
    rw [← mul_smul, ← pow_succ']
    exact hz
  have hn : levelMk p n y = 0 :=
    (levelMk_eq_zero_iff p n y).mpr ⟨z, hydiv⟩
  have ht := x.property n
  rw [← hy] at ht
  change levelMk p n y = x.val n at ht
  exact ht.symm.trans hn

theorem pow_smul_injective (p : R)
    (hp : Function.Injective (fun x : M => p • x)) (n : ℕ) :
    Function.Injective (fun x : M => p ^ n • x) := by
  induction n with
  | zero =>
    intro x y h
    simpa only [pow_zero, one_smul] using h
  | succ n ih =>
    intro x y h
    change p ^ (n + 1) • x = p ^ (n + 1) • y at h
    apply ih
    apply hp
    change p • (p ^ n • x) = p • (p ^ n • y)
    simpa only [pow_succ', mul_smul] using h

theorem completion_pow_smul_injective (p : R)
    (hp : Function.Injective (fun x : M => p • x)) (n : ℕ) :
    Function.Injective (fun x : Completion p M => p ^ n • x) :=
  pow_smul_injective (M := Completion p M) p (completion_smul_injective p hp) n

/-- A scalar whose multiple is a power of the distinguished scalar can be
cancelled, including factorials after their finite valuation is cleared. -/
theorem completion_scalar_injective_of_multiple (p a b : R) (e : ℕ)
    (hp : Function.Injective (fun x : M => p • x)) (hba : b * a = p ^ e) :
    Function.Injective (fun x : Completion p M => a • x) := by
  intro x y h
  apply completion_pow_smul_injective p hp e
  have h' := congrArg (fun z : Completion p M => b • z) h
  simpa only [smul_smul, hba] using h'

/-- Termwise finite scalar clearing is legitimate in the actual completion. -/
theorem eventuallyDivisible_divide (p : R)
    (hp : Function.Injective (fun x : M => p • x)) (n : ℕ)
    (a b : ℕ → M) (ha : EventuallyDivisible p a)
    (hb : ∀ k, p ^ n • b k = a k) : EventuallyDivisible p b := by
  intro r
  obtain ⟨K, hK⟩ := ha (n + r)
  refine ⟨K, ?_⟩
  intro k hk
  obtain ⟨z, hz⟩ := hK k hk
  change p ^ (n + r) • z = a k at hz
  refine ⟨z, ?_⟩
  change p ^ r • z = b k
  apply pow_smul_injective p hp n
  change p ^ n • (p ^ r • z) = p ^ n • b k
  rw [hb k]
  simpa [pow_add, mul_smul] using hz

theorem sum_mem_powerSubmodule (p : R)
    (hp : Function.Injective (fun x : M => p • x)) (n : ℕ)
    (a : ℕ → M) (ha : EventuallyDivisible p a)
    (hdiv : ∀ k, a k ∈ powerSubmodule p n) :
    sum p a ha ∈ powerSubmodule (M := Completion p M) p n := by
  choose b hb using hdiv
  change ∀ k, p ^ n • b k = a k at hb
  have hbRapid := eventuallyDivisible_divide p hp n a b ha hb
  refine ⟨sum p b hbRapid, ?_⟩
  change p ^ n • sum p b hbRapid = sum p a ha
  rw [← sum_smul]
  congr 1
  exact funext hb

theorem eventuallyDivisible_tail (p : R) (a : ℕ → M)
    (ha : EventuallyDivisible p a) (K : ℕ) :
    EventuallyDivisible p (fun k => a (K + k)) := by
  intro n
  obtain ⟨L, hL⟩ := ha n
  exact ⟨L, fun k hk => hL (K + k) (hk.trans (Nat.le_add_left _ _))⟩

theorem sum_tail_mem_powerSubmodule (p : R)
    (hp : Function.Injective (fun x : M => p • x)) (n K : ℕ)
    (a : ℕ → M) (ha : EventuallyDivisible p a)
    (hK : ∀ k, K ≤ k → a k ∈ powerSubmodule p n) :
    sum p (fun k => a (K + k)) (eventuallyDivisible_tail p a ha K) ∈
      powerSubmodule (M := Completion p M) p n := by
  apply sum_mem_powerSubmodule p hp n
  intro k
  exact hK (K + k) (Nat.le_add_right _ _)

theorem sum_eq_partialSum_add_tail (p : R) (a : ℕ → M)
    (ha : EventuallyDivisible p a) (K : ℕ) :
    sum p a ha = ofModule p (partialSum a K) +
      sum p (fun k => a (K + k)) (eventuallyDivisible_tail p a ha K) := by
  apply completion_ext p
  intro n
  let ht := eventuallyDivisible_tail p a ha K
  let L := max (cutoff p a ha n) (cutoff p (fun k => a (K + k)) ht n)
  rw [sum_level_eq p a ha n (K + L)
    ((Nat.le_max_left _ _).trans (Nat.le_add_left _ _))]
  change _ = levelMk p n (partialSum a K) + (sum p (fun k => a (K + k)) ht).val n
  rw [sum_level_eq p _ ht n L (Nat.le_max_right _ _)]
  simp [levelPartialSum, partialSum, Finset.sum_range_add, map_add]

theorem sum_sub_partialSum_mem_powerSubmodule (p : R)
    (hp : Function.Injective (fun x : M => p • x)) (n K : ℕ)
    (a : ℕ → M) (ha : EventuallyDivisible p a)
    (hK : ∀ k, K ≤ k → a k ∈ powerSubmodule p n) :
    sum p a ha - ofModule p (partialSum a K) ∈
      powerSubmodule (M := Completion p M) p n := by
  rw [sum_eq_partialSum_add_tail p a ha K, add_sub_cancel_left]
  exact sum_tail_mem_powerSubmodule p hp n K a ha hK

/-- A linear map into the actual completion already preserves every scalar
power. Its quotient-level descent supplies the extension, rather than a
continuity hypothesis on a desired operator. -/
def extensionLevel (p : R) (f : M →ₗ[R] Completion p N) (n : ℕ) :
    Level p M n →ₗ[R] Level p N n :=
  (powerSubmodule (M := M) p n).liftQ ((projection p n).comp f) (by
    rintro x ⟨y, rfl⟩
    change (f (p ^ n • y)).val n = 0
    rw [map_smul]
    exact power_smul_level_zero p n ((f y).val n))

@[simp] theorem extensionLevel_mk (p : R) (f : M →ₗ[R] Completion p N)
    (n : ℕ) (x : M) : extensionLevel p f n (levelMk p n x) = (f x).val n := rfl

theorem extensionLevel_transition (p : R) (f : M →ₗ[R] Completion p N)
    (n : ℕ) (x : Level p M (n + 1)) :
    transition p n (extensionLevel p f (n + 1) x) =
      extensionLevel p f n (transition p n x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x => exact (f x).property n

def extension (p : R) (f : M →ₗ[R] Completion p N) :
    Completion p M →ₗ[R] Completion p N where
  toFun x := ⟨fun n => extensionLevel p f n (x.val n), fun n => by
    rw [extensionLevel_transition, x.property n]⟩
  map_add' x y := by
    apply completion_ext p
    intro n
    exact map_add (extensionLevel p f n) _ _
  map_smul' r x := by
    apply completion_ext p
    intro n
    exact map_smul (extensionLevel p f n) r _

@[simp] theorem extension_ofModule (p : R) (f : M →ₗ[R] Completion p N)
    (x : M) : extension p f (ofModule p x) = f x := by
  apply completion_ext p
  intro n
  rfl

theorem continuous_extension (p : R) (f : M →ₗ[R] Completion p N) :
    Continuous (extension p f) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := extensionLevel p f n)).comp
    ((continuous_apply n).comp continuous_subtype_val)

theorem extension_unique (p : R) (f : M →ₗ[R] Completion p N)
    (g : Completion p M →ₗ[R] Completion p N) (hg : Continuous g)
    (h : ∀ x, g (ofModule p x) = f x) : g = extension p f := by
  apply LinearMap.ext
  have heq := (denseRange_ofModule (M := M) p).equalizer hg
    (continuous_extension p f) (funext (fun x => (h x).trans (extension_ofModule p f x).symm))
  exact congrFun heq

theorem extension_eq_completeMap (p : R) (f : M →ₗ[R] N) :
    extension p ((ofModule p).comp f) = completeMap p f := by
  symm
  apply extension_unique p _ _ (continuous_completeMap p f)
  intro x
  exact completeMap_ofModule p f x

theorem extension_sum (p : R) (f : M →ₗ[R] Completion p N)
    (a : ℕ → M) (ha : EventuallyDivisible p a) :
    Filter.Tendsto (fun K => f (partialSum a K)) Filter.atTop
      (nhds (extension p f (sum p a ha))) := by
  have h := (continuous_extension p f).tendsto (sum p a ha)
    |>.comp (tendsto_partialSum p a ha)
  simpa only [Function.comp_def, extension_ofModule] using h

/-- A proved logarithmic-derivative identity on the actual module extends
to its actual completion by density and the explicit continuous extension. -/
theorem extension_intertwines (p r : R) (f : M →ₗ[R] Completion p M)
    (d : M →ₗ[R] M)
    (h : ∀ x, f (d x) = r • completeMap p d (f x)) :
    (extension p f).comp (completeMap p d) =
      r • ((completeMap p d).comp (extension p f)) := by
  let g : Completion p M →ₗ[R] Completion p M :=
    r • ((completeMap p d).comp (extension p f))
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro n
    exact (continuous_of_discreteTopology
      (f := fun x : Level p M n => r • x)).comp
      ((continuous_projection p n).comp
        ((continuous_completeMap p d).comp (continuous_extension p f)))
  have hleft : Continuous ((extension p f).comp (completeMap p d)) :=
    (continuous_extension p f).comp (continuous_completeMap p d)
  apply LinearMap.ext
  have heq := (denseRange_ofModule (M := M) p).equalizer hleft hg
    (funext (fun x => by
      change extension p f (completeMap p d (ofModule p x)) =
        r • completeMap p d (extension p f (ofModule p x))
      rw [completeMap_ofModule, extension_ofModule, extension_ofModule]
      exact h x))
  exact congrFun heq

/-- Rationalization at the powers of the distinguished scalar has a proved
injective integral map; finite denominators cannot erase actual classes. -/
theorem rationalization_injective (p : R)
    (hp : Function.Injective (fun x : M => p • x)) :
    Function.Injective (LocalizedModule.mkLinearMap (Submonoid.powers p)
      (Completion p M)) := by
  intro x y h
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers p)
    (LocalizedModule.mkLinearMap (Submonoid.powers p) (Completion p M))).mp h
  obtain ⟨e, he⟩ := c.property
  change (c : R) • x = (c : R) • y at hc
  rw [← he] at hc
  exact completion_pow_smul_injective p hp e hc

def rationalizedMap (p : R) (f : Completion p M →ₗ[R] Completion p N) :
    LocalizedModule (Submonoid.powers p) (Completion p M) →ₗ[Localization
      (Submonoid.powers p)] LocalizedModule (Submonoid.powers p) (Completion p N) :=
  LocalizedModule.map (Submonoid.powers p) f

@[simp] theorem rationalizedMap_mk (p : R)
    (f : Completion p M →ₗ[R] Completion p N) (x : Completion p M)
    (s : Submonoid.powers p) :
    rationalizedMap p f (LocalizedModule.mk x s) = LocalizedModule.mk (f x) s :=
  LocalizedModule.map_mk (Submonoid.powers p) f x s

/-- Continuous linear maps preserve the closure of a proved invariant
submodule; this is the topology input for the closed exact range. -/
theorem mapsTo_closure (f : M →ₗ[R] N) [TopologicalSpace M] [TopologicalSpace N]
    (hf : Continuous f) (S : Submodule R M) (T : Submodule R N)
    (h : ∀ x ∈ S, f x ∈ T) : Set.MapsTo f (closure (S : Set M))
      (closure (T : Set N)) := by
  intro x hx
  have hi := image_closure_subset_closure_image hf ⟨x, hx, rfl⟩
  exact (closure_mono (by rintro y ⟨z, hz, rfl⟩; exact h z hz)) hi

end

section ActualModules

open WPResidueQuotient

variable {R : Type*} [CommRing R] [IsDomain R]

theorem actualScalarMap_injective (u : R) :
    Function.Injective (algebraMap R (ActualRing u)) := by
  intro r s h
  apply FaithfulSMul.algebraMap_injective R (WPResidueQuotient.LaurentPolynomial R)
  apply actual_algebraMap_injective u
  simpa only [IsScalarTower.algebraMap_apply R
    (WPResidueQuotient.LaurentPolynomial R) (ActualRing u)] using h

theorem actualSubmodule_smul_injective (u p : R) (hp : p ≠ 0)
    (S : Submodule R (ActualRing u)) : Function.Injective (fun x : S => p • x) := by
  intro x y h
  apply Subtype.ext
  have hs : algebraMap R (ActualRing u) p ≠ 0 := by
    intro hz
    apply hp
    exact actualScalarMap_injective u (hz.trans (map_zero _).symm)
  have hxy := congrArg Subtype.val h
  change p • (x : ActualRing u) = p • (y : ActualRing u) at hxy
  rw [Algebra.smul_def, Algebra.smul_def] at hxy
  exact mul_left_cancel₀ hs hxy

theorem actualClosed_smul_injective (u p : R) (hp : p ≠ 0) :
    Function.Injective (fun x : FClosed u => p • x) :=
  actualSubmodule_smul_injective u p hp (FClosed u)

theorem actualInterior_smul_injective (u p : R) (hp : p ≠ 0) :
    Function.Injective (fun x : FInterior u => p • x) :=
  actualSubmodule_smul_injective u p hp (FInterior u)

theorem completedClosed_pow_smul_injective (u p : R) (hp : p ≠ 0) (n : ℕ) :
    Function.Injective (fun x : Completion p (FClosed u) => p ^ n • x) :=
  completion_pow_smul_injective p (actualClosed_smul_injective u p hp) n

theorem completedInterior_pow_smul_injective (u p : R) (hp : p ≠ 0) (n : ℕ) :
    Function.Injective (fun x : Completion p (FInterior u) => p ^ n • x) :=
  completion_pow_smul_injective p (actualInterior_smul_injective u p hp) n

end ActualModules

end WPCompletedCartier.AdicSeries
