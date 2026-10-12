import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

/-!
An explicit inverse-limit completion of the *given* module, for the filtration
`p^n M`.  The splitting theorem takes a proved linear equivalence as input.
It does not construct or assume a residue quotient basis.  The residue-module
owner must instantiate it with the actual closed module and exact summand.
-/

namespace WPResidueQuotient.Adic

variable {R : Type*} [CommRing R]
variable {M N K : Type*}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup K] [Module R K]

/-- The actual scalar-image submodule `p^n M`. -/
def powerSubmodule (p : R) (n : ℕ) : Submodule R M :=
  LinearMap.range (p ^ n • (LinearMap.id : M →ₗ[R] M))

theorem mem_powerSubmodule (p : R) (n : ℕ) (x : M) :
    x ∈ powerSubmodule p n ↔ ∃ y : M, p ^ n • y = x := by
  rfl

theorem powerSubmodule_succ_le (p : R) (n : ℕ) :
    powerSubmodule (M := M) p (n + 1) ≤ powerSubmodule p n := by
  rintro x ⟨y, rfl⟩
  refine ⟨p • y, ?_⟩
  change p ^ n • p • y = p ^ (n + 1) • y
  rw [pow_succ, mul_smul]

theorem powerSubmodule_antitone (p : R) :
    Antitone (powerSubmodule (M := M) p) := by
  intro m n h
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n h ih => exact (powerSubmodule_succ_le p n).trans ih

theorem map_powerSubmodule (p : R) (n : ℕ) (f : M →ₗ[R] N) :
    powerSubmodule p n ≤ (powerSubmodule p n).comap f := by
  rintro x ⟨y, rfl⟩
  exact ⟨f y, (f.map_smul (p ^ n) y).symm⟩

/-- A type synonym isolates the discrete topology of each quotient level. -/
abbrev Level (p : R) (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) :=
  M ⧸ powerSubmodule (M := M) p n

instance (p : R) (n : ℕ) : TopologicalSpace (Level p M n) := ⊥

instance (p : R) (n : ℕ) : DiscreteTopology (Level p M n) := ⟨rfl⟩

def levelMk (p : R) (n : ℕ) : M →ₗ[R] Level p M n :=
  (powerSubmodule (M := M) p n).mkQ

def transition (p : R) (n : ℕ) : Level p M (n + 1) →ₗ[R] Level p M n :=
  (powerSubmodule (M := M) p (n + 1)).mapQ (powerSubmodule (M := M) p n) LinearMap.id
    (powerSubmodule_succ_le p n)

@[simp] theorem transition_mk (p : R) (n : ℕ) (x : M) :
    transition p n (levelMk p (n + 1) x) = levelMk p n x := rfl

def transitionLE (p : R) (m n : ℕ) (h : m ≤ n) :
    Level p M n →ₗ[R] Level p M m :=
  (powerSubmodule (M := M) p n).mapQ (powerSubmodule (M := M) p m) LinearMap.id
    (powerSubmodule_antitone p h)

@[simp] theorem transitionLE_mk (p : R) (m n : ℕ) (h : m ≤ n) (x : M) :
    transitionLE p m n h (levelMk p n x) = levelMk p m x := rfl

theorem transitionLE_succ (p : R) (m n : ℕ) (h : m ≤ n)
    (x : Level p M (n + 1)) :
    transitionLE p m (n + 1) (h.trans (Nat.le_succ n)) x =
      transitionLE p m n h (transition p n x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

def levelMap (p : R) (f : M →ₗ[R] N) (n : ℕ) :
    Level p M n →ₗ[R] Level p N n :=
  (powerSubmodule (M := M) p n).mapQ (powerSubmodule (M := N) p n) f
    (map_powerSubmodule p n f)

@[simp] theorem levelMap_mk (p : R) (f : M →ₗ[R] N) (n : ℕ) (x : M) :
    levelMap p f n (levelMk p n x) = levelMk p n (f x) := rfl

theorem levelMap_transition (p : R) (f : M →ₗ[R] N) (n : ℕ)
    (x : Level p M (n + 1)) :
    transition p n (levelMap p f (n + 1) x) =
      levelMap p f n (transition p n x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

@[simp] theorem levelMap_id (p : R) (n : ℕ) (x : Level p M n) :
    levelMap p (LinearMap.id : M →ₗ[R] M) n x = x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

@[simp] theorem levelMap_comp (p : R) (f : M →ₗ[R] N) (g : N →ₗ[R] K)
    (n : ℕ) (x : Level p M n) :
    levelMap p (g.comp f) n x = levelMap p g n (levelMap p f n x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

@[simp] theorem levelMap_add (p : R) (f g : M →ₗ[R] N)
    (n : ℕ) (x : Level p M n) :
    levelMap p (f + g) n x = levelMap p f n x + levelMap p g n x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

@[simp] theorem levelMap_zero (p : R) (n : ℕ) (x : Level p M n) :
    levelMap p (0 : M →ₗ[R] N) n x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

/-- Compatible sequences of actual quotient classes, a submodule of their
product.  No separatedness or completeness premise is imposed on `M`. -/
def compatible (p : R) : Submodule R (∀ n : ℕ, Level p M n) where
  carrier := {x | ∀ n, transition p n (x (n + 1)) = x n}
  zero_mem' := by intro n; simp
  add_mem' := by
    intro x y hx hy n
    change transition p n (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  smul_mem' := by
    intro r x hx n
    change transition p n (r • x (n + 1)) = r • x n
    rw [map_smul, hx n]

abbrev Completion (p : R) (M : Type*) [AddCommGroup M] [Module R M] :=
  compatible (M := M) p

@[ext] theorem completion_ext (p : R) {x y : Completion p M}
    (h : ∀ n, x.val n = y.val n) : x = y :=
  Subtype.ext (funext h)

theorem transitionLE_value (p : R) (x : Completion p M) (m n : ℕ) (h : m ≤ n) :
    transitionLE p m n h (x.val n) = x.val m := by
  induction n, h using Nat.le_induction with
  | base =>
    induction x.val m using Submodule.Quotient.induction_on with
    | _ y => rfl
  | succ n h ih =>
    rw [transitionLE_succ p m n h, x.property n, ih]

def completeMap (p : R) (f : M →ₗ[R] N) : Completion p M →ₗ[R] Completion p N where
  toFun x := ⟨fun n => levelMap p f n (x.val n), fun n => by
    rw [levelMap_transition, x.property n]⟩
  map_add' x y := by ext n; exact map_add (levelMap p f n) _ _
  map_smul' r x := by ext n; exact map_smul (levelMap p f n) r _

@[simp] theorem completeMap_apply (p : R) (f : M →ₗ[R] N)
    (x : Completion p M) (n : ℕ) :
    (completeMap p f x).val n = levelMap p f n (x.val n) := rfl

@[simp] theorem completeMap_id (p : R) (x : Completion p M) :
    completeMap p (LinearMap.id : M →ₗ[R] M) x = x := by
  ext n; exact levelMap_id p n (x.val n)

@[simp] theorem completeMap_comp (p : R) (f : M →ₗ[R] N) (g : N →ₗ[R] K)
    (x : Completion p M) :
    completeMap p (g.comp f) x = completeMap p g (completeMap p f x) := by
  ext n; exact levelMap_comp p f g n (x.val n)

@[simp] theorem completeMap_add (p : R) (f g : M →ₗ[R] N) (x : Completion p M) :
    completeMap p (f + g) x = completeMap p f x + completeMap p g x := by
  ext n; exact levelMap_add p f g n (x.val n)

@[simp] theorem completeMap_zero (p : R) (x : Completion p M) :
    completeMap p (0 : M →ₗ[R] N) x = 0 := by
  ext n; exact levelMap_zero p n (x.val n)

/-- The canonical map need not be injective: its kernel is the intersection
of all `p^n M`. -/
def ofModule (p : R) : M →ₗ[R] Completion p M where
  toFun x := ⟨fun n => levelMk p n x, fun n => transition_mk p n x⟩
  map_add' x y := by ext n; exact map_add (levelMk p n) x y
  map_smul' r x := by ext n; exact map_smul (levelMk p n) r x

@[simp] theorem ofModule_apply (p : R) (x : M) (n : ℕ) :
    (ofModule p x).val n = levelMk p n x := rfl

@[simp] theorem completeMap_ofModule (p : R) (f : M →ₗ[R] N) (x : M) :
    completeMap p f (ofModule p x) = ofModule p (f x) := by
  ext n; rfl

theorem ofModule_eq_zero_iff (p : R) (x : M) :
    ofModule p x = 0 ↔ ∀ n, x ∈ powerSubmodule p n := by
  constructor
  · intro h n
    have hn := congrArg (fun z : Completion p M => z.val n) h
    change (Submodule.Quotient.mk x : Level p M n) = Submodule.Quotient.mk 0 at hn
    simpa using (Submodule.Quotient.eq (powerSubmodule (M := M) p n)).mp hn
  · intro h
    ext n
    change (Submodule.Quotient.mk x : Level p M n) = Submodule.Quotient.mk 0
    exact (Submodule.Quotient.eq (powerSubmodule (M := M) p n)).mpr (by simpa using h n)

def completeEquiv (p : R) (e : M ≃ₗ[R] N) : Completion p M ≃ₗ[R] Completion p N where
  __ := completeMap p e.toLinearMap
  invFun := completeMap p e.symm.toLinearMap
  left_inv x := by
    change completeMap p e.symm.toLinearMap (completeMap p e.toLinearMap x) = x
    rw [← completeMap_comp]
    have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      ext x; exact e.symm_apply_apply x
    rw [h, completeMap_id]
  right_inv x := by
    change completeMap p e.toLinearMap (completeMap p e.symm.toLinearMap x) = x
    rw [← completeMap_comp]
    have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      ext x; exact e.apply_symm_apply x
    rw [h, completeMap_id]

@[simp] theorem completeEquiv_apply (p : R) (e : M ≃ₗ[R] N) (x : Completion p M) :
    completeEquiv p e x = completeMap p e.toLinearMap x := rfl

@[simp] theorem completeEquiv_symm_apply (p : R) (e : M ≃ₗ[R] N)
    (x : Completion p N) :
    (completeEquiv p e).symm x = completeMap p e.symm.toLinearMap x := rfl

def completeProdEquiv (p : R) :
    Completion p (M × N) ≃ₗ[R] Completion p M × Completion p N where
  toFun x := (completeMap p (LinearMap.fst R M N) x,
    completeMap p (LinearMap.snd R M N) x)
  invFun x := completeMap p (LinearMap.inl R M N) x.1 +
    completeMap p (LinearMap.inr R M N) x.2
  map_add' x y := by simp
  map_smul' r x := by simp
  left_inv x := by
    change completeMap p (LinearMap.inl R M N) (completeMap p (LinearMap.fst R M N) x) +
      completeMap p (LinearMap.inr R M N) (completeMap p (LinearMap.snd R M N) x) = x
    rw [← completeMap_comp, ← completeMap_comp, ← completeMap_add]
    have h : (LinearMap.inl R M N).comp (LinearMap.fst R M N) +
        (LinearMap.inr R M N).comp (LinearMap.snd R M N) = LinearMap.id := by
      ext x <;> simp [LinearMap.inl, LinearMap.inr]
    rw [h, completeMap_id]
  right_inv x := by
    change (completeMap p (LinearMap.fst R M N)
      (completeMap p (LinearMap.inl R M N) x.1 + completeMap p (LinearMap.inr R M N) x.2),
      completeMap p (LinearMap.snd R M N)
      (completeMap p (LinearMap.inl R M N) x.1 + completeMap p (LinearMap.inr R M N) x.2)) = x
    apply Prod.ext <;> simp [← completeMap_comp]

@[simp] theorem completeProdEquiv_apply (p : R) (x : Completion p (M × N)) :
    completeProdEquiv p x =
      (completeMap p (LinearMap.fst R M N) x,
        completeMap p (LinearMap.snd R M N) x) := rfl

@[simp] theorem completeProdEquiv_symm_apply (p : R)
    (x : Completion p M × Completion p N) :
    (completeProdEquiv p).symm x =
      completeMap p (LinearMap.inl R M N) x.1 +
        completeMap p (LinearMap.inr R M N) x.2 := rfl

/-- The completed actual splitting.  Its only input beyond scalar/module
structures is the already proved equivalence `e`. -/
def completedSplit (p : R) (e : M ≃ₗ[R] N × K) :
    Completion p M ≃ₗ[R] Completion p N × Completion p K :=
  (completeEquiv p e).trans (completeProdEquiv p)

def coordinates (p : R) (e : M ≃ₗ[R] N × K) :
    Completion p M →ₗ[R] Completion p K :=
  (LinearMap.snd R _ _).comp (completedSplit p e).toLinearMap

def exactInclusion (p : R) (e : M ≃ₗ[R] N × K) :
    Completion p N →ₗ[R] Completion p M :=
  (completedSplit p e).symm.toLinearMap.comp (LinearMap.inl R _ _)

def coordinateSection (p : R) (e : M ≃ₗ[R] N × K) :
    Completion p K →ₗ[R] Completion p M :=
  (completedSplit p e).symm.toLinearMap.comp (LinearMap.inr R _ _)

@[simp] theorem coordinates_section (p : R) (e : M ≃ₗ[R] N × K)
    (x : Completion p K) : coordinates p e (coordinateSection p e x) = x := by
  simp [coordinates, coordinateSection]

@[simp] theorem coordinates_exactInclusion (p : R) (e : M ≃ₗ[R] N × K)
    (x : Completion p N) : coordinates p e (exactInclusion p e x) = 0 := by
  simp [coordinates, exactInclusion]

theorem coordinates_surjective (p : R) (e : M ≃ₗ[R] N × K) :
    Function.Surjective (coordinates p e) :=
  fun x => ⟨coordinateSection p e x, coordinates_section p e x⟩

theorem exactInclusion_injective (p : R) (e : M ≃ₗ[R] N × K) :
    Function.Injective (exactInclusion p e) := by
  intro x y h
  have h' := congrArg (completedSplit p e) h
  simpa [exactInclusion] using congrArg Prod.fst h'

theorem coordinates_kernel (p : R) (e : M ≃ₗ[R] N × K) :
    LinearMap.ker (coordinates p e) = LinearMap.range (exactInclusion p e) := by
  ext x
  constructor
  · intro hx
    change coordinates p e x = 0 at hx
    refine ⟨(completedSplit p e x).1, ?_⟩
    apply (completedSplit p e).injective
    simp only [exactInclusion, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    exact Prod.ext rfl hx.symm
  · rintro ⟨y, rfl⟩
    exact coordinates_exactInclusion p e y

/-- Algebraic quotient by the completed exact summand, with the induced
coordinate map as forward map and the displayed section as inverse. -/
def completedQuotientEquiv (p : R) (e : M ≃ₗ[R] N × K) :
    (Completion p M ⧸ LinearMap.range (exactInclusion p e)) ≃ₗ[R] Completion p K where
  __ := (LinearMap.range (exactInclusion p e)).liftQ (coordinates p e)
    (coordinates_kernel p e).symm.le
  invFun x := (LinearMap.range (exactInclusion p e)).mkQ (coordinateSection p e x)
  left_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      apply (Submodule.Quotient.eq (LinearMap.range (exactInclusion p e))).mpr
      change coordinateSection p e (coordinates p e x) - x ∈
        LinearMap.range (exactInclusion p e)
      have hk : coordinateSection p e (coordinates p e x) - x ∈
          LinearMap.ker (coordinates p e) := by
        change coordinates p e (coordinateSection p e (coordinates p e x) - x) = 0
        rw [map_sub, coordinates_section, sub_self]
      exact (coordinates_kernel p e) ▸ hk
  right_inv x := coordinates_section p e x

@[simp] theorem completedQuotientEquiv_mk (p : R) (e : M ≃ₗ[R] N × K)
    (x : Completion p M) :
    completedQuotientEquiv p e (Submodule.Quotient.mk x) = coordinates p e x := rfl

/-- Each functor map is continuous for the inverse-limit topology. -/
theorem continuous_completeMap (p : R) (f : M →ₗ[R] N) :
    Continuous (completeMap p f) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := levelMap p f n)).comp
    ((continuous_apply n).comp continuous_subtype_val)

theorem continuous_completeEquiv (p : R) (e : M ≃ₗ[R] N) :
    Continuous (completeEquiv p e) := continuous_completeMap p e.toLinearMap

theorem continuous_completeProdEquiv (p : R) :
    Continuous (completeProdEquiv (M := M) (N := N) p) :=
  (continuous_completeMap p (LinearMap.fst R M N)).prodMk
    (continuous_completeMap p (LinearMap.snd R M N))

theorem continuous_completedSplit (p : R) (e : M ≃ₗ[R] N × K) :
    Continuous (completedSplit p e) :=
  (continuous_completeProdEquiv p).comp (continuous_completeEquiv p e)

theorem continuous_coordinates (p : R) (e : M ≃ₗ[R] N × K) :
    Continuous (coordinates p e) :=
  continuous_snd.comp (continuous_completedSplit p e)

/-- Representatives of the higher quotient levels agree at every lower
level; therefore the actual module is dense in its compatible inverse limit. -/
theorem denseRange_ofModule (p : R) : DenseRange (ofModule (M := M) p) := by
  classical
  intro x
  have hs : ∀ n, ∃ m : M, levelMk p n m = x.val n :=
    fun n => (powerSubmodule p n).mkQ_surjective (x.val n)
  choose representative hrepresentative using hs
  have hlim : Filter.Tendsto (fun n => ofModule p (representative n))
      Filter.atTop (nhds x) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro k
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.Ici_mem_atTop k] with n hn
    have hmatch : levelMk p k (representative n) = x.val k := by
      calc
        levelMk p k (representative n) =
          transitionLE p k n hn (levelMk p n (representative n)) := rfl
        _ = transitionLE p k n hn (x.val n) :=
          congrArg (transitionLE (M := M) p k n hn) (hrepresentative n)
        _ = x.val k := transitionLE_value p x k n hn
    exact hmatch.symm
  exact mem_closure_of_tendsto hlim (Filter.Eventually.of_forall
    (fun n => Set.mem_range_self (representative n)))

/-- The actual map of the exact summand before completion. -/
def moduleExactInclusion (e : M ≃ₗ[R] N × K) : N →ₗ[R] M :=
  e.symm.toLinearMap.comp (LinearMap.inl R N K)

theorem exactInclusion_eq_completeMap (p : R) (e : M ≃ₗ[R] N × K) :
    exactInclusion p e = completeMap p (moduleExactInclusion e) := by
  apply LinearMap.ext
  intro x
  change completeMap p e.symm.toLinearMap
    (completeMap p (LinearMap.inl R N K) x + completeMap p (LinearMap.inr R N K) 0) = _
  rw [map_zero, add_zero, ← completeMap_comp]
  rfl

theorem continuous_exactInclusion (p : R) (e : M ≃ₗ[R] N × K) :
    Continuous (exactInclusion p e) := by
  rw [exactInclusion_eq_completeMap]
  exact continuous_completeMap p (moduleExactInclusion e)

def moduleCoordinateSection (e : M ≃ₗ[R] N × K) : K →ₗ[R] M :=
  e.symm.toLinearMap.comp (LinearMap.inr R N K)

theorem coordinateSection_eq_completeMap (p : R) (e : M ≃ₗ[R] N × K) :
    coordinateSection p e = completeMap p (moduleCoordinateSection e) := by
  apply LinearMap.ext
  intro x
  change completeMap p e.symm.toLinearMap
    (completeMap p (LinearMap.inl R N K) 0 + completeMap p (LinearMap.inr R N K) x) = _
  rw [map_zero, zero_add, ← completeMap_comp]
  rfl

theorem continuous_coordinateSection (p : R) (e : M ≃ₗ[R] N × K) :
    Continuous (coordinateSection p e) := by
  rw [coordinateSection_eq_completeMap]
  exact continuous_completeMap p (moduleCoordinateSection e)

/-- The coordinate map is a continuous quotient map, with a continuous
linear section, for the genuine inverse-limit topologies. -/
theorem isQuotientMap_coordinates (p : R) (e : M ≃ₗ[R] N × K) :
    Topology.IsQuotientMap (coordinates p e) :=
  Topology.IsQuotientMap.of_inverse (continuous_coordinateSection p e)
    (continuous_coordinates p e) (coordinates_section p e)

theorem isClosed_range_exactInclusion (p : R) (e : M ≃ₗ[R] N × K) :
    IsClosed (Set.range (exactInclusion p e)) := by
  have h : Set.range (exactInclusion p e) =
      (coordinates p e) ⁻¹' ({0} : Set (Completion p K)) := by
    ext x
    change x ∈ LinearMap.range (exactInclusion p e) ↔ coordinates p e x = 0
    rw [← coordinates_kernel]
    rfl
  rw [h]
  exact isClosed_singleton.preimage (continuous_coordinates p e)

/-- The closure of the *actual, uncompleted* exact summand is precisely
the completed exact summand.  No arbitrary completed primitive is used. -/
theorem closure_actual_exact (p : R) (e : M ≃ₗ[R] N × K) :
    closure (Set.range ((ofModule p).comp (moduleExactInclusion e))) =
      Set.range (exactInclusion p e) := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ (isClosed_range_exactInclusion p e)
    rintro x ⟨y, rfl⟩
    refine ⟨ofModule p y, ?_⟩
    rw [exactInclusion_eq_completeMap, completeMap_ofModule]
    rfl
  · rintro x ⟨y, rfl⟩
    have hy : y ∈ closure (Set.range (ofModule (M := N) p)) := denseRange_ofModule p y
    have h := image_closure_subset_closure_image (continuous_exactInclusion p e)
      (s := Set.range (ofModule (M := N) p)) ⟨y, hy, rfl⟩
    have hset : (exactInclusion p e) '' Set.range (ofModule (M := N) p) =
        Set.range ((ofModule p).comp (moduleExactInclusion e)) := by
      ext z
      constructor
      · rintro ⟨a, ha, haz⟩
        rcases ha with ⟨b, hb⟩
        refine ⟨b, ?_⟩
        calc
          (ofModule p).comp (moduleExactInclusion e) b =
            exactInclusion p e (ofModule p b) := by
              rw [exactInclusion_eq_completeMap, completeMap_ofModule]; rfl
          _ = exactInclusion p e a := congrArg (exactInclusion p e) hb
          _ = z := haz
      · rintro ⟨b, hb⟩
        refine ⟨ofModule p b, ⟨b, rfl⟩, ?_⟩
        calc
          exactInclusion p e (ofModule p b) =
            (ofModule p).comp (moduleExactInclusion e) b := by
              rw [exactInclusion_eq_completeMap, completeMap_ofModule]; rfl
          _ = z := hb
    rw [hset] at h
    exact h

/-- Extending a linear map adds no new closed image: its completed image
has exactly the closure of its actual, uncompleted image. -/
theorem closure_completeMap_range (p : R) (f : M →ₗ[R] N) :
    closure (Set.range (completeMap p f)) =
      closure (Set.range ((ofModule p).comp f)) := by
  have hset : (completeMap p f) '' Set.range (ofModule (M := M) p) =
      Set.range ((ofModule p).comp f) := by
    ext z
    constructor
    · rintro ⟨a, ha, haz⟩
      rcases ha with ⟨b, hb⟩
      refine ⟨b, ?_⟩
      calc
        (ofModule p).comp f b = completeMap p f (ofModule p b) :=
          (completeMap_ofModule p f b).symm
        _ = completeMap p f a := congrArg (completeMap p f) hb
        _ = z := haz
    · rintro ⟨b, hb⟩
      exact ⟨ofModule p b, ⟨b, rfl⟩, (completeMap_ofModule p f b).trans hb⟩
  apply Set.Subset.antisymm
  · apply closure_minimal _ isClosed_closure
    rintro z ⟨x, rfl⟩
    have h := image_closure_subset_closure_image (continuous_completeMap p f)
      (s := Set.range (ofModule (M := M) p)) ⟨x, denseRange_ofModule p x, rfl⟩
    rw [hset] at h
    exact h
  · apply closure_mono
    rintro z ⟨x, rfl⟩
    exact ⟨ofModule p x, completeMap_ofModule p f x⟩

/-- Apply this to the actual finite aggregate of the logarithmic
derivations, after proving that its range is the actual exact summand.
The theorem is an image-closure statement, not a license to use primitives
from a larger module. -/
theorem closure_completedMap_of_range_eq
    {P : Type*} [AddCommGroup P] [Module R P]
    (p : R) (e : M ≃ₗ[R] N × K) (d : P →ₗ[R] M)
    (hd : LinearMap.range d = LinearMap.range (moduleExactInclusion e)) :
    closure (Set.range (completeMap p d)) = Set.range (exactInclusion p e) := by
  rw [closure_completeMap_range]
  have hr : LinearMap.range ((ofModule p).comp d) =
      LinearMap.range ((ofModule p).comp (moduleExactInclusion e)) := by
    rw [LinearMap.range_comp, LinearMap.range_comp, hd]
  change closure (LinearMap.range ((ofModule p).comp d) : Set (Completion p M)) = _
  rw [hr]
  exact closure_actual_exact p e

section FiniteCoordinates

variable {ι : Type*}

theorem mem_powerSubmodule_pi (p : R) (n : ℕ) (x : ι → M) :
    x ∈ powerSubmodule p n ↔ ∀ i, x i ∈ powerSubmodule p n := by
  classical
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, rfl⟩
  · intro h
    choose y hy using h
    exact ⟨y, funext hy⟩

def levelPiMap (p : R) (n : ℕ) :
    Level p (ι → M) n →ₗ[R] (ι → Level p M n) :=
  LinearMap.pi (fun i => levelMap p (LinearMap.proj i) n)

@[simp] theorem levelPiMap_mk (p : R) (n : ℕ) (x : ι → M) (i : ι) :
    levelPiMap p n (levelMk p n x) i = levelMk p n (x i) := rfl

theorem levelPiMap_injective (p : R) (n : ℕ) :
    Function.Injective (levelPiMap (M := M) (ι := ι) p n) := by
  intro x y h
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      apply (Submodule.Quotient.eq (powerSubmodule (M := ι → M) p n)).mpr
      apply (mem_powerSubmodule_pi p n (x - y)).mpr
      intro i
      have hi := congrArg (fun z => z i) h
      exact (Submodule.Quotient.eq (powerSubmodule (M := M) p n)).mp hi

theorem levelPiMap_surjective (p : R) (n : ℕ) :
    Function.Surjective (levelPiMap (M := M) (ι := ι) p n) := by
  classical
  intro x
  have hs : ∀ i, ∃ m : M, levelMk p n m = x i :=
    fun i => (powerSubmodule (M := M) p n).mkQ_surjective (x i)
  choose representative hrepresentative using hs
  exact ⟨levelMk p n representative, funext hrepresentative⟩

noncomputable def levelPiEquiv (p : R) (n : ℕ) :
    Level p (ι → M) n ≃ₗ[R] (ι → Level p M n) :=
  LinearEquiv.ofBijective (levelPiMap p n)
    ⟨levelPiMap_injective p n, levelPiMap_surjective p n⟩

def completePiMap (p : R) : Completion p (ι → M) →ₗ[R] (ι → Completion p M) :=
  LinearMap.pi (fun i => completeMap p (LinearMap.proj i))

theorem completePiMap_injective (p : R) :
    Function.Injective (completePiMap (M := M) (ι := ι) p) := by
  intro x y h
  apply completion_ext
  intro n
  apply levelPiMap_injective p n
  funext i
  exact congrArg (fun z => (z i).val n) h

theorem completePiMap_surjective (p : R) :
    Function.Surjective (completePiMap (M := M) (ι := ι) p) := by
  classical
  intro x
  let v : ∀ n, Level p (ι → M) n :=
    fun n => (levelPiEquiv p n).symm (fun i => (x i).val n)
  have hv : ∀ n i, levelMap p (LinearMap.proj i) n (v n) = (x i).val n := by
    intro n i
    exact congrArg (fun z => z i)
      ((levelPiEquiv (M := M) (ι := ι) p n).apply_symm_apply (fun i => (x i).val n))
  have hcompat : ∀ n, transition p n (v (n + 1)) = v n := by
    intro n
    apply levelPiMap_injective p n
    funext i
    change levelMap p (LinearMap.proj i) n (transition p n (v (n + 1))) =
      levelMap p (LinearMap.proj i) n (v n)
    rw [← levelMap_transition, hv, hv]
    exact (x i).property n
  refine ⟨⟨v, hcompat⟩, ?_⟩
  funext i
  apply completion_ext
  intro n
  exact hv n i

/-- Finite free module coordinates may be read as a finite family of scalar
completions.  The algebraic statement also holds for arbitrary index types. -/
noncomputable def completePiEquiv (p : R) :
    Completion p (ι → M) ≃ₗ[R] (ι → Completion p M) :=
  LinearEquiv.ofBijective (completePiMap p)
    ⟨completePiMap_injective p, completePiMap_surjective p⟩

theorem continuous_completePiEquiv (p : R) :
    Continuous (completePiEquiv (M := M) (ι := ι) p) := by
  apply continuous_pi
  intro i
  exact continuous_completeMap p (LinearMap.proj i : (ι → M) →ₗ[R] M)

theorem completePiEquiv_symm_val (p : R) (x : ι → Completion p M) (n : ℕ) :
    ((completePiEquiv p).symm x).val n =
      (levelPiEquiv p n).symm (fun i => (x i).val n) := by
  apply (levelPiEquiv p n).injective
  rw [LinearEquiv.apply_symm_apply]
  funext i
  exact congrArg (fun z => (z i).val n)
    ((completePiEquiv p).apply_symm_apply x)

theorem continuous_completePiEquiv_symm [Finite ι] (p : R) :
    Continuous (completePiEquiv (M := M) (ι := ι) p).symm := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  have h : Continuous (fun x : ι → Completion p M => fun i => (x i).val n) := by
    apply continuous_pi
    intro i
    exact ((continuous_apply n).comp continuous_subtype_val).comp (continuous_apply i)
  have h' := (continuous_of_discreteTopology (f := (levelPiEquiv (M := M) p n).symm)).comp h
  convert h' using 1
  funext x
  exact completePiEquiv_symm_val p x n

end FiniteCoordinates

def elevenSplit : (Fin 11 → R) ≃ₗ[R] (Fin 5 → R) × (Fin 6 → R) where
  toFun x := (fun i => x ⟨i.val, by omega⟩, fun i => x ⟨5 + i.val, by omega⟩)
  invFun x := fun i => if h : i.val < 5 then x.1 ⟨i.val, h⟩
    else x.2 ⟨i.val - 5, by omega⟩
  left_inv x := by
    funext i
    dsimp
    split_ifs with h
    · rfl
    · apply congrArg x
      apply Fin.ext
      dsimp
      omega
  right_inv x := by
    apply Prod.ext
    · funext i
      dsimp
      rw [dif_pos i.isLt]
    · funext i
      dsimp
      rw [dif_neg (by omega)]
      apply congrArg x.2
      apply Fin.ext
      dsimp
      omega
  map_add' x y := rfl
  map_smul' r x := rfl

/-- The completed eleven coordinates split into five interior and six
boundary directions, using the original finite coordinate positions. -/
def completedElevenSplit (p : R) :
    Completion p (Fin 11 → R) ≃ₗ[R]
      Completion p (Fin 5 → R) × Completion p (Fin 6 → R) :=
  completedSplit p elevenSplit

def interiorCoordinateInclusion (p : R) :
    Completion p (Fin 5 → R) →ₗ[R] Completion p (Fin 11 → R) :=
  exactInclusion p elevenSplit

def boundaryCoordinates (p : R) :
    Completion p (Fin 11 → R) →ₗ[R] Completion p (Fin 6 → R) :=
  coordinates p elevenSplit

theorem interiorCoordinateInclusion_injective (p : R) :
    Function.Injective (interiorCoordinateInclusion p) :=
  exactInclusion_injective p elevenSplit

theorem boundaryCoordinates_kernel (p : R) :
    LinearMap.ker (boundaryCoordinates p) =
      LinearMap.range (interiorCoordinateInclusion p) :=
  coordinates_kernel p elevenSplit

theorem interior_coordinates_closed (p : R) :
    IsClosed (Set.range (interiorCoordinateInclusion p)) :=
  isClosed_range_exactInclusion p elevenSplit

/-- The five-coordinate lift into the completed closed module.  Identifying
this range with the completion of the actual interior module is a separate
instantiation theorem owned by the actual-module construction. -/
def interiorSection (p : R) (e : M ≃ₗ[R] N × (Fin 11 → R)) :
    Completion p (Fin 5 → R) →ₗ[R] Completion p M :=
  (coordinateSection p e).comp (interiorCoordinateInclusion p)

@[simp] theorem coordinates_interiorSection (p : R)
    (e : M ≃ₗ[R] N × (Fin 11 → R)) (x : Completion p (Fin 5 → R)) :
    coordinates p e (interiorSection p e x) = interiorCoordinateInclusion p x := by
  exact coordinates_section p e (interiorCoordinateInclusion p x)

theorem interiorSection_injective (p : R) (e : M ≃ₗ[R] N × (Fin 11 → R)) :
    Function.Injective (interiorSection p e) := by
  intro x y h
  apply interiorCoordinateInclusion_injective p
  simpa only [coordinates_interiorSection] using congrArg (coordinates p e) h

theorem interiorSection_coordinate_range (p : R)
    (e : M ≃ₗ[R] N × (Fin 11 → R)) :
    (LinearMap.range (interiorSection p e)).map (coordinates p e) =
      LinearMap.range (interiorCoordinateInclusion p) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, (coordinates_interiorSection p e z).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨interiorSection p e y, ⟨y, rfl⟩, coordinates_interiorSection p e y⟩

/-- Literal eleven scalar coordinates in the scalar inverse limit. -/
noncomputable def scalarCoordinates (p : R) (e : M ≃ₗ[R] N × (Fin 11 → R)) :
    Completion p M →ₗ[R] (Fin 11 → Completion p R) :=
  (completePiEquiv p).toLinearMap.comp (coordinates p e)

noncomputable def scalarCoordinateSection (p : R) (e : M ≃ₗ[R] N × (Fin 11 → R)) :
    (Fin 11 → Completion p R) →ₗ[R] Completion p M :=
  (coordinateSection p e).comp (completePiEquiv p).symm.toLinearMap

@[simp] theorem scalarCoordinates_section (p : R)
    (e : M ≃ₗ[R] N × (Fin 11 → R)) (x : Fin 11 → Completion p R) :
    scalarCoordinates p e (scalarCoordinateSection p e x) = x := by
  simp [scalarCoordinates, scalarCoordinateSection]

theorem scalarCoordinates_kernel (p : R) (e : M ≃ₗ[R] N × (Fin 11 → R)) :
    LinearMap.ker (scalarCoordinates p e) = LinearMap.range (exactInclusion p e) := by
  rw [← coordinates_kernel]
  ext x
  change completePiEquiv p (coordinates p e x) = 0 ↔ coordinates p e x = 0
  exact (completePiEquiv p).map_eq_zero_iff

theorem continuous_scalarCoordinates (p : R) (e : M ≃ₗ[R] N × (Fin 11 → R)) :
    Continuous (scalarCoordinates p e) :=
  (continuous_completePiEquiv p).comp (continuous_coordinates p e)

theorem continuous_scalarCoordinateSection (p : R) (e : M ≃ₗ[R] N × (Fin 11 → R)) :
    Continuous (scalarCoordinateSection p e) :=
  (continuous_coordinateSection p e).comp (continuous_completePiEquiv_symm p)

theorem isQuotientMap_scalarCoordinates (p : R) (e : M ≃ₗ[R] N × (Fin 11 → R)) :
    Topology.IsQuotientMap (scalarCoordinates p e) :=
  Topology.IsQuotientMap.of_inverse (continuous_scalarCoordinateSection p e)
    (continuous_scalarCoordinates p e) (scalarCoordinates_section p e)

noncomputable def completedElevenQuotientEquiv (p : R)
    (e : M ≃ₗ[R] N × (Fin 11 → R)) :
    (Completion p M ⧸ LinearMap.range (exactInclusion p e)) ≃ₗ[R]
      (Fin 11 → Completion p R) :=
  (completedQuotientEquiv p e).trans (completePiEquiv p)

theorem interior_high_coordinates_zero (p : R)
    (x : Completion p (Fin 5 → R)) (i : Fin 11) (hi : 5 ≤ i.val) :
    completePiEquiv p (interiorCoordinateInclusion p x) i = 0 := by
  have hmap : (LinearMap.proj i).comp (moduleExactInclusion (R := R) elevenSplit) = 0 := by
    apply LinearMap.ext
    intro y
    change (if h : i.val < 5 then y ⟨i.val, h⟩ else 0) = 0
    rw [dif_neg (by omega)]
  change completeMap p (LinearMap.proj i) (exactInclusion p elevenSplit x) = 0
  rw [exactInclusion_eq_completeMap, ← completeMap_comp, hmap, completeMap_zero]

theorem scalarCoordinates_interior_high_zero (p : R)
    (e : M ≃ₗ[R] N × (Fin 11 → R)) (x : Completion p (Fin 5 → R))
    (i : Fin 11) (hi : 5 ≤ i.val) : scalarCoordinates p e (interiorSection p e x) i = 0 := by
  change completePiEquiv p (coordinates p e (interiorSection p e x)) i = 0
  rw [coordinates_interiorSection]
  exact interior_high_coordinates_zero p x i hi

end WPResidueQuotient.Adic
