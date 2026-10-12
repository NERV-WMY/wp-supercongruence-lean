import WPResidueQuotient.SplitCompletion
import Mathlib.NumberTheory.Padics.RingHoms

/-!
The explicit compatible scalar inverse limit is identified with the actual
p-adic integers.  The proof uses their proved maximal-ideal adic completeness,
identifies that filtration with the scalar images `p^n Zp`, and checks both
directions against the p-adic topology.  This does not identify the completion
of the unspecialized parameter ring with the parameter ring.
-/

namespace WPResidueQuotient.PadicScalarCompletion

noncomputable section
open scoped Topology

variable (p : ℕ) [Fact p.Prime]

theorem powerSubmodule_eq_span (n : ℕ) :
    Adic.powerSubmodule (M := ℤ_[p]) (p : ℤ_[p]) n =
      (Ideal.span {(p : ℤ_[p]) ^ n} : Submodule ℤ_[p] ℤ_[p]) := by
  ext x
  rw [Adic.mem_powerSubmodule, Ideal.mem_span_singleton]
  simp only [smul_eq_mul]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, hy.symm⟩

theorem powerSubmodule_eq_maximal (n : ℕ) :
    Adic.powerSubmodule (M := ℤ_[p]) (p : ℤ_[p]) n =
      ((IsLocalRing.maximalIdeal ℤ_[p]) ^ n • (⊤ : Submodule ℤ_[p] ℤ_[p])) := by
  simpa only [← Ideal.one_eq_top, smul_eq_mul, mul_one, PadicInt.maximalIdeal_eq_span_p,
    Ideal.span_singleton_pow] using powerSubmodule_eq_span p n

theorem ofModule_injective :
    Function.Injective (Adic.ofModule (M := ℤ_[p]) (p : ℤ_[p])) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply IsHausdorff.haus' (I := IsLocalRing.maximalIdeal ℤ_[p])
  intro n
  have hz : Adic.ofModule (p : ℤ_[p]) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hm := (Adic.ofModule_eq_zero_iff (p : ℤ_[p]) (a - b)).mp hz n
  rw [powerSubmodule_eq_maximal] at hm
  simpa only [SModEq.sub_mem, sub_zero] using hm

theorem ofModule_surjective :
    Function.Surjective (Adic.ofModule (M := ℤ_[p]) (p : ℤ_[p])) := by
  classical
  intro x
  have hs : ∀ n, ∃ a : ℤ_[p], Adic.levelMk (p : ℤ_[p]) n a = x.val n :=
    fun n => (Adic.powerSubmodule (M := ℤ_[p]) (p : ℤ_[p]) n).mkQ_surjective (x.val n)
  choose a ha using hs
  have hcompat : ∀ {m n : ℕ}, m ≤ n → a m ≡ a n
      [SMOD ((IsLocalRing.maximalIdeal ℤ_[p]) ^ m • (⊤ : Submodule ℤ_[p] ℤ_[p]))] := by
    intro m n hmn
    have he : Adic.levelMk (p : ℤ_[p]) m (a m) = Adic.levelMk (p : ℤ_[p]) m (a n) := by
      rw [ha m]
      calc
        x.val m = Adic.transitionLE (p : ℤ_[p]) m n hmn (x.val n) :=
          (Adic.transitionLE_value (p : ℤ_[p]) x m n hmn).symm
        _ = Adic.transitionLE (p : ℤ_[p]) m n hmn
            (Adic.levelMk (p : ℤ_[p]) n (a n)) := congrArg _ (ha n).symm
        _ = Adic.levelMk (p : ℤ_[p]) m (a n) := rfl
    have hm := (Submodule.Quotient.eq
      (Adic.powerSubmodule (M := ℤ_[p]) (p : ℤ_[p]) m)).mp he
    rw [powerSubmodule_eq_maximal] at hm
    exact SModEq.sub_mem.mpr hm
  obtain ⟨L, hL⟩ := IsPrecomplete.prec'
    (I := IsLocalRing.maximalIdeal ℤ_[p]) a hcompat
  refine ⟨L, ?_⟩
  apply Adic.completion_ext
  intro n
  have hm := SModEq.sub_mem.mp (hL n)
  rw [← powerSubmodule_eq_maximal] at hm
  have he := (Submodule.Quotient.eq
    (Adic.powerSubmodule (M := ℤ_[p]) (p : ℤ_[p]) n)).mpr hm
  change Adic.levelMk (p : ℤ_[p]) n L = x.val n
  exact he.symm.trans (ha n)

def scalarEquiv : Adic.Completion (p : ℤ_[p]) ℤ_[p] ≃ₗ[ℤ_[p]] ℤ_[p] :=
  (LinearEquiv.ofBijective (Adic.ofModule (p : ℤ_[p]))
    ⟨ofModule_injective p, ofModule_surjective p⟩).symm

@[simp] theorem scalarEquiv_ofModule (a : ℤ_[p]) :
    scalarEquiv p (Adic.ofModule (p : ℤ_[p]) a) = a :=
  (LinearEquiv.ofBijective (Adic.ofModule (p : ℤ_[p]))
    ⟨ofModule_injective p, ofModule_surjective p⟩).symm_apply_apply a

@[simp] theorem ofModule_scalarEquiv (x : Adic.Completion (p : ℤ_[p]) ℤ_[p]) :
    Adic.ofModule (p : ℤ_[p]) (scalarEquiv p x) = x :=
  (LinearEquiv.ofBijective (Adic.ofModule (p : ℤ_[p]))
    ⟨ofModule_injective p, ofModule_surjective p⟩).apply_symm_apply x

theorem scalarEquiv_level (x : Adic.Completion (p : ℤ_[p]) ℤ_[p]) (n : ℕ) :
    Adic.levelMk (p : ℤ_[p]) n (scalarEquiv p x) = x.val n :=
  congrArg (fun z : Adic.Completion (p : ℤ_[p]) ℤ_[p] => z.val n)
    (ofModule_scalarEquiv p x)

theorem continuous_levelMk (n : ℕ) :
    Continuous (Adic.levelMk (M := ℤ_[p]) (p : ℤ_[p]) n) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  have hpos : 0 < (p : ℝ) ^ (-(n : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  have he : ∀ᶠ b in nhds a,
      Adic.levelMk (p : ℤ_[p]) n b = Adic.levelMk (p : ℤ_[p]) n a := by
    filter_upwards [Metric.ball_mem_nhds a hpos] with b hb
    apply (Submodule.Quotient.eq
      (Adic.powerSubmodule (M := ℤ_[p]) (p : ℤ_[p]) n)).mpr
    rw [powerSubmodule_eq_span]
    apply (PadicInt.norm_le_pow_iff_mem_span_pow (b - a) n).mp
    exact le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hb)
  have he' : ∀ᶠ b in nhds a,
      Adic.levelMk (p : ℤ_[p]) n a = Adic.levelMk (p : ℤ_[p]) n b := by
    filter_upwards [he] with b hb
    exact hb.symm
  exact tendsto_const_nhds.congr' he'

theorem continuous_ofModule :
    Continuous (Adic.ofModule (M := ℤ_[p]) (p : ℤ_[p])) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact continuous_levelMk p n

theorem continuous_scalarEquiv : Continuous (scalarEquiv p) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p hε
  have hc : Continuous (fun y : Adic.Completion (p : ℤ_[p]) ℤ_[p] => y.val n) :=
    (continuous_apply n).comp continuous_subtype_val
  have hv : ∀ᶠ z : Adic.Level (p : ℤ_[p]) ℤ_[p] n in nhds (x.val n), z = x.val n :=
    (isOpen_discrete ({x.val n} : Set (Adic.Level (p : ℤ_[p]) ℤ_[p] n))).mem_nhds
      (Set.mem_singleton (x.val n))
  filter_upwards [hc.continuousAt.eventually hv] with y hy
  have he : Adic.levelMk (p : ℤ_[p]) n (scalarEquiv p y) =
      Adic.levelMk (p : ℤ_[p]) n (scalarEquiv p x) := by
    rw [scalarEquiv_level, scalarEquiv_level, hy]
  have hm := (Submodule.Quotient.eq
    (Adic.powerSubmodule (M := ℤ_[p]) (p : ℤ_[p]) n)).mp he
  rw [powerSubmodule_eq_span] at hm
  have hnorm := (PadicInt.norm_le_pow_iff_mem_span_pow
    (scalarEquiv p y - scalarEquiv p x) n).mpr hm
  exact lt_of_le_of_lt (by simpa only [dist_eq_norm] using hnorm) hn

theorem continuous_scalarEquiv_symm : Continuous (scalarEquiv p).symm :=
  continuous_ofModule p

def scalarHomeomorph : Adic.Completion (p : ℤ_[p]) ℤ_[p] ≃ₜ ℤ_[p] where
  toEquiv := (scalarEquiv p).toEquiv
  continuous_toFun := continuous_scalarEquiv p
  continuous_invFun := continuous_scalarEquiv_symm p

def scalarPiEquiv (ι : Type*) :
    (ι → Adic.Completion (p : ℤ_[p]) ℤ_[p]) ≃ₗ[ℤ_[p]] (ι → ℤ_[p]) :=
  LinearEquiv.piCongrRight (fun _ => scalarEquiv p)

theorem continuous_scalarPiEquiv (ι : Type*) : Continuous (scalarPiEquiv p ι) := by
  apply continuous_pi
  intro i
  exact (continuous_scalarEquiv p).comp (continuous_apply i)

theorem continuous_scalarPiEquiv_symm (ι : Type*) : Continuous (scalarPiEquiv p ι).symm := by
  apply continuous_pi
  intro i
  exact (continuous_scalarEquiv_symm p).comp (continuous_apply i)

def finiteScalarEquiv (n : ℕ) :
    Adic.Completion (p : ℤ_[p]) (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]) :=
  (Adic.completePiEquiv (p : ℤ_[p])).trans (scalarPiEquiv p (Fin n))

@[simp] theorem finiteScalarEquiv_ofModule (n : ℕ) (c : Fin n → ℤ_[p]) :
    finiteScalarEquiv p n (Adic.ofModule (p : ℤ_[p]) c) = c := by
  funext i
  change scalarEquiv p
    (Adic.completeMap (p : ℤ_[p]) (LinearMap.proj i) (Adic.ofModule (p : ℤ_[p]) c)) = c i
  rw [Adic.completeMap_ofModule, scalarEquiv_ofModule]
  rfl

@[simp] theorem ofModule_finiteScalarEquiv (n : ℕ)
    (x : Adic.Completion (p : ℤ_[p]) (Fin n → ℤ_[p])) :
    Adic.ofModule (p : ℤ_[p]) (finiteScalarEquiv p n x) = x := by
  apply (finiteScalarEquiv p n).injective
  rw [finiteScalarEquiv_ofModule]

theorem finiteScalarEquiv_natural (m n : ℕ)
    (f : (Fin m → ℤ_[p]) →ₗ[ℤ_[p]] (Fin n → ℤ_[p]))
    (x : Adic.Completion (p : ℤ_[p]) (Fin m → ℤ_[p])) :
    finiteScalarEquiv p n (Adic.completeMap (p : ℤ_[p]) f x) =
      f (finiteScalarEquiv p m x) := by
  conv_lhs => rw [← ofModule_finiteScalarEquiv p m x]
  rw [Adic.completeMap_ofModule, finiteScalarEquiv_ofModule]

end
end WPResidueQuotient.PadicScalarCompletion
