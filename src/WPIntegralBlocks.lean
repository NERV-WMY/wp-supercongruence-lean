import WPToricCBlocks

noncomputable section

namespace WPIntegralBlocks

variable {M : Type*} [AddCommGroup M]

def Divisible (p n : ℕ) (A : Module.End ℤ M) : Prop :=
  ∀ v, ∃ w, A v = (p : ℤ)^n • w

theorem divisible_zero (p : ℕ) (A : Module.End ℤ M) : Divisible p 0 A := by
  intro v
  exact ⟨A v, by simp⟩

theorem divisible_mul (p m n : ℕ) (A B : Module.End ℤ M)
    (hA : Divisible p m A) (hB : Divisible p n B) :
    Divisible p (m+n) (A*B) := by
  intro v
  obtain ⟨b, hb⟩ := hB v
  obtain ⟨a, ha⟩ := hA b
  refine ⟨a, ?_⟩
  rw [Module.End.mul_apply, hb, map_zsmul, ha, smul_smul, pow_add]
  congr 1
  exact mul_comm _ _

def ordered (ops : ℕ → Module.End ℤ M) (s : ℕ) : ℕ → Module.End ℤ M
  | 0 => 1
  | n+1 => ops s * ordered ops (s+1) n

theorem ordered_add (ops : ℕ → Module.End ℤ M) (s m n : ℕ) :
    ordered ops s (m+n) = ordered ops s m * ordered ops (s+m) n := by
  induction m generalizing s with
  | zero => simp [ordered]
  | succ m ih =>
    simpa [ordered, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, mul_assoc]
      using congrArg (fun A => ops s * A) (ih (s+1))

theorem ordered_multiples_divisible (p h : ℕ) (ops : ℕ → Module.End ℤ M)
    (hblock : ∀ s, Divisible p 1 (ordered ops s h)) (q s : ℕ) :
    Divisible p q (ordered ops s (h*q)) := by
  induction q generalizing s with
  | zero =>
    simpa using divisible_zero p (ordered ops s 0)
  | succ q ih =>
    have he : h*(q+1)=h+h*q := by rw [Nat.mul_succ, Nat.add_comm]
    rw [he, ordered_add]
    simpa [Nat.add_comm] using
      divisible_mul p 1 q (ordered ops s h) (ordered ops (s+h) (h*q))
        (hblock s) (ih (s+h))

theorem ordered_divisible (p h : ℕ) (ops : ℕ → Module.End ℤ M)
    (hblock : ∀ s, Divisible p 1 (ordered ops s h)) (s n : ℕ) :
    Divisible p (n/h) (ordered ops s n) := by
  have hn : h*(n/h)+n%h=n := by
    simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div n h
  have hop : ordered ops s n =
      ordered ops s (h*(n/h)) * ordered ops (s+h*(n/h)) (n%h) := by
    conv_lhs => rw [← hn]
    rw [ordered_add]
  rw [hop]
  simpa using divisible_mul p (n/h) 0
    (ordered ops s (h*(n/h))) (ordered ops (s+h*(n/h)) (n%h))
    (ordered_multiples_divisible p h ops hblock (n/h) s)
    (divisible_zero p _)

variable {B : Type*} [AddCommGroup B]

theorem divisible_one_of_reduction_zero (p : ℕ) (reduce : M →ₗ[ℤ] B)
    (hker : ∀ v, reduce v=0 ↔ ∃ w, v=(p : ℤ) • w)
    (A : Module.End ℤ M) (hA : ∀ v, reduce (A v)=0) : Divisible p 1 A := by
  intro v
  obtain ⟨w, hw⟩ := (hker (A v)).mp (hA v)
  exact ⟨w, by simpa using hw⟩

theorem ordered_reduction (ops : ℕ → Module.End ℤ M)
    (barOps : ℕ → Module.End ℤ B) (reduce : M →ₗ[ℤ] B)
    (hreduce : ∀ j v, reduce (ops j v)=barOps j (reduce v)) (s n : ℕ) (v : M) :
    reduce (ordered ops s n v)=ordered barOps s n (reduce v) := by
  induction n generalizing s v with
  | zero => rfl
  | succ n ih =>
    change reduce (ops s (ordered ops (s+1) n v)) =
      barOps s (ordered barOps (s+1) n (reduce v))
    rw [hreduce, ih]

theorem ordered_divisible_of_reduction (p h : ℕ)
    (ops : ℕ → Module.End ℤ M) (barOps : ℕ → Module.End ℤ B)
    (reduce : M →ₗ[ℤ] B)
    (hker : ∀ v, reduce v=0 ↔ ∃ w, v=(p : ℤ) • w)
    (hreduce : ∀ j v, reduce (ops j v)=barOps j (reduce v))
    (hzero : ∀ s, ordered barOps s h=0) (s n : ℕ) :
    Divisible p (n/h) (ordered ops s n) := by
  apply ordered_divisible p h ops
  intro t
  apply divisible_one_of_reduction_zero p reduce hker
  intro v
  rw [ordered_reduction ops barOps reduce hreduce, hzero]
  rfl

theorem ordered_same (A : Module.End ℤ B) (s n : ℕ) :
    ordered (fun _ => A) s n=A^n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [ordered, ih, pow_succ']

theorem blocks_divisible_of_nilpotent_reduction (p h : ℕ)
    (ops : ℕ → Module.End ℤ M) (psi : Module.End ℤ B)
    (reduce : M →ₗ[ℤ] B)
    (hker : ∀ v, reduce v=0 ↔ ∃ w, v=(p : ℤ) • w)
    (hreduce : ∀ j v, reduce (ops j v)=psi (reduce v))
    (hpsi : psi^h=0) (s n : ℕ) :
    Divisible p (n/h) (ordered ops s n) := by
  apply ordered_divisible_of_reduction p h ops (fun _ => psi) reduce hker hreduce
  intro t
  rw [ordered_same, hpsi]

def toricFactor (p : ℕ) [Fact p.Prime] (a d : ZMod p) (j : ℕ) :
    WPToricCRegular.RegularEnd p := WPToricCRegular.gammaNabla p +
      algebraMap (ZMod p) (WPToricCRegular.RegularEnd p) (a+d*(j : ZMod p))

def toricOps (p : ℕ) [Fact p.Prime] (a d : ZMod p) (j : ℕ) :
    Module.End ℤ (WPToricCRegular.RegularSpace p) :=
  (toricFactor p a d j).restrictScalars ℤ

theorem toric_ordered_eq (p : ℕ) [Fact p.Prime] (a d : ZMod p) (s n : ℕ) :
    ordered (toricOps p a d) s n =
      (WPToricCBlocks.operatorProduct p (a+d*(s : ZMod p)) d n).restrictScalars ℤ := by
  induction n generalizing s with
  | zero =>
    apply LinearMap.ext
    intro v
    simp [ordered, WPToricCBlocks.operatorProduct]
  | succ n ih =>
    have hadd := WPToricCBlocks.operatorProduct_add p (a+d*(s : ZMod p)) d 1 n
    have hadd' : WPToricCBlocks.operatorProduct p (a+d*(s : ZMod p)) d (n+1) =
        WPToricCBlocks.operatorProduct p (a+d*(s : ZMod p)) d 1 *
        WPToricCBlocks.operatorProduct p (a+d*(s : ZMod p)+d) d n := by
      simpa [Nat.add_comm] using hadd
    have hs : a+d*(s+1 : ℕ)=a+d*(s : ZMod p)+d := by push_cast; ring
    have hone : WPToricCBlocks.operatorProduct p (a+d*(s : ZMod p)) d 1 =
        toricFactor p a d s := by
      simp [WPToricCBlocks.operatorProduct, toricFactor]
    apply LinearMap.ext
    intro v
    rw [ordered, Module.End.mul_apply, ih, hs, hadd', hone]
    rfl

theorem toric_three_prime_divisible (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (a d : ZMod p) (hd : d ≠ 0) (ops : ℕ → Module.End ℤ M)
    (reduce : M →ₗ[ℤ] WPToricCRegular.RegularSpace p)
    (hker : ∀ v, reduce v=0 ↔ ∃ w, v=(p : ℤ) • w)
    (hreduce : ∀ j v, reduce (ops j v)=toricFactor p a d j (reduce v))
    (s n : ℕ) : Divisible p (n/(3*p)) (ordered ops s n) := by
  apply ordered_divisible_of_reduction p (3*p) ops (toricOps p a d) reduce hker hreduce
  intro t
  rw [toric_ordered_eq, WPToricCBlocks.operatorProduct_three_prime_zero p hp7 _ d hd]
  rfl

end WPIntegralBlocks
