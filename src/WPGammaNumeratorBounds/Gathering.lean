import WPGammaIntegralLift
import WPReview.ResidueNumeratorOperators

noncomputable section

namespace WPGammaNumeratorBounds

open WPGammaIntegralLift WPIntegralBlocks

variable (p : ℕ) [Fact p.Prime]

def progression (b d : ℤ) : ℕ → End p := factor p (b : S p) (d : S p)

theorem integer_scalar_commute (b : ℤ) :
    Commute (gammaNabla p) (scalarAction p (b : S p)) := by
  apply LinearMap.ext
  intro v
  change gammaNabla p ((b : S p) • v) = (b : S p) • gammaNabla p v
  simpa only [Int.cast_smul_eq_zsmul] using map_zsmul (gammaNabla p) b v

theorem scalar_commute (a b : S p) : Commute (scalarAction p a) (scalarAction p b) := by
  apply LinearMap.ext
  intro v
  funext i
  change a * (b * v i) = b * (a * v i)
  ring

theorem progression_commute (a d b e : ℤ) (i j : ℕ) :
    Commute (progression p a d i) (progression p b e j) := by
  have hi : progression p a d i = gammaNabla p + scalarAction p ((a+d*i : ℤ) : S p) := by
    simp [progression, factor]
  have hj : progression p b e j = gammaNabla p + scalarAction p ((b+e*j : ℤ) : S p) := by
    simp [progression, factor]
  rw [hi, hj]
  exact Commute.add_left
    (Commute.add_right (Commute.refl _) (integer_scalar_commute p _))
    (Commute.add_right (integer_scalar_commute p _).symm (scalar_commute p _ _))

theorem ordered_commute {A B : ℕ → End p} (h : ∀ i j, Commute (A i) (B j))
    (s m t n : ℕ) : Commute (ordered A s m) (ordered B t n) := by
  induction m generalizing s with
  | zero => simp [ordered]
  | succ m ih =>
    rw [ordered]
    apply Commute.mul_left
    · clear ih
      induction n generalizing t with
      | zero => simp [ordered]
      | succ n ihn =>
        rw [ordered]
        exact Commute.mul_right (h s t) (ihn (t+1))
    · exact ih (s+1)

theorem progression_ordered_commute (a d b e : ℤ) (s m t n : ℕ) :
    Commute (ordered (progression p a d) s m) (ordered (progression p b e) t n) :=
  ordered_commute p (progression_commute p a d b e) s m t n

theorem divisible_mono (m n : ℕ) (A : End p) (hmn : m ≤ n)
    (hA : Divisible p n A) : Divisible p m A := by
  intro v
  obtain ⟨w, hw⟩ := hA v
  refine ⟨(p : ℤ)^(n-m) • w, ?_⟩
  rw [hw, smul_smul, ← pow_add, Nat.add_sub_of_le hmn]

theorem list_blocks_divisible (hp7 : 7 ≤ p) (l : List (End p))
    (hl : ∀ A ∈ l, ∀ v, reduceVector p (A v) =
      WPGammaURegular.gammaPsi p (reduceVector p v)) : Divisible p (l.length/5) l.prod := by
  have hpsi : ((WPGammaURegular.gammaPsi p).restrictScalars ℤ)^5 = 0 := by
    apply LinearMap.ext
    intro v
    change ((WPGammaURegular.gammaNabla p ^ p - WPGammaURegular.gammaNabla p)^5) v = 0
    rw [WPGammaURegular.actual_regular_u_fifth_zero p hp7]
    rfl
  generalize hn : l.length = n
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
    cases l with
    | nil => simp only [List.length_nil] at hn; subst n; simpa using divisible_zero p (1 : End p)
    | cons A l =>
      cases l with
      | nil => simp only [List.length_cons, List.length_nil] at hn; subst n; simpa using divisible_zero p A
      | cons B l =>
        cases l with
        | nil => simp only [List.length_cons, List.length_nil] at hn; subst n; simpa using divisible_zero p (A*B)
        | cons C l =>
          cases l with
          | nil => simp only [List.length_cons, List.length_nil] at hn; subst n; simpa [mul_assoc] using divisible_zero p (A*B*C)
          | cons D l =>
            cases l with
            | nil => simp only [List.length_cons, List.length_nil] at hn; subst n; simpa [mul_assoc] using divisible_zero p (A*B*C*D)
            | cons E l =>
              have hA := hl A (by simp)
              have hB := hl B (by simp)
              have hC := hl C (by simp)
              have hD := hl D (by simp)
              have hE := hl E (by simp)
              have hfull : Divisible p 1 (A*B*C*D*E) := by
                apply divisible_one_of_reduction_zero p (reduceVector p) (reduceVector_kernel p)
                intro v
                simp only [Module.End.mul_apply, hA, hB, hC, hD, hE]
                have he := congrArg (fun F : Module.End ℤ (WPGammaURegular.RegularSpace p) =>
                  F (reduceVector p v)) hpsi
                simpa [pow_succ', Module.End.mul_apply] using he
              have ht : Divisible p (l.length/5) l.prod := by
                apply ih l.length (by simp at hn; omega) l
                · intro F hF
                  exact hl F (by simp [hF])
                · rfl
              have he := divisible_mul p 1 (l.length/5) (A*B*C*D*E) l.prod hfull ht
              rw [← hn]
              have hq : (l.length+1+1+1+1+1)/5 = 1+l.length/5 := by omega
              simpa only [List.length_cons, List.prod_cons, hq, mul_assoc] using he

structure Progression where
  shift : ℤ
  step : ℤ
  start : ℕ
  length : ℕ

def product (r : Progression) : End p := ordered (progression p r.shift r.step) r.start r.length

def completeBlocks (r : Progression) : ℕ → ℕ → List (End p)
  | _, 0 => []
  | s, q+1 => primeBlock p (r.shift : ℤ_[p]) (r.step : ℤ_[p]) s :: completeBlocks r (s+p) q

theorem completeBlocks_length (r : Progression) (s q : ℕ) :
    (completeBlocks p r s q).length = q := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih => simp [completeBlocks, ih]

theorem completeBlocks_prod (r : Progression) (s q : ℕ) :
    (completeBlocks p r s q).prod = ordered (progression p r.shift r.step) s (p*q) := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih =>
    have he : p*(q+1)=p+p*q := by ring
    rw [he, ordered_add]
    simp [completeBlocks, primeBlock, progression, ih]

theorem completeBlocks_reduce (r : Progression)
    (hd : coefficientReduce p (r.step : ℤ_[p]) ≠ 0) (s q : ℕ) :
    ∀ A ∈ completeBlocks p r s q, ∀ v,
      reduceVector p (A v) = WPGammaURegular.gammaPsi p (reduceVector p v) := by
  induction q generalizing s with
  | zero => simp [completeBlocks]
  | succ q ih =>
    intro A hA
    simp only [completeBlocks, List.mem_cons] at hA
    rcases hA with rfl | hA
    · exact primeBlock_intertwines p _ _ hd s
    · exact ih (s+p) A hA

def full (r : Progression) : End p :=
  ordered (progression p r.shift r.step) r.start (p*(r.length/p))

def remainder (r : Progression) : End p :=
  ordered (progression p r.shift r.step) (r.start+p*(r.length/p)) (r.length%p)

theorem split_product (r : Progression) : product p r = full p r * remainder p r := by
  have he : p*(r.length/p)+r.length%p=r.length := by
    simpa [Nat.add_comm, Nat.mul_comm] using Nat.mod_add_div r.length p
  unfold product full remainder
  conv_lhs => rw [← he]
  exact ordered_add _ _ _ _

theorem remainder_full_commute (r : Progression) (l : List Progression) :
    Commute (remainder p r) (l.map (full p)).prod := by
  induction l with
  | nil => simp
  | cons s l ih =>
    rw [List.map_cons, List.prod_cons]
    exact Commute.mul_right (progression_ordered_commute p _ _ _ _ _ _ _ _) ih

/-- Every remainder is retained after the complete blocks are gathered. -/
theorem gather (l : List Progression) :
    (l.map (product p)).prod = (l.map (full p)).prod * (l.map (remainder p)).prod := by
  induction l with
  | nil => simp
  | cons r l ih =>
    simp only [List.map_cons, List.prod_cons, split_product, ih]
    have hc := (remainder_full_commute p r l).eq
    calc
      (full p r * remainder p r) * ((l.map (full p)).prod * (l.map (remainder p)).prod) =
        full p r * (remainder p r * (l.map (full p)).prod) * (l.map (remainder p)).prod := by simp [mul_assoc]
      _ = _ := by rw [hc]; simp [mul_assoc]

theorem progressions_divisible (hp7 : 7 ≤ p) (l : List Progression)
    (hd : ∀ r ∈ l, coefficientReduce p (r.step : ℤ_[p]) ≠ 0) :
    Divisible p ((l.map (fun r => r.length/p)).sum/5) (l.map (product p)).prod := by
  have hb := list_blocks_divisible p hp7
    (l.flatMap fun r => completeBlocks p r r.start (r.length/p)) (by
      intro A hA
      obtain ⟨r, hr, hA⟩ := List.mem_flatMap.mp hA
      exact completeBlocks_reduce p r (hd r hr) _ _ A hA)
  have hp : (l.flatMap fun r => completeBlocks p r r.start (r.length/p)).prod =
      (l.map (full p)).prod := by
    clear hd hb
    induction l with
    | nil => rfl
    | cons r l ih => simp [List.flatMap_cons, completeBlocks_prod, full, ih]
  have hl : (l.flatMap fun r => completeBlocks p r r.start (r.length/p)).length =
      (l.map (fun r => r.length/p)).sum := by
    clear hd hb hp
    induction l with
    | nil => rfl
    | cons r l ih => simp [List.flatMap_cons, completeBlocks_length, ih]
  rw [hp, hl] at hb
  rw [gather]
  simpa using divisible_mul p _ 0 _ _ hb (divisible_zero p _)

end WPGammaNumeratorBounds
