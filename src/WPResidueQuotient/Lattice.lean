import WPResidueQuotient.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

/-!
The literal six-exponent lattice modulo simultaneous translation, together
with its unique nonnegative representative having minimum zero. The degree
is the sum of those six entries. All definitions use `Fin` and integers.
-/

namespace WPResidueQuotient

open scoped BigOperators

abbrev SixExponents := Fin 6 → ℤ

/-- The five coordinates of the quotient of the six-exponent lattice. -/
def latticeQ : SixExponents →+ Exponents where
  toFun b i := b i.castSucc - b (Fin.last 5)
  map_zero' := by ext i; simp
  map_add' b c := by
    ext i
    change (b i.castSucc + c i.castSucc) - (b (Fin.last 5) + c (Fin.last 5)) =
      (b i.castSucc - b (Fin.last 5)) + (c i.castSucc - c (Fin.last 5))
    omega

@[simp] theorem latticeQ_apply (b : SixExponents) (i : Fin 5) :
    latticeQ b i = b i.castSucc - b (Fin.last 5) := rfl

/-- A simultaneous integral translation of all six coordinates. -/
def diagonal (c : ℤ) : SixExponents := fun _ => c

@[simp] theorem diagonal_apply (c : ℤ) (i : Fin 6) : diagonal c i = c := rfl

def diagonalHom : ℤ →+ SixExponents where
  toFun := diagonal
  map_zero' := by ext i; rfl
  map_add' c d := by ext i; rfl

@[simp] theorem latticeQ_diagonal (c : ℤ) : latticeQ (diagonal c) = 0 := by
  ext i
  simp [diagonal]

@[simp] theorem latticeQ_add_diagonal (b : SixExponents) (c : ℤ) :
    latticeQ (b + diagonal c) = latticeQ b := by
  rw [map_add, latticeQ_diagonal, add_zero]

/-- The unnormalized section is precisely `(x₀,...,x₄,0)`. -/
def rawRepresentative (x : Exponents) : SixExponents := Fin.lastCases 0 x

@[simp] theorem rawRepresentative_castSucc (x : Exponents) (i : Fin 5) :
    rawRepresentative x i.castSucc = x i := by simp [rawRepresentative]

@[simp] theorem rawRepresentative_last (x : Exponents) :
    rawRepresentative x (Fin.last 5) = 0 := Fin.lastCases_last

@[simp] theorem latticeQ_rawRepresentative (x : Exponents) :
    latticeQ (rawRepresentative x) = x := by
  ext i
  change rawRepresentative x i.castSucc - rawRepresentative x (Fin.last 5) = x i
  rw [rawRepresentative_castSucc, rawRepresentative_last, sub_zero]

theorem latticeQ_surjective : Function.Surjective latticeQ :=
  fun x => ⟨rawRepresentative x, latticeQ_rawRepresentative x⟩

/-- Equality in the five-coordinate lattice is exactly diagonal translation. -/
theorem latticeQ_eq_iff (b c : SixExponents) :
    latticeQ b = latticeQ c ↔ ∃ t : ℤ, b = c + diagonal t := by
  constructor
  · intro h
    refine ⟨b (Fin.last 5) - c (Fin.last 5), ?_⟩
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · change b (Fin.last 5) = c (Fin.last 5) +
        (b (Fin.last 5) - c (Fin.last 5))
      omega
    · have hi := congrFun h i
      change b i.castSucc - b (Fin.last 5) =
        c i.castSucc - c (Fin.last 5) at hi
      change b i.castSucc = c i.castSucc +
        (b (Fin.last 5) - c (Fin.last 5))
      omega
  · rintro ⟨t, rfl⟩
    exact latticeQ_add_diagonal c t

theorem latticeQ_eq_zero_iff (b : SixExponents) :
    latticeQ b = 0 ↔ ∃ t : ℤ, b = diagonal t := by
  simpa using latticeQ_eq_iff b 0

/-- The actual additive-homomorphism kernel is the diagonal subgroup. -/
theorem latticeQ_ker_eq_diagonal : latticeQ.ker = diagonalHom.range := by
  ext b
  change latticeQ b = 0 ↔ ∃ t : ℤ, diagonalHom t = b
  constructor
  · intro h
    obtain ⟨t, ht⟩ := (latticeQ_eq_zero_iff b).1 h
    exact ⟨t, ht.symm⟩
  · rintro ⟨t, ht⟩
    apply (latticeQ_eq_zero_iff b).2
    exact ⟨t, ht.symm⟩

/-- An explicit additive equivalence from the literal diagonal quotient. -/
def diagonalQuotientEquiv : (SixExponents ⧸ diagonalHom.range) ≃+ Exponents :=
  (QuotientAddGroup.quotientAddEquivOfEq latticeQ_ker_eq_diagonal.symm).trans
    (QuotientAddGroup.quotientKerEquivOfRightInverse latticeQ rawRepresentative
      latticeQ_rawRepresentative)

@[simp] theorem diagonalQuotientEquiv_mk (b : SixExponents) :
    diagonalQuotientEquiv (QuotientAddGroup.mk b) = latticeQ b := rfl

/-- The minimum of the actual six integer entries. -/
def minimumEntry (b : SixExponents) : ℤ :=
  Finset.univ.inf' ⟨0, Finset.mem_univ _⟩ b

theorem minimumEntry_le (b : SixExponents) (i : Fin 6) : minimumEntry b ≤ b i :=
  Finset.inf'_le b (Finset.mem_univ i)

theorem le_minimumEntry (b : SixExponents) (c : ℤ) (h : ∀ i, c ≤ b i) :
    c ≤ minimumEntry b := by
  exact (Finset.le_inf'_iff _ b).2 (fun i _ => h i)

theorem minimumEntry_attained (b : SixExponents) : ∃ i, b i = minimumEntry b := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ)
    (⟨0, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin 6)).Nonempty) b
  exact ⟨i, hi.symm⟩

theorem minimumEntry_add_diagonal (b : SixExponents) (c : ℤ) :
    minimumEntry (b + diagonal c) = minimumEntry b + c := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := minimumEntry_attained b
    have h := minimumEntry_le (b + diagonal c) i
    change minimumEntry (b + diagonal c) ≤ b i + c at h
    omega
  · apply le_minimumEntry
    intro i
    change minimumEntry b + c ≤ b i + c
    have h := minimumEntry_le b i
    omega

/-- Canonicalization subtracts the minimum simultaneously from all six entries. -/
def normalizeExponents (b : SixExponents) : SixExponents :=
  fun i => b i - minimumEntry b

@[simp] theorem normalizeExponents_apply (b : SixExponents) (i : Fin 6) :
    normalizeExponents b i = b i - minimumEntry b := rfl

def IsCanonical (b : SixExponents) : Prop := (∀ i, 0 ≤ b i) ∧ ∃ i, b i = 0

theorem normalizeExponents_nonneg (b : SixExponents) (i : Fin 6) :
    0 ≤ normalizeExponents b i := sub_nonneg.mpr (minimumEntry_le b i)

theorem normalizeExponents_has_zero (b : SixExponents) :
    ∃ i, normalizeExponents b i = 0 := by
  obtain ⟨i, hi⟩ := minimumEntry_attained b
  exact ⟨i, by simp [hi]⟩

theorem normalizeExponents_isCanonical (b : SixExponents) :
    IsCanonical (normalizeExponents b) :=
  ⟨normalizeExponents_nonneg b, normalizeExponents_has_zero b⟩

theorem minimumEntry_eq_zero (b : SixExponents) (h : IsCanonical b) :
    minimumEntry b = 0 := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := h.2
    exact hi ▸ minimumEntry_le b i
  · exact le_minimumEntry b 0 h.1

theorem minimumEntry_eq_zero_iff (b : SixExponents) :
    minimumEntry b = 0 ↔ IsCanonical b := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      exact h ▸ minimumEntry_le b i
    · obtain ⟨i, hi⟩ := minimumEntry_attained b
      exact ⟨i, hi.trans h⟩
  · exact minimumEntry_eq_zero b

theorem normalizeExponents_eq_self (b : SixExponents) (h : IsCanonical b) :
    normalizeExponents b = b := by
  ext i
  simp [minimumEntry_eq_zero b h]

theorem normalizeExponents_add_diagonal (b : SixExponents) (c : ℤ) :
    normalizeExponents (b + diagonal c) = normalizeExponents b := by
  ext i
  change b i + c - minimumEntry (b + diagonal c) = b i - minimumEntry b
  rw [minimumEntry_add_diagonal]
  omega

theorem normalizeExponents_as_translation (b : SixExponents) :
    normalizeExponents b = b + diagonal (-minimumEntry b) := by
  ext i
  change b i - minimumEntry b = b i + -minimumEntry b
  omega

@[simp] theorem latticeQ_normalizeExponents (b : SixExponents) :
    latticeQ (normalizeExponents b) = latticeQ b := by
  rw [normalizeExponents_as_translation, latticeQ_add_diagonal]

/-- The canonical representative required by the Laurent-algebra convention. -/
def canonicalRepresentative (x : Exponents) : SixExponents :=
  normalizeExponents (rawRepresentative x)

theorem canonicalRepresentative_formula (x : Exponents) (i : Fin 6) :
    canonicalRepresentative x i = rawRepresentative x i -
      minimumEntry (rawRepresentative x) := rfl

@[simp] theorem canonicalRepresentative_castSucc (x : Exponents) (i : Fin 5) :
    canonicalRepresentative x i.castSucc = x i - minimumEntry (rawRepresentative x) := by
  rw [canonicalRepresentative_formula, rawRepresentative_castSucc]

@[simp] theorem canonicalRepresentative_last (x : Exponents) :
    canonicalRepresentative x (Fin.last 5) = -minimumEntry (rawRepresentative x) := by
  rw [canonicalRepresentative_formula, rawRepresentative_last, zero_sub]

theorem minimumEntry_rawRepresentative_nonpos (x : Exponents) :
    minimumEntry (rawRepresentative x) ≤ 0 := by
  simpa only [rawRepresentative_last] using
    minimumEntry_le (rawRepresentative x) (Fin.last 5)

theorem canonicalRepresentative_isCanonical (x : Exponents) :
    IsCanonical (canonicalRepresentative x) :=
  normalizeExponents_isCanonical (rawRepresentative x)

theorem canonicalRepresentative_nonneg (x : Exponents) (i : Fin 6) :
    0 ≤ canonicalRepresentative x i := (canonicalRepresentative_isCanonical x).1 i

theorem canonicalRepresentative_minimum_zero (x : Exponents) :
    minimumEntry (canonicalRepresentative x) = 0 :=
  minimumEntry_eq_zero _ (canonicalRepresentative_isCanonical x)

@[simp] theorem latticeQ_canonicalRepresentative (x : Exponents) :
    latticeQ (canonicalRepresentative x) = x := by
  simp [canonicalRepresentative]

theorem canonicalRepresentative_latticeQ (b : SixExponents) :
    canonicalRepresentative (latticeQ b) = normalizeExponents b := by
  obtain ⟨t, ht⟩ := (latticeQ_eq_iff b (rawRepresentative (latticeQ b))).1
    (latticeQ_rawRepresentative (latticeQ b)).symm
  have hn := congrArg normalizeExponents ht
  rw [normalizeExponents_add_diagonal] at hn
  exact hn.symm

/-- Nonnegativity and minimum zero remove every diagonal ambiguity. -/
theorem canonicalRepresentative_unique (x : Exponents) (b : SixExponents)
    (hb : IsCanonical b) (hq : latticeQ b = x) : b = canonicalRepresentative x := by
  calc
    b = normalizeExponents b := (normalizeExponents_eq_self b hb).symm
    _ = canonicalRepresentative (latticeQ b) := (canonicalRepresentative_latticeQ b).symm
    _ = canonicalRepresentative x := congrArg canonicalRepresentative hq

theorem canonical_unique (b c : SixExponents) (hb : IsCanonical b)
    (hc : IsCanonical c) (hq : latticeQ b = latticeQ c) : b = c := by
  exact (canonicalRepresentative_unique (latticeQ c) b hb hq).trans
    (canonicalRepresentative_unique (latticeQ c) c hc rfl).symm

@[simp] theorem canonicalRepresentative_zero : canonicalRepresentative 0 = 0 := by
  apply (canonicalRepresentative_unique 0 0 ?_ (map_zero latticeQ)).symm
  exact ⟨fun _ => le_rfl, ⟨0, rfl⟩⟩

def totalDegree (b : SixExponents) : ℤ := ∑ i, b i

def canonicalDegree (x : Exponents) : ℤ := totalDegree (canonicalRepresentative x)

def canonicalDegreeNat (x : Exponents) : ℕ := (canonicalDegree x).toNat

@[simp] theorem canonicalDegree_zero : canonicalDegree 0 = 0 := by
  simp [canonicalDegree, totalDegree]

@[simp] theorem canonicalDegreeNat_zero : canonicalDegreeNat 0 = 0 := by
  simp [canonicalDegreeNat]

theorem totalDegree_add (b c : SixExponents) :
    totalDegree (b + c) = totalDegree b + totalDegree c := by
  simp [totalDegree, Finset.sum_add_distrib]

theorem totalDegree_diagonal (c : ℤ) : totalDegree (diagonal c) = 6 * c := by
  simp [totalDegree, diagonal]

theorem totalDegree_add_diagonal (b : SixExponents) (c : ℤ) :
    totalDegree (b + diagonal c) = totalDegree b + 6 * c := by
  rw [totalDegree_add, totalDegree_diagonal]

/-- Canonicalization removes exactly six times the simultaneous minimum. -/
theorem totalDegree_normalizeExponents (b : SixExponents) :
    totalDegree (normalizeExponents b) = totalDegree b - 6 * minimumEntry b := by
  rw [normalizeExponents_as_translation, totalDegree_add_diagonal]
  ring

theorem totalDegree_normalizeExponents_le (b : SixExponents) (h : ∀ i, 0 ≤ b i) :
    totalDegree (normalizeExponents b) ≤ totalDegree b := by
  have hm := le_minimumEntry b 0 h
  rw [totalDegree_normalizeExponents]
  omega

theorem totalDegree_normalizeExponents_lt (b : SixExponents) (h : 0 < minimumEntry b) :
    totalDegree (normalizeExponents b) < totalDegree b := by
  rw [totalDegree_normalizeExponents]
  omega

theorem canonicalDegree_nonneg (x : Exponents) : 0 ≤ canonicalDegree x := by
  unfold canonicalDegree totalDegree
  exact Finset.sum_nonneg (fun i _ => canonicalRepresentative_nonneg x i)

@[simp] theorem canonicalDegreeNat_cast (x : Exponents) :
    (canonicalDegreeNat x : ℤ) = canonicalDegree x :=
  Int.toNat_of_nonneg (canonicalDegree_nonneg x)

theorem canonicalDegreeNat_eq_sum_toNat (x : Exponents) :
    canonicalDegreeNat x = ∑ i : Fin 6, (canonicalRepresentative x i).toNat := by
  have hcast : (canonicalDegreeNat x : ℤ) =
      ((∑ i : Fin 6, (canonicalRepresentative x i).toNat : ℕ) : ℤ) := by
    rw [canonicalDegreeNat_cast]
    simp only [Nat.cast_sum]
    unfold canonicalDegree totalDegree
    apply Finset.sum_congr rfl
    intro i _
    exact (Int.toNat_of_nonneg (canonicalRepresentative_nonneg x i)).symm
  exact_mod_cast hcast

theorem totalDegree_rawRepresentative (x : Exponents) :
    totalDegree (rawRepresentative x) = ∑ i : Fin 5, x i := by
  unfold totalDegree
  rw [Fin.sum_univ_castSucc]
  simp only [rawRepresentative_castSucc, rawRepresentative_last, add_zero]

theorem canonicalDegree_formula (x : Exponents) :
    canonicalDegree x = (∑ i : Fin 5, x i) -
      6 * minimumEntry (rawRepresentative x) := by
  change totalDegree (normalizeExponents (rawRepresentative x)) = _
  rw [totalDegree_normalizeExponents, totalDegree_rawRepresentative]

theorem canonicalDegree_latticeQ (b : SixExponents) :
    canonicalDegree (latticeQ b) = totalDegree b - 6 * minimumEntry b := by
  unfold canonicalDegree
  rw [canonicalRepresentative_latticeQ, totalDegree_normalizeExponents]

@[simp] theorem canonicalDegree_add_diagonal (b : SixExponents) (c : ℤ) :
    canonicalDegree (latticeQ (b + diagonal c)) = canonicalDegree (latticeQ b) := by
  rw [latticeQ_add_diagonal]

/-- The actual standard six exponents, before taking the quotient. -/
def standardExponent (j : Fin 6) : SixExponents := fun i => if i = j then 1 else 0

theorem standardExponent_nonneg (j i : Fin 6) : 0 ≤ standardExponent j i := by
  simp only [standardExponent]
  split_ifs <;> omega

theorem standardExponent_le_one (j i : Fin 6) : standardExponent j i ≤ 1 := by
  simp only [standardExponent]
  split_ifs <;> omega

theorem totalDegree_standardExponent (j : Fin 6) : totalDegree (standardExponent j) = 1 := by
  simp [totalDegree, standardExponent]

theorem latticeQ_standardExponent_castSucc (j : Fin 5) :
    latticeQ (standardExponent j.castSucc) = fun i => if i = j then 1 else 0 := by
  ext i
  change (if i.castSucc = j.castSucc then (1 : ℤ) else 0) -
    (if Fin.last 5 = j.castSucc then 1 else 0) = if i = j then 1 else 0
  rw [if_neg (Ne.symm (Fin.castSucc_ne_last j)), sub_zero]
  simp only [Fin.castSucc_inj]

theorem latticeQ_standardExponent_last :
    latticeQ (standardExponent (Fin.last 5)) = fun _ => -1 := by
  ext i
  change (if i.castSucc = Fin.last 5 then (1 : ℤ) else 0) -
    (if Fin.last 5 = Fin.last 5 then 1 else 0) = -1
  rw [if_neg (Fin.castSucc_ne_last i), if_pos rfl]
  omega

theorem sum_standardExponent : (∑ j : Fin 6, standardExponent j) = diagonal 1 := by
  ext i
  simp [standardExponent, diagonal, Finset.sum_apply]

/-- The additive lattice relation underlying `y₀⋯y₅ = 1`. -/
theorem sum_latticeQ_standardExponent : (∑ j : Fin 6, latticeQ (standardExponent j)) = 0 := by
  calc
    (∑ j : Fin 6, latticeQ (standardExponent j)) =
        latticeQ (∑ j : Fin 6, standardExponent j) := (map_sum latticeQ _ _).symm
    _ = 0 := by rw [sum_standardExponent, latticeQ_diagonal]

theorem minimumEntry_add_standardExponent_lower (b : SixExponents) (j : Fin 6) :
    minimumEntry b ≤ minimumEntry (b + standardExponent j) := by
  apply le_minimumEntry
  intro i
  change minimumEntry b ≤ b i + standardExponent j i
  have h₁ := minimumEntry_le b i
  have h₂ := standardExponent_nonneg j i
  omega

theorem minimumEntry_add_standardExponent_upper (b : SixExponents) (j : Fin 6) :
    minimumEntry (b + standardExponent j) ≤ minimumEntry b + 1 := by
  obtain ⟨i, hi⟩ := minimumEntry_attained b
  have h₁ := minimumEntry_le (b + standardExponent j) i
  change minimumEntry (b + standardExponent j) ≤ b i + standardExponent j i at h₁
  have h₂ := standardExponent_le_one j i
  omega

/-- The exact degree formula for adjoining a single six-coordinate generator. -/
theorem canonicalDegree_add_standardExponent_formula (x : Exponents) (j : Fin 6) :
    canonicalDegree (x + latticeQ (standardExponent j)) = canonicalDegree x + 1 -
      6 * minimumEntry (canonicalRepresentative x + standardExponent j) := by
  have hq : x + latticeQ (standardExponent j) =
      latticeQ (canonicalRepresentative x + standardExponent j) := by
    rw [map_add, latticeQ_canonicalRepresentative]
  rw [hq, canonicalDegree_latticeQ, totalDegree_add, totalDegree_standardExponent]
  rfl

/-- A standard exponent raises the canonical total degree by at most one. -/
theorem canonicalDegree_add_standardExponent_le (x : Exponents) (j : Fin 6) :
    canonicalDegree (x + latticeQ (standardExponent j)) ≤ canonicalDegree x + 1 := by
  have hm := minimumEntry_add_standardExponent_lower (canonicalRepresentative x) j
  rw [canonicalRepresentative_minimum_zero] at hm
  rw [canonicalDegree_add_standardExponent_formula]
  omega

theorem canonicalDegreeNat_add_standardExponent_le (x : Exponents) (j : Fin 6) :
    canonicalDegreeNat (x + latticeQ (standardExponent j)) ≤ canonicalDegreeNat x + 1 := by
  have h := canonicalDegree_add_standardExponent_le x j
  rw [← canonicalDegreeNat_cast (x + latticeQ (standardExponent j)),
    ← canonicalDegreeNat_cast x] at h
  omega

/-- The possible degree changes are exactly `+1` and `-5`. -/
theorem canonicalDegree_add_standardExponent_dichotomy (x : Exponents) (j : Fin 6) :
    canonicalDegree (x + latticeQ (standardExponent j)) = canonicalDegree x + 1 ∨
    canonicalDegree (x + latticeQ (standardExponent j)) = canonicalDegree x - 5 := by
  have hl := minimumEntry_add_standardExponent_lower (canonicalRepresentative x) j
  have hu := minimumEntry_add_standardExponent_upper (canonicalRepresentative x) j
  rw [canonicalRepresentative_minimum_zero] at hl hu
  have he : minimumEntry (canonicalRepresentative x + standardExponent j) = 0 ∨
      minimumEntry (canonicalRepresentative x + standardExponent j) = 1 := by omega
  rw [canonicalDegree_add_standardExponent_formula]
  rcases he with he | he
  · left; rw [he]; omega
  · right; rw [he]; omega

end WPResidueQuotient
