import WPCartierFinite.Selector
import Mathlib.Algebra.MonoidAlgebra.Degree

namespace WPCartierFinite
noncomputable section
open scoped BigOperators

def canonicalDegree (x : Exponents) : ℕ := ∑ i, canonicalSixNat x i

@[simp] theorem canonicalSixNat_zero : canonicalSixNat 0 = 0 := by
  have hc : canonicalSix 0 = 0 := by
    apply canonicalSix_unique
    · exact canonicalSix_nonnegative _
    · simp
    · exact canonicalSix_has_zero _
    · exact ⟨0, rfl⟩
    · rw [qSix_canonicalSix]; ext i; rfl
  ext i
  simp [canonicalSixNat, hc]

theorem sixMinimum_nonnegative (b : Fin 6 → ℤ) (hb : ∀ i, 0 ≤ b i) :
    0 ≤ sixMinimum b := by
  apply Finset.le_min'
  intro y hy
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
  exact hb i

theorem canonicalSix_scale (p : ℕ) (_hp : 0 < p) (x : Exponents) :
    canonicalSix (exponentScale p x) = fun i => (p : ℤ) * canonicalSix x i := by
  apply canonicalSix_unique
  · exact canonicalSix_nonnegative _
  · intro i
    exact mul_nonneg (Int.natCast_nonneg p) (canonicalSix_nonnegative x i)
  · exact canonicalSix_has_zero _
  · obtain ⟨i, hi⟩ := canonicalSix_has_zero x
    exact ⟨i, by simp [hi]⟩
  · rw [qSix_canonicalSix]
    ext i
    simp only [qSix, exponentScale_apply]
    have hi := congrFun (qSix_canonicalSix x) i
    change canonicalSix x i.castSucc - canonicalSix x (Fin.last 5) = x i at hi
    rw [← mul_sub, hi]

theorem canonicalSixNat_scale (p : ℕ) (hp : 0 < p) (x : Exponents) :
    canonicalSixNat (exponentScale p x) = fun i => p * canonicalSixNat x i := by
  ext i
  apply Int.natCast_inj.mp
  simp [canonicalSix_scale p hp]

theorem canonicalDegree_scale (p : ℕ) (hp : 0 < p) (x : Exponents) :
    canonicalDegree (exponentScale p x) = p * canonicalDegree x := by
  simp [canonicalDegree, canonicalSixNat_scale p hp, Finset.mul_sum]

theorem canonicalDegree_le_ordinary (b : Fin 6 → ℕ) :
    canonicalDegree (qSix (fun i => (b i : ℤ))) ≤ ∑ i, b i := by
  apply Finset.sum_le_sum
  intro i _
  apply Int.ofNat_le.mp
  rw [canonicalSixNat_cast, canonicalSix_qSix]
  dsimp [normalizeSix]
  have := sixMinimum_nonnegative (fun i => (b i : ℤ)) (by intro i; positivity)
  omega

theorem canonicalDegree_add_le (x y : Exponents) :
    canonicalDegree (x + y) ≤ canonicalDegree x + canonicalDegree y := by
  let b : Fin 6 → ℕ := fun i => canonicalSixNat x i + canonicalSixNat y i
  have hq : qSix (fun i => (b i : ℤ)) = x + y := by
    ext i
    have hx := congrFun (qSix_canonicalSixNat x) i
    have hy := congrFun (qSix_canonicalSixNat y) i
    simp only [qSix, canonicalSixNat_cast] at hx hy
    change canonicalSix x i.castSucc - canonicalSix x (Fin.last 5) = x i at hx
    change canonicalSix y i.castSucc - canonicalSix y (Fin.last 5) = y i at hy
    simp only [qSix, b, Nat.cast_add, canonicalSixNat_cast, Pi.add_apply]
    omega
  calc
    canonicalDegree (x + y) = canonicalDegree (qSix (fun i => (b i : ℤ))) := by rw [hq]
    _ ≤ ∑ i, b i := canonicalDegree_le_ordinary b
    _ = canonicalDegree x + canonicalDegree y := by
      simp [b, canonicalDegree, Finset.sum_add_distrib]

def SupportBound (P : LaurentPolynomial) (d : ℕ) : Prop :=
  ∀ x ∈ P.coeff.support, canonicalDegree x ≤ d

theorem supportBound_mono {P : LaurentPolynomial} {d e : ℕ}
    (h : SupportBound P d) (hde : d ≤ e) : SupportBound P e := by
  intro x hx
  exact (h x hx).trans hde

theorem supportBound_zero (d : ℕ) : SupportBound 0 d := by
  simp [SupportBound]

theorem supportBound_one : SupportBound 1 0 := by
  intro x hx
  have hx0 : x = 0 := by simpa [AddMonoidAlgebra.one_def] using hx
  subst x
  simp [canonicalDegree, canonicalSixNat_zero]

theorem supportBound_add {P Q : LaurentPolynomial} {d : ℕ}
    (hP : SupportBound P d) (hQ : SupportBound Q d) : SupportBound (P + Q) d := by
  intro x hx
  rcases Finset.mem_union.mp (Finsupp.support_add hx) with h | h
  · exact hP x h
  · exact hQ x h

theorem supportBound_neg {P : LaurentPolynomial} {d : ℕ}
    (hP : SupportBound P d) : SupportBound (-P) d := by
  intro x hx
  exact hP x (by simpa using hx)

theorem supportBound_sub {P Q : LaurentPolynomial} {d : ℕ}
    (hP : SupportBound P d) (hQ : SupportBound Q d) : SupportBound (P - Q) d := by
  simpa [sub_eq_add_neg] using supportBound_add hP (supportBound_neg hQ)

theorem supportBound_smul {P : LaurentPolynomial} {d : ℕ} (c : ℚ)
    (hP : SupportBound P d) : SupportBound (c • P) d := by
  intro x hx
  exact hP x (Finsupp.support_smul hx)

theorem supportBound_mul {P Q : LaurentPolynomial} {d e : ℕ}
    (hP : SupportBound P d) (hQ : SupportBound Q e) : SupportBound (P * Q) (d + e) := by
  intro x hx
  calc
    canonicalDegree x ≤ (P * Q).coeff.support.sup canonicalDegree := Finset.le_sup hx
    _ ≤ P.coeff.support.sup canonicalDegree + Q.coeff.support.sup canonicalDegree :=
      AddMonoidAlgebra.sup_support_coeff_mul_le canonicalDegree_add_le P Q
    _ ≤ d + e := Nat.add_le_add (Finset.sup_le hP) (Finset.sup_le hQ)

theorem supportBound_pow {P : LaurentPolynomial} {d : ℕ} (hP : SupportBound P d) (n : ℕ) :
    SupportBound (P ^ n) (n * d) := by
  induction n with
  | zero => simpa using supportBound_one
  | succ n hn => simpa [pow_succ, Nat.succ_mul] using supportBound_mul hn hP

@[simp] theorem phi_coeff (p : ℕ) (P : LaurentPolynomial) :
    (phi p P).coeff = P.coeff.mapDomain (exponentScale p) := rfl

theorem supportBound_phi (p : ℕ) (hp : 0 < p) {P : LaurentPolynomial} {d : ℕ}
    (hP : SupportBound P d) : SupportBound (phi p P) (p * d) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hx)
  rw [canonicalDegree_scale p hp]
  exact Nat.mul_le_mul_left p (hP y hy)

theorem kappa_support_closed (p : ℕ) (hp : 0 < p) (P : LaurentPolynomial) (d : ℕ)
    (hP : SupportBound P (p * d)) : SupportBound (kappa p hp P) d := by
  intro x hx
  have hsel : exponentScale p x ∈ P.coeff.support := by
    simpa [Finsupp.mem_support_iff] using hx
  have hbound := hP _ hsel
  rw [canonicalDegree_scale p hp] at hbound
  exact Nat.le_of_mul_le_mul_left hbound hp

theorem kappa_support_strict (p : ℕ) (hp : 0 < p) (P : LaurentPolynomial) (d : ℕ)
    (hP : ∀ x ∈ P.coeff.support, canonicalDegree x < p * d) :
    ∀ x ∈ (kappa p hp P).coeff.support, canonicalDegree x < d := by
  intro x hx
  have hsel : exponentScale p x ∈ P.coeff.support := by
    simpa [Finsupp.mem_support_iff] using hx
  have hbound := hP _ hsel
  rw [canonicalDegree_scale p hp] at hbound
  exact (Nat.mul_lt_mul_left hp).mp hbound

def canonicalCoefficients (P : LaurentPolynomial) : (Fin 6 → ℕ) →₀ ℚ :=
  P.coeff.mapDomain canonicalSixNat

@[simp] theorem canonicalCoefficients_apply (P : LaurentPolynomial) (x : Exponents) :
    canonicalCoefficients P (canonicalSixNat x) = P.coeff x := by
  exact Finsupp.mapDomain_apply canonicalSixNat_injective _ _

@[simp] theorem canonicalCoefficients_zero (P : LaurentPolynomial) :
    canonicalCoefficients P 0 = constantCoefficient P := by
  change canonicalCoefficients P 0 = P.coeff 0
  simpa using canonicalCoefficients_apply P 0

theorem canonicalCoefficients_support_degree (P : LaurentPolynomial) (d : ℕ)
    (hP : SupportBound P d) (a : Fin 6 → ℕ) (ha : a ∈ (canonicalCoefficients P).support) :
    ∑ i, a i ≤ d := by
  classical
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
  exact hP x hx

theorem canonicalCoefficients_support_has_zero (P : LaurentPolynomial) (a : Fin 6 → ℕ)
    (ha : a ∈ (canonicalCoefficients P).support) : ∃ i, a i = 0 := by
  classical
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
  obtain ⟨i, hi⟩ := canonicalSix_has_zero x
  exact ⟨i, by simp [canonicalSixNat, hi]⟩

end
end WPCartierFinite
