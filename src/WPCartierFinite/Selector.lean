import WPCartierFinite.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Max

namespace WPCartierFinite

noncomputable section
open scoped BigOperators

def qSix (b : Fin 6 → ℤ) : Exponents :=
  fun i => b i.castSucc - b (Fin.last 5)

def liftSix (x : Exponents) : Fin 6 → ℤ := Fin.lastCases 0 x

@[simp] theorem liftSix_castSucc (x : Exponents) (i : Fin 5) :
    liftSix x i.castSucc = x i := by simp [liftSix]

@[simp] theorem liftSix_last (x : Exponents) : liftSix x (Fin.last 5) = 0 := by
  rfl

@[simp] theorem qSix_liftSix (x : Exponents) : qSix (liftSix x) = x := by
  ext i
  change liftSix x i.castSucc - liftSix x (Fin.last 5) = x i
  rw [liftSix_castSucc, liftSix_last, sub_zero]

theorem qSix_eq_zero (b : Fin 6 → ℤ) :
    qSix b = 0 ↔ ∀ i, b i = b (Fin.last 5) := by
  constructor
  · intro h i
    refine Fin.lastCases (by rfl) (fun j => ?_) i
    have hj := congrFun h j
    simpa [qSix, sub_eq_zero] using hj
  · intro h
    ext i
    simp [qSix, h]

theorem qSix_eq_iff_diagonal (b c : Fin 6 → ℤ) :
    qSix b = qSix c ↔ ∃ t : ℤ, ∀ i, b i = c i + t := by
  constructor
  · intro h
    refine ⟨b (Fin.last 5) - c (Fin.last 5), fun i => ?_⟩
    refine Fin.lastCases (by ring) (fun j => ?_) i
    have hj := congrFun h j
    change b j.castSucc - b (Fin.last 5) = c j.castSucc - c (Fin.last 5) at hj
    linarith
  · rintro ⟨t, h⟩
    ext i
    simp only [qSix, h]
    ring

def sixMinimum (b : Fin 6 → ℤ) : ℤ :=
  (Finset.univ.image b).min' (by simp)

theorem sixMinimum_le (b : Fin 6 → ℤ) (i : Fin 6) : sixMinimum b ≤ b i := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem sixMinimum_attained (b : Fin 6 → ℤ) : ∃ i, b i = sixMinimum b := by
  have h := Finset.min'_mem (Finset.univ.image b) (by simp)
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  exact ⟨i, hi⟩

def normalizeSix (b : Fin 6 → ℤ) : Fin 6 → ℤ := fun i => b i - sixMinimum b

theorem normalizeSix_nonnegative (b : Fin 6 → ℤ) (i : Fin 6) :
    0 ≤ normalizeSix b i := sub_nonneg.mpr (sixMinimum_le b i)

theorem normalizeSix_has_zero (b : Fin 6 → ℤ) : ∃ i, normalizeSix b i = 0 := by
  obtain ⟨i, hi⟩ := sixMinimum_attained b
  exact ⟨i, by simp [normalizeSix, hi]⟩

@[simp] theorem qSix_normalizeSix (b : Fin 6 → ℤ) :
    qSix (normalizeSix b) = qSix b := by
  ext i
  simp only [qSix, normalizeSix]
  ring

theorem canonicalSix_unique (b c : Fin 6 → ℤ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i)
    (hb0 : ∃ i, b i = 0) (hc0 : ∃ i, c i = 0)
    (h : qSix b = qSix c) : b = c := by
  obtain ⟨t, ht⟩ := (qSix_eq_iff_diagonal b c).mp h
  obtain ⟨i, hi⟩ := hb0
  obtain ⟨j, hj⟩ := hc0
  have hti := ht i
  have htj := ht j
  have hci := hc i
  have hbj := hb j
  have hzero : t = 0 := by omega
  ext k
  simpa [hzero] using ht k

def canonicalSix (x : Exponents) : Fin 6 → ℤ := normalizeSix (liftSix x)

@[simp] theorem qSix_canonicalSix (x : Exponents) : qSix (canonicalSix x) = x := by
  simp [canonicalSix]

theorem canonicalSix_nonnegative (x : Exponents) (i : Fin 6) :
    0 ≤ canonicalSix x i := normalizeSix_nonnegative _ _

theorem canonicalSix_has_zero (x : Exponents) : ∃ i, canonicalSix x i = 0 :=
  normalizeSix_has_zero _

theorem canonicalSix_qSix (b : Fin 6 → ℤ) :
    canonicalSix (qSix b) = normalizeSix b := by
  apply canonicalSix_unique
  · exact canonicalSix_nonnegative _
  · exact normalizeSix_nonnegative _
  · exact canonicalSix_has_zero _
  · exact normalizeSix_has_zero _
  · simp

def canonicalSixNat (x : Exponents) : Fin 6 → ℕ := fun i => (canonicalSix x i).toNat

@[simp] theorem canonicalSixNat_cast (x : Exponents) (i : Fin 6) :
    (canonicalSixNat x i : ℤ) = canonicalSix x i :=
  Int.toNat_of_nonneg (canonicalSix_nonnegative x i)

@[simp] theorem qSix_canonicalSixNat (x : Exponents) :
    qSix (fun i => (canonicalSixNat x i : ℤ)) = x := by simp

theorem canonicalSixNat_injective : Function.Injective canonicalSixNat := by
  intro x y h
  have := congrArg (fun a : Fin 6 → ℕ => qSix (fun i => (a i : ℤ))) h
  simpa using this

def exponentScale (p : ℕ) : Exponents →+ Exponents where
  toFun x i := (p : ℤ) * x i
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp [mul_add]

@[simp] theorem exponentScale_apply (p : ℕ) (x : Exponents) (i : Fin 5) :
    exponentScale p x i = (p : ℤ) * x i := rfl

theorem exponentScale_injective (p : ℕ) (hp : 0 < p) :
    Function.Injective (exponentScale p) := by
  intro x y h
  ext i
  have hi := congrFun h i
  exact mul_left_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hp)) hi

def phi (p : ℕ) : LaurentPolynomial →ₐ[ℚ] LaurentPolynomial :=
  AddMonoidAlgebra.mapDomainAlgHom ℚ ℚ (exponentScale p)

def kappa (p : ℕ) (hp : 0 < p) : LaurentPolynomial →ₗ[ℚ] LaurentPolynomial where
  toFun P := AddMonoidAlgebra.ofCoeff
    (Finsupp.comapDomain (exponentScale p) P.coeff (exponentScale_injective p hp).injOn)
  map_add' P Q := by
    apply AddMonoidAlgebra.coeff_injective
    ext x
    simp [Finsupp.comapDomain_apply]
  map_smul' c P := by
    apply AddMonoidAlgebra.coeff_injective
    ext x
    simp [Finsupp.comapDomain_apply]

@[simp] theorem kappa_coeff (p : ℕ) (hp : 0 < p) (P : LaurentPolynomial) (x : Exponents) :
    (kappa p hp P).coeff x = P.coeff (exponentScale p x) := rfl

@[simp] theorem phi_single (p : ℕ) (x : Exponents) (c : ℚ) :
    phi p (AddMonoidAlgebra.single x c) = AddMonoidAlgebra.single (exponentScale p x) c := by
  simp [phi, AddMonoidAlgebra.mapDomainAlgHom]

@[simp] theorem kappa_scaled_single (p : ℕ) (hp : 0 < p) (x : Exponents) (c : ℚ) :
    kappa p hp (AddMonoidAlgebra.single (exponentScale p x) c) =
      AddMonoidAlgebra.single x c := by
  apply AddMonoidAlgebra.coeff_injective
  exact Finsupp.comapDomain_single _ _ _ _

theorem kappa_single_not_selected (p : ℕ) (hp : 0 < p) (x : Exponents) (c : ℚ)
    (hx : x ∉ Set.range (exponentScale p)) :
    kappa p hp (AddMonoidAlgebra.single x c) = 0 := by
  apply AddMonoidAlgebra.coeff_injective
  exact Finsupp.comapDomain_single_of_not_mem_range hx _ _

theorem kappa_mul_phi_single (p : ℕ) (hp : 0 < p) (P : LaurentPolynomial)
    (x : Exponents) (c : ℚ) :
    kappa p hp (P * phi p (AddMonoidAlgebra.single x c)) =
      kappa p hp P * AddMonoidAlgebra.single x c := by
  apply AddMonoidAlgebra.coeff_injective
  ext y
  simp only [phi_single, kappa_coeff, AddMonoidAlgebra.coeff_mul_single_apply]
  congr 2
  simp

theorem kappa_mul_phi (p : ℕ) (hp : 0 < p) (P H : LaurentPolynomial) :
    kappa p hp (P * phi p H) = kappa p hp P * H := by
  induction H using AddMonoidAlgebra.induction_on with
  | of x => simpa using kappa_mul_phi_single p hp P x 1
  | add H K hH hK => simp [mul_add, hH, hK]
  | smul c H hH => simp [hH]

def constantCoefficient : LaurentPolynomial →ₗ[ℚ] ℚ where
  toFun P := P.coeff 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem constantCoefficient_kappa (p : ℕ) (hp : 0 < p) (P : LaurentPolynomial) :
    constantCoefficient (kappa p hp P) = constantCoefficient P := by
  change (kappa p hp P).coeff 0 = P.coeff 0
  simp

theorem constantCoefficient_six_monomial (b : Fin 6 → ℤ) (c : ℚ) :
    constantCoefficient (AddMonoidAlgebra.single (qSix b) c) =
      if ∀ i, b i = b (Fin.last 5) then c else 0 := by
  classical
  change (AddMonoidAlgebra.single (qSix b) c).coeff 0 = _
  simp [Finsupp.single_apply, qSix_eq_zero]

def latticeDerivative (i : Fin 5) : LaurentPolynomial →ₗ[ℚ] LaurentPolynomial where
  toFun P := AddMonoidAlgebra.ofCoeff (Finsupp.onFinset P.coeff.support
    (fun x => (x i : ℚ) * P.coeff x)
    (by intro x hx; by_contra h; exact hx (by simp [Finsupp.notMem_support_iff.mp h])))
  map_add' P Q := by
    apply AddMonoidAlgebra.coeff_injective
    ext x
    simp [mul_add]
  map_smul' c P := by
    apply AddMonoidAlgebra.coeff_injective
    ext x
    simp [smul_eq_mul]
    ring

@[simp] theorem latticeDerivative_coeff (i : Fin 5) (P : LaurentPolynomial) (x : Exponents) :
    (latticeDerivative i P).coeff x = (x i : ℚ) * P.coeff x := rfl

theorem kappa_latticeDerivative (p : ℕ) (hp : 0 < p) (i : Fin 5) (P : LaurentPolynomial) :
    kappa p hp (latticeDerivative i P) = (p : ℚ) • latticeDerivative i (kappa p hp P) := by
  apply AddMonoidAlgebra.coeff_injective
  ext x
  simp [Int.cast_mul, mul_assoc]

end
end WPCartierFinite
