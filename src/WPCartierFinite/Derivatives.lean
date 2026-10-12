import WPCartierFinite.Selector

namespace WPCartierFinite
noncomputable section

def latticeDerivativeOf (w : Exponents →+ ℤ) : LaurentPolynomial →ₗ[ℚ] LaurentPolynomial where
  toFun P := AddMonoidAlgebra.ofCoeff (Finsupp.onFinset P.coeff.support
    (fun x => (w x : ℚ) * P.coeff x)
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

@[simp] theorem latticeDerivativeOf_coeff (w : Exponents →+ ℤ)
    (P : LaurentPolynomial) (x : Exponents) :
    (latticeDerivativeOf w P).coeff x = (w x : ℚ) * P.coeff x := rfl

@[simp] theorem latticeDerivativeOf_single (w : Exponents →+ ℤ)
    (x : Exponents) (c : ℚ) :
    latticeDerivativeOf w (AddMonoidAlgebra.single x c) =
      AddMonoidAlgebra.single x ((w x : ℚ) * c) := by
  classical
  apply AddMonoidAlgebra.coeff_injective
  ext y
  simp only [latticeDerivativeOf_coeff, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with h
  · subst y; rfl
  · simp

theorem latticeDerivativeOf_mul_single (w : Exponents →+ ℤ) (P : LaurentPolynomial)
    (x : Exponents) (c : ℚ) :
    latticeDerivativeOf w (P * AddMonoidAlgebra.single x c) =
      latticeDerivativeOf w P * AddMonoidAlgebra.single x c +
        P * latticeDerivativeOf w (AddMonoidAlgebra.single x c) := by
  apply AddMonoidAlgebra.coeff_injective
  ext y
  simp
  ring

theorem latticeDerivativeOf_mul (w : Exponents →+ ℤ) (P H : LaurentPolynomial) :
    latticeDerivativeOf w (P * H) = latticeDerivativeOf w P * H + P * latticeDerivativeOf w H := by
  induction H using AddMonoidAlgebra.induction_on with
  | of x => simpa using latticeDerivativeOf_mul_single w P x 1
  | add H K hH hK => simp [mul_add, hH, hK]; abel
  | smul c H hH => simp [hH, smul_add]

@[simp] theorem exponentScale_eq_nsmul (p : ℕ) (x : Exponents) : exponentScale p x = p • x := by
  ext i
  simp

theorem kappa_latticeDerivativeOf (p : ℕ) (hp : 0 < p) (w : Exponents →+ ℤ)
    (P : LaurentPolynomial) :
    kappa p hp (latticeDerivativeOf w P) =
      (p : ℚ) • latticeDerivativeOf w (kappa p hp P) := by
  apply AddMonoidAlgebra.coeff_injective
  ext x
  change (w (exponentScale p x) : ℚ) * P.coeff (exponentScale p x) =
    (p : ℚ) * ((w x : ℚ) * P.coeff (exponentScale p x))
  have hw : w (exponentScale p x) = (p : ℤ) * w x := by
    rw [exponentScale_eq_nsmul, w.map_nsmul]
    simp
  rw [hw, Int.cast_mul, Int.cast_natCast, mul_assoc]

def coordinateWeight (i : Fin 5) : Exponents →+ ℤ where
  toFun x := x i
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coordinate_derivative_agrees (i : Fin 5) :
    latticeDerivativeOf (coordinateWeight i) = latticeDerivative i := by
  ext P x
  rfl

end
end WPCartierFinite
