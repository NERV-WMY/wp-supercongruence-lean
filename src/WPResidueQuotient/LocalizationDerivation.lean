import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Tactic.Ring

namespace WPResidueQuotient

noncomputable section
set_option linter.unusedSectionVars false

section Extension

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

def derivationGraph (D : Derivation R A A) : A →ₐ[R] TrivSqZeroExt B B where
  toFun a := ⟨algebraMap A B a, algebraMap A B (D a)⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by
    ext
    · change algebraMap A B (a + b) = algebraMap A B a + algebraMap A B b
      exact map_add _ _ _
    · change algebraMap A B (D (a + b)) = algebraMap A B (D a) + algebraMap A B (D b)
      simp
  map_mul' a b := by
    ext
    · change algebraMap A B (a * b) = algebraMap A B a * algebraMap A B b
      exact map_mul _ _ _
    · change algebraMap A B (D (a * b)) =
        algebraMap A B a * algebraMap A B (D b) +
          algebraMap A B (D a) * algebraMap A B b
      simp only [D.leibniz, smul_eq_mul, map_add, map_mul]
      ring
  commutes' r := by
    ext
    · change algebraMap A B (algebraMap R A r) = algebraMap R B r
      exact (IsScalarTower.algebraMap_apply R A B r).symm
    · change algebraMap A B (D (algebraMap R A r)) = 0
      simp

@[simp] theorem derivationGraph_fst (D : Derivation R A A) (a : A) :
    (derivationGraph (B := B) D a).fst = algebraMap A B a := rfl

@[simp] theorem derivationGraph_snd (D : Derivation R A A) (a : A) :
    (derivationGraph (B := B) D a).snd = algebraMap A B (D a) := rfl

variable (f : A) [IsLocalization.Away f B]

def localizedGraph (D : Derivation R A A) : B →ₐ[R] TrivSqZeroExt B B :=
  IsLocalization.liftAlgHom (M := Submonoid.powers f) (S := B)
    (f := derivationGraph (B := B) D) (fun s => by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact IsLocalization.map_units B s)

@[simp] theorem localizedGraph_algebraMap (D : Derivation R A A) (a : A) :
    localizedGraph (B := B) f D (algebraMap A B a) = derivationGraph D a := by
  simp [localizedGraph, IsLocalization.liftAlgHom]

theorem localizedGraph_fst (D : Derivation R A A) (b : B) :
    (localizedGraph f D b).fst = b := by
  have h : ((TrivSqZeroExt.fstHom R B B).comp (localizedGraph f D)).toRingHom =
      RingHom.id B := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    simp
  exact DFunLike.congr_fun h b

def extendDerivation (D : Derivation R A A) : Derivation R B B :=
  Derivation.mk'
    (((TrivSqZeroExt.sndHom B B).restrictScalars R).comp
      (localizedGraph f D).toLinearMap) (by
        intro a b
        change (localizedGraph f D (a * b)).snd = _
        rw [map_mul, TrivSqZeroExt.snd_mul, localizedGraph_fst, localizedGraph_fst]
        simp [mul_comm])

@[simp] theorem extendDerivation_algebraMap (D : Derivation R A A) (a : A) :
    extendDerivation f D (algebraMap A B a) = algebraMap A B (D a) := by
  change (localizedGraph f D (algebraMap A B a)).snd = _
  rw [localizedGraph_algebraMap]
  rfl

theorem derivation_invSelf (D : Derivation R B B) :
    D (IsLocalization.Away.invSelf (S := B) f) =
      -(IsLocalization.Away.invSelf (S := B) f)^2 * D (algebraMap A B f) := by
  have hinv := D.leibniz_of_mul_eq_one
    (mul_comm (IsLocalization.Away.invSelf (S := B) f) (algebraMap A B f) ▸
      IsLocalization.Away.mul_invSelf (S := B) f)
  simpa [Algebra.smul_def] using hinv

end Extension

end

end WPResidueQuotient
