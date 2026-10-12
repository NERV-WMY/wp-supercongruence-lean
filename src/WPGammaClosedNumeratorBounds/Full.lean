import WPReview.ResidueClosedConnection
import WPGammaIntegralLift
import WPGammaNumeratorBounds
import Mathlib.Algebra.CharP.Lemmas

noncomputable section

namespace WPGammaClosedNumeratorBounds

open WPResidueQuotient

variable (p : ℕ) [Fact p.Prime]

abbrev S := WPGammaIntegralLift.S p
abbrev Space := WPReview.ResidueClosedConnection.Space ℤ_[p]
abbrev End := Module.End ℤ (Space p)
abbrev RegularSpace := WPGammaURegular.RegularSpace p × (Fin 6 → WPGammaURegular.R p)
abbrev RegularEnd := Module.End (ZMod p) (RegularSpace p)

def reduceBoundary : (Fin 6 → S p) →ₗ[ℤ] (Fin 6 → WPGammaURegular.R p) where
  toFun v := fun i => WPGammaIntegralLift.reduce p (v i)
  map_add' _ _ := by funext i; exact map_add _ _ _
  map_smul' _ _ := by funext i; simp

def reduceVector : Space p →ₗ[ℤ] RegularSpace p :=
  (WPGammaIntegralLift.reduceVector p).prodMap (reduceBoundary p)

theorem reduceBoundary_surjective : Function.Surjective (reduceBoundary p) := by
  intro v
  choose w hw using fun i => WPGammaIntegralLift.reduce_surjective p (v i)
  exact ⟨w, funext hw⟩

theorem reduceBoundary_kernel (v : Fin 6 → S p) :
    reduceBoundary p v = 0 ↔ ∃ w, v = (p : ℤ) • w := by
  constructor
  · intro h
    have hi (i : Fin 6) : WPGammaIntegralLift.reduce p (v i) = 0 := congrFun h i
    choose w hw using fun i => (WPGammaIntegralLift.reduce_kernel p (v i)).mp (hi i)
    refine ⟨w, ?_⟩
    funext i
    simpa [Algebra.smul_def] using hw i
  · rintro ⟨w, rfl⟩
    funext i
    change WPGammaIntegralLift.reduce p ((p : ℤ) • w i) = 0
    apply (WPGammaIntegralLift.reduce_kernel p _).mpr
    exact ⟨w i, by simp⟩

theorem reduceVector_surjective : Function.Surjective (reduceVector p) := by
  intro v
  obtain ⟨a, ha⟩ := WPGammaIntegralLift.reduceVector_surjective p v.1
  obtain ⟨b, hb⟩ := reduceBoundary_surjective p v.2
  exact ⟨(a,b), Prod.ext ha hb⟩

theorem reduceVector_kernel (v : Space p) :
    reduceVector p v = 0 ↔ ∃ w, v = (p : ℤ) • w := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (WPGammaIntegralLift.reduceVector_kernel p v.1).mp (congrArg Prod.fst h)
    obtain ⟨b, hb⟩ := (reduceBoundary_kernel p v.2).mp (congrArg Prod.snd h)
    exact ⟨(a,b), Prod.ext ha hb⟩
  · rintro ⟨w, rfl⟩
    exact Prod.ext
      ((WPGammaIntegralLift.reduceVector_kernel p _).mpr ⟨w.1,rfl⟩)
      ((reduceBoundary_kernel p _).mpr ⟨w.2,rfl⟩)

def gammaNabla : End p := (WPReview.ResidueClosedConnection.fullNabla ℤ_[p]).restrictScalars ℤ

def boundaryEuler : Module.End (ZMod p) (Fin 6 → WPGammaURegular.R p) where
  toFun v := fun i => WPGammaURegular.regularTheta p (v i)
  map_add' _ _ := by funext i; exact map_add _ _ _
  map_smul' a v := by funext i; exact (WPGammaURegular.regularTheta p).map_smul a (v i)

def boundaryNabla : Module.End (ZMod p) (Fin 6 → WPGammaURegular.R p) := boundaryEuler p - 1

def regularNabla : RegularEnd p := (WPGammaURegular.gammaNabla p).prodMap (boundaryNabla p)
def regularPsi : RegularEnd p := regularNabla p ^ p - regularNabla p

theorem gammaNabla_intertwines (v : Space p) :
    reduceVector p (gammaNabla p v) = regularNabla p (reduceVector p v) := by
  apply Prod.ext
  · exact WPGammaIntegralLift.gammaNabla_intertwines p v.1
  · funext i
    change WPGammaIntegralLift.reduce p (Parameter.theta (v.2 i)-v.2 i) = _
    rw [map_sub, WPGammaIntegralLift.reduce_theta]
    rfl

theorem boundaryEuler_power (n : ℕ) (v : Fin 6 → WPGammaURegular.R p) (i : Fin 6) :
    (boundaryEuler p ^ n) v i = (WPGammaURegular.regularTheta p)^[n] (v i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply']
    change WPGammaURegular.regularTheta p ((boundaryEuler p^n) v i) = _
    rw [ih]

theorem boundaryEuler_prime : boundaryEuler p ^ p = boundaryEuler p := by
  apply LinearMap.ext
  intro v
  funext i
  rw [boundaryEuler_power, WPGammaURegular.regularTheta_prime]
  rfl

theorem boundaryNabla_prime : boundaryNabla p ^ p = boundaryNabla p := by
  let : CharP (Module.End (ZMod p) (Fin 6 → WPGammaURegular.R p)) p :=
    CharP.of_ringHom_of_ne_zero
      (algebraMap (ZMod p) (Module.End (ZMod p) (Fin 6 → WPGammaURegular.R p))) p
      (Fact.out : p.Prime).ne_zero
  have he := sub_pow_char_of_commute
    (R := Module.End (ZMod p) (Fin 6 → WPGammaURegular.R p)) p
    (Commute.one_right (boundaryEuler p))
  rw [boundaryNabla, he, boundaryEuler_prime, one_pow]

theorem regularNabla_power (n : ℕ) (v : RegularSpace p) :
    (regularNabla p ^ n) v =
      ((WPGammaURegular.gammaNabla p ^ n) v.1, (boundaryNabla p ^ n) v.2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    simp only [pow_succ', Module.End.mul_apply]
    rfl

theorem regularPsi_apply (v : RegularSpace p) :
    regularPsi p v = (WPGammaURegular.gammaPsi p v.1, 0) := by
  change (regularNabla p^p) v - regularNabla p v = _
  rw [regularNabla_power, boundaryNabla_prime]
  apply Prod.ext
  · rfl
  · exact sub_self _

theorem regularPsi_power (n : ℕ) (v : RegularSpace p) :
    (regularPsi p ^ (n+1)) v = ((WPGammaURegular.gammaPsi p ^ (n+1)) v.1, 0) := by
  induction n with
  | zero => simpa only [zero_add, pow_one] using regularPsi_apply p v
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, regularPsi_apply]
    simp only [pow_succ', Module.End.mul_apply]

theorem full_fifth_zero (hp7 : 7 ≤ p) : regularPsi p ^ 5 = 0 := by
  apply LinearMap.ext
  intro v
  have he := regularPsi_power p 4 v
  change (regularPsi p ^ 5) v = ((WPGammaURegular.gammaPsi p ^ 5) v.1,0) at he
  rw [he]
  have hg : WPGammaURegular.gammaPsi p^5=0 := WPGammaURegular.actual_regular_u_fifth_zero p hp7
  rw [hg]
  rfl

def fullSection (hp7 : 7 ≤ p) : Space p →ₗ[S p] WPGammaIntegralLift.Residue p :=
  WPReview.ResidueClosedConnection.fullSection ℤ_[p] (Parameter.padic_six_unit p hp7)

def classReduce (hp7 : 7 ≤ p) : WPGammaIntegralLift.Residue p →ₗ[ℤ] RegularSpace p :=
  (reduceVector p).comp
    ((WPReview.ResidueClosedConnection.integralFullEquiv p hp7).symm.toLinearMap.restrictScalars ℤ)

theorem classReduce_surjective (hp7 : 7 ≤ p) : Function.Surjective (classReduce p hp7) := by
  intro v
  obtain ⟨w, hw⟩ := reduceVector_surjective p v
  refine ⟨WPReview.ResidueClosedConnection.integralFullEquiv p hp7 w, ?_⟩
  simpa [classReduce] using hw

theorem classReduce_kernel (hp7 : 7 ≤ p) (v : WPGammaIntegralLift.Residue p) :
    classReduce p hp7 v = 0 ↔ ∃ w, v = (p : ℤ) • w := by
  change reduceVector p ((WPReview.ResidueClosedConnection.integralFullEquiv p hp7).symm v) = 0 ↔ _
  rw [reduceVector_kernel]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨WPReview.ResidueClosedConnection.integralFullEquiv p hp7 w, ?_⟩
    have he := congrArg (WPReview.ResidueClosedConnection.integralFullEquiv p hp7) hw
    simpa only [LinearEquiv.apply_symm_apply, map_zsmul] using he
  · rintro ⟨w, rfl⟩
    exact ⟨(WPReview.ResidueClosedConnection.integralFullEquiv p hp7).symm w, by simp⟩

theorem classReduce_connection (hp7 : 7 ≤ p) (v : WPGammaIntegralLift.Residue p) :
    classReduce p hp7 (ActualConnection.quotientTheta ℤ_[p] v) =
      regularNabla p (classReduce p hp7 v) := by
  have he := WPReview.ResidueClosedConnection.integralFullEquiv_connection p hp7
    ((WPReview.ResidueClosedConnection.integralFullEquiv p hp7).symm v)
  simp only [LinearEquiv.apply_symm_apply] at he
  change reduceVector p ((WPReview.ResidueClosedConnection.integralFullEquiv p hp7).symm
    (ActualConnection.quotientTheta ℤ_[p] v)) = _
  rw [he, LinearEquiv.symm_apply_apply]
  exact gammaNabla_intertwines p _

end WPGammaClosedNumeratorBounds
