import WPGammaIntegralLift.Reduction
import Mathlib.LinearAlgebra.StdBasis

noncomputable section

namespace WPGammaIntegralLift

open Polynomial
open Module
open WPResidueQuotient

variable (p : ℕ) [Fact p.Prime]

theorem reduce_theta_polynomial (f : Polynomial ℤ_[p]) :
    reduce p (Parameter.theta (algebraMap (Polynomial ℤ_[p]) (S p) f)) =
      WPGammaURegular.regularTheta p (baseReduce p f) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg]
  | monomial n a =>
    have hf : algebraMap (Polynomial ℤ_[p]) (S p) (monomial n a) =
        algebraMap ℤ_[p] (S p) a * Parameter.u ^ n := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      change algebraMap (Polynomial ℤ_[p]) (S p)
        (algebraMap ℤ_[p] (Polynomial ℤ_[p]) a) * Parameter.u ^ n = _
      rw [← IsScalarTower.algebraMap_apply ℤ_[p] (Polynomial ℤ_[p]) (S p)]
    have hb : baseReduce p (monomial n a) =
        algebraMap (ZMod p) (WPGammaURegular.R p) (coefficientReduce p a) *
          regularU p ^ n := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, baseReduce_C, baseReduce_X]
    rw [hf, hb, Parameter.theta.leibniz, Parameter.theta.map_algebraMap,
      Parameter.theta.leibniz_pow, Parameter.theta_u,
      (WPGammaURegular.regularTheta p).leibniz,
      (WPGammaURegular.regularTheta p).map_algebraMap,
      (WPGammaURegular.regularTheta p).leibniz_pow]
    have hu : WPGammaURegular.regularTheta p (regularU p) = regularU p := by
      apply Subtype.ext
      exact WPGammaU.theta_u p
    rw [hu]
    simp [smul_eq_mul, nsmul_eq_mul]

/-- Differentiate the localization denominator identity and cancel its unit
image; no reduction injectivity is used. -/
theorem reduce_theta (a : S p) :
    reduce p (Parameter.theta a) = WPGammaURegular.regularTheta p (reduce p a) := by
  obtain ⟨n, f, hf⟩ := IsLocalization.Away.surj (Parameter.denominatorPolynomial ℤ_[p]) a
  let d : S p := algebraMap (Polynomial ℤ_[p]) (S p)
    (Parameter.denominatorPolynomial ℤ_[p]) ^ n
  have hunit : IsUnit (reduce p d) := by
    dsimp [d]
    rw [← map_pow, reduce_polynomial, map_pow]
    exact (baseReduce_denominator p).pow n
  apply hunit.mul_right_inj.mp
  have ht := congrArg (fun x => reduce p (Parameter.theta x)) hf
  rw [Parameter.theta.leibniz] at ht
  have ht' := congrArg (WPGammaURegular.regularTheta p) (congrArg (reduce p) hf)
  rw [map_mul, reduce_polynomial, (WPGammaURegular.regularTheta p).leibniz] at ht'
  have htd := reduce_theta_polynomial p (Parameter.denominatorPolynomial ℤ_[p] ^ n)
  have htf := reduce_theta_polynomial p f
  change reduce p (a • Parameter.theta d + d • Parameter.theta a) =
    reduce p (Parameter.theta (algebraMap (Polynomial ℤ_[p]) (S p) f)) at ht
  simp only [map_add, smul_eq_mul, map_mul] at ht
  change reduce p a • WPGammaURegular.regularTheta p (reduce p d) +
    reduce p d • WPGammaURegular.regularTheta p (reduce p a) =
    WPGammaURegular.regularTheta p (baseReduce p f) at ht'
  have hdtheta : reduce p (Parameter.theta d) =
      WPGammaURegular.regularTheta p (reduce p d) := by
    dsimp [d]
    rw [← map_pow, reduce_polynomial]
    exact htd
  rw [hdtheta, htf] at ht
  simp only [smul_eq_mul] at ht'
  exact add_left_cancel (ht.trans ht'.symm)

abbrev Space := Fin 5 → S p
abbrev End := Module.End ℤ (Space p)

def reduceVector : Space p →ₗ[ℤ] WPGammaURegular.RegularSpace p where
  toFun v := fun i => reduce p (v i)
  map_add' _ _ := by funext i; exact map_add (reduce p) _ _
  map_smul' a v := by funext i; simp

theorem reduceVector_surjective : Function.Surjective (reduceVector p) := by
  intro v
  choose w hw using fun i => reduce_surjective p (v i)
  exact ⟨w, funext hw⟩

theorem reduceVector_kernel (v : Space p) :
    reduceVector p v = 0 ↔ ∃ w, v = (p : ℤ) • w := by
  constructor
  · intro h
    have hi (i : Fin 5) : reduce p (v i) = 0 := congrFun h i
    choose w hw using fun i => (reduce_kernel p (v i)).mp (hi i)
    refine ⟨w, ?_⟩
    funext i
    simpa [Algebra.smul_def] using hw i
  · rintro ⟨w, rfl⟩
    funext i
    change reduce p ((p : ℤ) • w i) = 0
    apply (reduce_kernel p _).mpr
    exact ⟨w i, by simp⟩

/-- This is the integral coordinate operator of the literal factorial classes
already constructed in the residue quotient. -/
def gammaNabla : End p := (WPReview.ResidueConnection.gammaNabla ℤ_[p]).restrictScalars ℤ

theorem reduce_gammaM (i j : Fin 5) :
    reduce p (WPReview.ResidueConnection.gammaM ℤ_[p] i j) =
      WPGammaURegular.gammaM p i j := by
  fin_cases i <;> fin_cases j <;>
    simp [WPReview.ResidueConnection.gammaM, WPGammaURegular.gammaM, map_ofNat]
  all_goals ring

theorem gammaNabla_intertwines (v : Space p) :
    reduceVector p (gammaNabla p v) = WPGammaURegular.gammaNabla p (reduceVector p v) := by
  funext i
  change reduce p (Parameter.theta (v i) +
      ∑ j : Fin 5, WPReview.ResidueConnection.gammaM ℤ_[p] i j * v j) =
    WPGammaURegular.regularTheta p (reduce p (v i)) +
      ∑ j : Fin 5, WPGammaURegular.gammaM p i j * reduce p (v j)
  rw [map_add, reduce_theta, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, reduce_gammaM]

abbrev Residue := WPReview.ResidueConnection.Residue ℤ_[p]

def gammaSection : Space p →ₗ[S p] Residue p :=
  WPReview.ResidueConnection.gammaSection ℤ_[p]

theorem gammaSection_injective : Function.Injective (gammaSection p) :=
  WPReview.ResidueConnection.integral_gammaSection_injective p

theorem gammaSection_apply (v : Space p) :
    gammaSection p v = ∑ i : Fin 5, v i • ActualConnection.qGamma ℤ_[p] i.val :=
  WPReview.ResidueConnection.gammaSection_apply ℤ_[p] v

theorem gammaSection_connection (hp7 : 7 ≤ p) (v : Space p) :
    ActualConnection.quotientTheta ℤ_[p] (gammaSection p v) =
      gammaSection p (gammaNabla p v) :=
  WPReview.ResidueConnection.integral_gammaSection_connection p hp7 v

/-- The actual finite Gamma lattice is the range of the injective section.
The reduction below is transported from its integral coordinates, rather
than obtained by reducing ambient factorial fractions. -/
def gammaLattice : Submodule (S p) (Residue p) := (gammaSection p).range

def gammaLatticeEquiv : Space p ≃ₗ[S p] gammaLattice p :=
  LinearEquiv.ofInjective (gammaSection p) (gammaSection_injective p)

theorem gammaLatticeEquiv_val (v : Space p) :
    (gammaLatticeEquiv p v : Residue p) = gammaSection p v := rfl

/-- An actual constructed basis of the section's range, not a supplied basis
for the entire residue quotient. -/
def gammaBasis : Basis (Fin 5) (S p) (gammaLattice p) :=
  (Pi.basisFun (S p) (Fin 5)).map (gammaLatticeEquiv p)

theorem gammaBasis_val (i : Fin 5) :
    (gammaBasis p i : Residue p) = ActualConnection.qGamma ℤ_[p] i.val := by
  simp only [gammaBasis, Basis.map_apply, Pi.basisFun_apply]
  change gammaSection p (Pi.single i 1) = _
  exact WPReview.ResidueConnection.gammaSection_single ℤ_[p] i

def latticeConnection : Module.End ℤ (gammaLattice p) :=
  ((gammaLatticeEquiv p).toLinearMap.restrictScalars ℤ).comp
    ((gammaNabla p).comp ((gammaLatticeEquiv p).symm.toLinearMap.restrictScalars ℤ))

theorem latticeConnection_val (hp7 : 7 ≤ p) (v : gammaLattice p) :
    (latticeConnection p v : Residue p) =
      ActualConnection.quotientTheta ℤ_[p] (v : Residue p) := by
  change gammaSection p (gammaNabla p ((gammaLatticeEquiv p).symm v)) = _
  rw [← gammaSection_connection p hp7]
  have he := gammaLatticeEquiv_val p ((gammaLatticeEquiv p).symm v)
  simp only [LinearEquiv.apply_symm_apply] at he
  rw [← he]

def latticeReduce : gammaLattice p →ₗ[ℤ] WPGammaURegular.RegularSpace p :=
  (reduceVector p).comp ((gammaLatticeEquiv p).symm.toLinearMap.restrictScalars ℤ)

theorem latticeReduce_equiv (v : Space p) :
    latticeReduce p (gammaLatticeEquiv p v) = reduceVector p v := by
  simp [latticeReduce]

theorem latticeReduce_connection (v : gammaLattice p) :
    latticeReduce p (latticeConnection p v) =
      WPGammaURegular.gammaNabla p (latticeReduce p v) := by
  change latticeReduce p (gammaLatticeEquiv p
    (gammaNabla p ((gammaLatticeEquiv p).symm v))) = _
  rw [latticeReduce_equiv, gammaNabla_intertwines]
  rfl

theorem latticeReduce_surjective : Function.Surjective (latticeReduce p) := by
  intro v
  obtain ⟨w, hw⟩ := reduceVector_surjective p v
  exact ⟨gammaLatticeEquiv p w, by simpa [latticeReduce] using hw⟩

theorem latticeReduce_kernel (v : gammaLattice p) :
    latticeReduce p v = 0 ↔ ∃ w, v = (p : ℤ) • w := by
  change reduceVector p ((gammaLatticeEquiv p).symm v) = 0 ↔ _
  rw [reduceVector_kernel]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨gammaLatticeEquiv p w, ?_⟩
    have he := congrArg (gammaLatticeEquiv p) hw
    simpa only [LinearEquiv.apply_symm_apply, map_zsmul] using he
  · rintro ⟨w, rfl⟩
    exact ⟨(gammaLatticeEquiv p).symm w, by simp⟩

end WPGammaIntegralLift
