import WPGammaClosedNumeratorBounds.Full

noncomputable section

namespace WPGammaClosedNumeratorBounds

open Polynomial WPIntegralBlocks

variable (p : ℕ) [Fact p.Prime]

def scalarAction (a : S p) : End p := (LinearMap.lsmul (S p) (Space p) a).restrictScalars ℤ
def factor (a d : S p) (j : ℕ) : End p := gammaNabla p + scalarAction p (a+d*j)

def regularFactor (a d : ZMod p) (j : ℕ) : RegularEnd p :=
  regularNabla p + algebraMap (ZMod p) (RegularEnd p) (a+d*j)
def regularOps (a d : ZMod p) (j : ℕ) : Module.End ℤ (RegularSpace p) :=
  (regularFactor p a d j).restrictScalars ℤ

def scaleRegular (r : WPGammaURegular.R p) (v : RegularSpace p) : RegularSpace p :=
  (fun i => r*v.1 i, fun i => r*v.2 i)

theorem reduceVector_smul (r : S p) (v : Space p) :
    reduceVector p (r • v) = scaleRegular p (WPGammaIntegralLift.reduce p r) (reduceVector p v) := by
  apply Prod.ext <;> funext i <;> exact map_mul (WPGammaIntegralLift.reduce p) _ _

theorem factor_intertwines (a d : ℤ_[p]) (j : ℕ) (v : Space p) :
    reduceVector p (factor p (algebraMap ℤ_[p] (S p) a) (algebraMap ℤ_[p] (S p) d) j v) =
      regularFactor p (WPGammaIntegralLift.coefficientReduce p a)
        (WPGammaIntegralLift.coefficientReduce p d) j (reduceVector p v) := by
  change reduceVector p (gammaNabla p v +
    (algebraMap ℤ_[p] (S p) a+algebraMap ℤ_[p] (S p) d*j) • v) = _
  rw [map_add, gammaNabla_intertwines, reduceVector_smul]
  congr 1
  apply Prod.ext <;> funext i <;>
    simp [scaleRegular, WPGammaIntegralLift.reduce_coefficient, Algebra.smul_def,
      add_mul, mul_assoc]

def evaluate : Polynomial (ZMod p) →+* RegularEnd p :=
  Polynomial.eval₂RingHom' (algebraMap (ZMod p) (RegularEnd p)) (regularNabla p)
    (fun a => Algebra.commute_algebraMap_left a (regularNabla p))

theorem evaluate_X : evaluate p X = regularNabla p := by
  change Polynomial.eval₂ _ _ X = _
  exact Polynomial.eval₂_X _ _

theorem evaluate_C (a : ZMod p) : evaluate p (C a) = algebraMap (ZMod p) (RegularEnd p) a := by
  change Polynomial.eval₂ _ _ (C a) = _
  exact Polynomial.eval₂_C _ _

theorem evaluate_factor (a : ZMod p) :
    evaluate p (X+C a) = regularNabla p+algebraMap (ZMod p) (RegularEnd p) a := by
  rw [map_add, evaluate_X, evaluate_C]

theorem evaluate_primeCore : evaluate p (WPGammaBlocks.primeCore p) = regularPsi p := by
  rw [WPGammaBlocks.primeCore, map_sub, map_pow, evaluate_X]
  rfl

theorem ordered_evaluate (a d : ZMod p) (s n : ℕ) :
    ordered (regularOps p a d) s n =
      (evaluate p (WPGammaURegular.steppedPolynomial p (a+d*s) d n)).restrictScalars ℤ := by
  induction n generalizing s with
  | zero =>
    apply LinearMap.ext
    intro v
    simp [ordered, WPGammaURegular.steppedPolynomial]
  | succ n ih =>
    have hadd := WPGammaURegular.steppedPolynomial_add p (a+d*s) d 1 n
    have hs : a+d*(s+1 : ℕ) = a+d*(s : ZMod p)+d := by push_cast; ring
    have hone : WPGammaURegular.steppedPolynomial p (a+d*s) d 1 = X+C (a+d*s) := by
      simp [WPGammaURegular.steppedPolynomial]
    have he : WPGammaURegular.steppedPolynomial p (a+d*s) d (n+1) =
        (X+C (a+d*s)) * WPGammaURegular.steppedPolynomial p (a+d*s+d) d n := by
      simpa [Nat.add_comm, hone] using hadd
    rw [he, map_mul, evaluate_factor]
    apply LinearMap.ext
    intro v
    rw [ordered, Module.End.mul_apply, ih, hs]
    rfl

def primeBlock (a d : ℤ_[p]) (s : ℕ) : End p :=
  ordered (factor p (algebraMap ℤ_[p] (S p) a) (algebraMap ℤ_[p] (S p) d)) s p

theorem primeBlock_intertwines (a d : ℤ_[p])
    (hd : WPGammaIntegralLift.coefficientReduce p d ≠ 0) (s : ℕ) (v : Space p) :
    reduceVector p (primeBlock p a d s v) = regularPsi p (reduceVector p v) := by
  rw [primeBlock, ordered_reduction _
    (regularOps p (WPGammaIntegralLift.coefficientReduce p a) (WPGammaIntegralLift.coefficientReduce p d))
    (reduceVector p) (factor_intertwines p a d), ordered_evaluate,
    WPGammaURegular.steppedPolynomial_prime p _ _ hd, evaluate_primeCore]
  rfl

end WPGammaClosedNumeratorBounds
