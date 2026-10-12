import WPGammaIntegralLift.Connection
import WPIntegralBlocks

noncomputable section

namespace WPGammaIntegralLift

open WPResidueQuotient

variable (p : ℕ) [Fact p.Prime]

def scalarAction (a : S p) : End p :=
  (LinearMap.lsmul (S p) (Space p) a).restrictScalars ℤ

def factor (a d : S p) (j : ℕ) : End p :=
  gammaNabla p + scalarAction p (a + d * j)

def reducedFactor (a d : ZMod p) (j : ℕ) : WPGammaURegular.RegularEnd p :=
  WPGammaURegular.gammaNabla p +
    algebraMap (ZMod p) (WPGammaURegular.RegularEnd p) (a + d * j)

def reducedOps (a d : ZMod p) (j : ℕ) :
    Module.End ℤ (WPGammaURegular.RegularSpace p) :=
  (reducedFactor p a d j).restrictScalars ℤ

theorem factor_intertwines (a d : ℤ_[p]) (j : ℕ) (v : Space p) :
    reduceVector p (factor p (algebraMap ℤ_[p] (S p) a)
      (algebraMap ℤ_[p] (S p) d) j v) =
    reducedFactor p (coefficientReduce p a) (coefficientReduce p d) j (reduceVector p v) := by
  change reduceVector p (gammaNabla p v + (algebraMap ℤ_[p] (S p) a +
    algebraMap ℤ_[p] (S p) d * j) • v) = _
  rw [map_add, gammaNabla_intertwines]
  funext i
  change _ + reduce p ((algebraMap ℤ_[p] (S p) a +
    algebraMap ℤ_[p] (S p) d * j) * v i) = _ + _
  simp [reduce_coefficient, Algebra.smul_def, reduceVector, add_mul, mul_assoc]

theorem reduced_ordered_eq (a d : ZMod p) (s n : ℕ) :
    WPIntegralBlocks.ordered (reducedOps p a d) s n =
      (WPGammaURegular.steppedOperatorProduct p (a + d * s) d n).restrictScalars ℤ := by
  induction n generalizing s with
  | zero =>
    apply LinearMap.ext
    intro v
    simp [WPIntegralBlocks.ordered, WPGammaURegular.steppedOperatorProduct]
  | succ n ih =>
    have hadd := WPGammaURegular.steppedOperatorProduct_add p (a + d * s) d 1 n
    have hadd' : WPGammaURegular.steppedOperatorProduct p (a + d * s) d (n + 1) =
        WPGammaURegular.steppedOperatorProduct p (a + d * s) d 1 *
        WPGammaURegular.steppedOperatorProduct p (a + d * s + d) d n := by
      simpa [Nat.add_comm] using hadd
    have hs : a + d * (s + 1 : ℕ) = a + d * (s : ZMod p) + d := by push_cast; ring
    have hone : WPGammaURegular.steppedOperatorProduct p (a + d * s) d 1 =
        reducedFactor p a d s := by
      simp [WPGammaURegular.steppedOperatorProduct, reducedFactor]
    apply LinearMap.ext
    intro v
    rw [WPIntegralBlocks.ordered, Module.End.mul_apply, ih, hs, hadd', hone]
    rfl

/-- Every five consecutive p-blocks vanish after actual lattice reduction. -/
theorem factors_divisible (hp7 : 7 ≤ p) (a d : ℤ_[p])
    (hd : coefficientReduce p d ≠ 0) (s n : ℕ) :
    WPIntegralBlocks.Divisible p (n / (5 * p))
      (WPIntegralBlocks.ordered
        (factor p (algebraMap ℤ_[p] (S p) a) (algebraMap ℤ_[p] (S p) d)) s n) := by
  apply WPIntegralBlocks.ordered_divisible_of_reduction p (5 * p) _
    (reducedOps p (coefficientReduce p a) (coefficientReduce p d))
    (reduceVector p) (reduceVector_kernel p) (factor_intertwines p a d)
  intro t
  rw [reduced_ordered_eq,
    WPGammaURegular.steppedOperatorProduct_five_prime_zero p hp7 _ _ hd]
  rfl

theorem negative_six_residue_ne_zero (hp7 : 7 ≤ p) : coefficientReduce p (-6) ≠ 0 := by
  rw [map_neg, map_ofNat]
  exact neg_ne_zero.mpr (WPFiveFactor.six_unit p Fact.out hp7).ne_zero

/-- The progression is the original -6 progression, with arbitrary p-adic
starting scalar and every natural starting index. -/
theorem original_factors_divisible (hp7 : 7 ≤ p) (a : ℤ_[p]) (s n : ℕ) :
    WPIntegralBlocks.Divisible p (n / (5 * p))
      (WPIntegralBlocks.ordered (factor p (algebraMap ℤ_[p] (S p) a) (-6)) s n) := by
  simpa [map_ofNat] using
    factors_divisible p hp7 a (-6) (negative_six_residue_ne_zero p hp7) s n

def primeBlock (a d : ℤ_[p]) (s : ℕ) : End p :=
  WPIntegralBlocks.ordered
    (factor p (algebraMap ℤ_[p] (S p) a) (algebraMap ℤ_[p] (S p) d)) s p

theorem primeBlock_intertwines (a d : ℤ_[p]) (hd : coefficientReduce p d ≠ 0)
    (s : ℕ) (v : Space p) :
    reduceVector p (primeBlock p a d s v) =
      WPGammaURegular.gammaPsi p (reduceVector p v) := by
  rw [primeBlock, WPIntegralBlocks.ordered_reduction _
    (reducedOps p (coefficientReduce p a) (coefficientReduce p d))
    (reduceVector p) (factor_intertwines p a d), reduced_ordered_eq]
  have he : WPGammaURegular.steppedOperatorProduct p
      (coefficientReduce p a + coefficientReduce p d * s) (coefficientReduce p d) p =
      WPGammaURegular.gammaPsi p := by
    rw [WPGammaURegular.steppedOperatorProduct_evaluate,
      WPGammaURegular.steppedPolynomial_prime p _ _ hd,
      WPGammaURegular.evaluate_primeCore]
  rw [he]
  rfl

/-- Each block may have its own p-adic shift and nonzero reduced
step. Their reductions are the same literal psi, so any five blocks gain p. -/
theorem variable_prime_blocks_divisible (hp7 : 7 ≤ p) (a d : ℕ → ℤ_[p])
    (hd : ∀ j, coefficientReduce p (d j) ≠ 0) (start : ℕ → ℕ) (s n : ℕ) :
    WPIntegralBlocks.Divisible p (n / 5)
      (WPIntegralBlocks.ordered (fun j => primeBlock p (a j) (d j) (start j)) s n) := by
  apply WPIntegralBlocks.blocks_divisible_of_nilpotent_reduction p 5 _
    ((WPGammaURegular.gammaPsi p).restrictScalars ℤ) (reduceVector p)
    (reduceVector_kernel p)
  · intro j v
    exact primeBlock_intertwines p (a j) (d j) (hd j) (start j) v
  · apply LinearMap.ext
    intro v
    change ((WPGammaURegular.gammaNabla p ^ p - WPGammaURegular.gammaNabla p) ^ 5) v = 0
    rw [WPGammaURegular.actual_regular_u_fifth_zero p hp7]
    rfl

theorem original_prime_blocks_divisible (hp7 : 7 ≤ p) (a : ℕ → ℤ_[p])
    (start : ℕ → ℕ) (s n : ℕ) :
    WPIntegralBlocks.Divisible p (n / 5)
      (WPIntegralBlocks.ordered (fun j => primeBlock p (a j) (-6) (start j)) s n) :=
  variable_prime_blocks_divisible p hp7 a (fun _ => -6)
    (fun _ => negative_six_residue_ne_zero p hp7) start s n

def residueFactor (a d : S p) (j : ℕ) : Module.End ℤ (Residue p) :=
  (ActualConnection.quotientTheta ℤ_[p]).restrictScalars ℤ +
    (LinearMap.lsmul (S p) (Residue p) (a + d * j)).restrictScalars ℤ

theorem gammaSection_factor (hp7 : 7 ≤ p) (a d : S p) (j : ℕ) (v : Space p) :
    gammaSection p (factor p a d j v) = residueFactor p a d j (gammaSection p v) := by
  change gammaSection p (gammaNabla p v + (a + d * j) • v) = _
  rw [map_add, map_smul, ← gammaSection_connection p hp7]
  rfl

theorem gammaSection_ordered (hp7 : 7 ≤ p) (a d : S p) (s n : ℕ) (v : Space p) :
    gammaSection p (WPIntegralBlocks.ordered (factor p a d) s n v) =
      WPIntegralBlocks.ordered (residueFactor p a d) s n (gammaSection p v) :=
  WPIntegralBlocks.ordered_reduction _ _ ((gammaSection p).restrictScalars ℤ)
    (gammaSection_factor p hp7 a d) s n v

/-- Divisibility takes place in the actual integral Gamma class lattice.
It is not a statement about ambient fractions reduced modulo p. -/
theorem original_actual_classes_divisible (hp7 : 7 ≤ p) (a : ℤ_[p])
    (s n : ℕ) (v : Space p) : ∃ w : Space p,
    WPIntegralBlocks.ordered (residueFactor p (algebraMap ℤ_[p] (S p) a) (-6)) s n
      (gammaSection p v) = (p : ℤ)^(n / (5 * p)) • gammaSection p w := by
  obtain ⟨w, hw⟩ := original_factors_divisible p hp7 a s n v
  refine ⟨w, ?_⟩
  rw [← gammaSection_ordered p hp7, hw, map_zsmul]

end WPGammaIntegralLift
