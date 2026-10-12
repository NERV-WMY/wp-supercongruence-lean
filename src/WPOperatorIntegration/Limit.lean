import WPOperatorIntegration.FiniteCoordinates

noncomputable section

namespace WPOperatorIntegration

set_option maxHeartbeats 1600000

open scoped BigOperators Topology
open Filter WPResidueQuotient
open WPCompletedCartier.ActualRationalizedQuotient

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

local instance : Module ℚ_[p] (RationalizedQuotient p hp) := quotientQpModule p hp

theorem finite_cartier_normalization (N : ℕ) (j : Fin 5) :
    factorialCoordinates p
      ((gammaMatrixQp p hp hp7 hp19).mulVec (finiteGammaColumn p hp N j)) =
    (j.val.factorial : ℚ_[p]) • rawQuotientEquiv p hp hp7 hp19
      (cartierQuotientQp p hp hp7 hp19
        ((p : ℚ_[p])^5 • finitePullbackQuotient p hp N j)) := by
  let q := finitePullbackQuotient p hp N j
  let c := cartierQuotientQp p hp hp7 hp19
  let g := gammaQuotientEquiv p hp hp7 hp19
  let d := factorialCoordinates p
  let s : ℚ_[p] := (p : ℚ_[p])^5
  let t : ℚ_[p] := j.val.factorial
  have hc := c.map_smul s q
  have hg := g.map_smul s (c q)
  have hd := d.map_smul s (g (c q))
  have hdt := d.map_smul (s * t) (g (c q))
  have ha := gamma_coordinate_action p hp hp7 hp19 q
  have hleft : factorialCoordinates p
      ((gammaMatrixQp p hp hp7 hp19).mulVec (finiteGammaColumn p hp N j)) =
      (s * t) • d (g (c q)) := by
    have hn : finiteGammaColumn p hp N j = (s * t) • g q :=
      actual_finite_normalization p hp hp7 hp19 N j
    have hm := (congrArg (fun v : Fin 5 → ℚ_[p] =>
      (gammaMatrixQp p hp hp7 hp19).mulVec v) hn).trans
        (Matrix.mulVec_smul (gammaMatrixQp p hp hp7 hp19) (s * t) (g q))
    have hh := hm.trans
      (congrArg (fun v : Fin 5 → ℚ_[p] => (s * t) • v) ha.symm)
    exact (congrArg d hh).trans hdt
  have hright : d (g (c (s • q))) = s • d (g (c q)) :=
    (congrArg d ((congrArg g hc).trans hg)).trans hd
  calc
    factorialCoordinates p
        ((gammaMatrixQp p hp hp7 hp19).mulVec (finiteGammaColumn p hp N j)) =
        (s * t) • d (g (c q)) := hleft
    _ = t • (s • d (g (c q))) :=
      (congrArg (fun a : ℚ_[p] => a • d (g (c q))) (mul_comm s t)).trans
        (mul_smul t s (d (g (c q))))
    _ = t • d (g (c (s • q))) := congrArg (fun v : Fin 5 → ℚ_[p] => t • v) hright.symm

theorem continuous_gamma_action :
    Continuous (fun v : Fin 5 → ℚ_[p] =>
      factorialCoordinates p ((gammaMatrixQp p hp hp7 hp19).mulVec v)) := by
  change Continuous (fun v : Fin 5 → ℚ_[p] => fun i =>
    (i.val.factorial : ℚ_[p]) * ∑ r, gammaMatrixQp p hp hp7 hp19 i r * v r)
  fun_prop

/-- The column law follows from the actual finite inverse-trace limit and
the actual raw pullback limit, with the factorial normalization retained. -/
theorem actual_gamma_column_law (j : Fin 5) :
    (gammaMatrixQp p hp hp7 hp19).mulVec
      (fun i => (WPResidueFrobenius.gammaRawInteriorMatrix p hp hp7 hp19 i j : ℚ_[p])) =
        (p : ℚ_[p])^5 • Pi.single j (1 : ℚ_[p]) := by
  have hsource := (finiteGammaColumn_tendsto p hp hp7 hp19 j).comp
    (tendsto_add_atTop_nat 1)
  have hleft := (continuous_gamma_action p hp hp7 hp19).tendsto _ |>.comp hsource
  have hright :=
    (WPCompletedCartier.InverseTraceQuotient.actual_quotient_inverse_trace_limit
      p hp hp7 hp19 j).const_smul (j.val.factorial : ℚ_[p])
  have hsame : Tendsto (fun N => factorialCoordinates p
      ((gammaMatrixQp p hp hp7 hp19).mulVec (finiteGammaColumn p hp (N + 1) j)))
      atTop (nhds ((j.val.factorial : ℚ_[p]) •
        ((p : ℚ_[p])^5 • Pi.single j (1 : ℚ_[p])))) := by
    simpa only [finite_cartier_normalization] using hright
  have he := tendsto_nhds_unique hleft hsame
  apply (factorialCoordinates p).injective
  exact he.trans (by
    ext i
    by_cases hi : i = j
    · subst i
      simp [factorialCoordinates, Pi.single_apply, mul_comm]
    · simp [factorialCoordinates, Pi.single_apply, hi])

end WPOperatorIntegration
