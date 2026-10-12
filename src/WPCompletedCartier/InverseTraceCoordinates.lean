import WPCompletedCartier.InverseTraceConstruction

namespace WPCompletedCartier.InverseTraceCoordinates

noncomputable section
open scoped BigOperators
open WPResidueQuotient WPResidueQuotient.Adic WPResidueQuotient.ActualCompletion

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

local notation "u" => Parameter.integralTenth p hp

/-- Gamma coordinates followed by the actual raw-pole factorial normalization. -/
def rawProjection : InverseTraceTail.StrictCompleted p hp →ₗ[ℤ_[p]] (Fin 5 → ℤ_[p]) where
  toFun x i := (i.val.factorial : ℤ_[p]) *
    constantCoordinatesZp p hp hp7 hp19 (completedInteriorInclusion u (p : ℤ_[p]) x)
      (Fin.castAdd 6 i)
  map_add' x y := by ext i; simp only [map_add, Pi.add_apply, mul_add]
  map_smul' c x := by
    ext i
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def coeVector : (Fin 5 → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 5 → ℚ_[p]) where
  toFun x i := x i
  map_add' x y := by ext i; exact PadicInt.coe_add _ _
  map_smul' c x := by ext i; exact PadicInt.coe_mul _ _

theorem coeVector_single (r : Fin 5) :
    coeVector p (Pi.single r (1 : ℤ_[p])) = Pi.single r (1 : ℚ_[p]) := by
  ext i
  by_cases hi : i = r
  · subst i
    simp [coeVector]
  · simp [coeVector, hi]

theorem continuous_rawProjection : Continuous (rawProjection p hp hp7 hp19) := by
  apply continuous_pi
  intro i
  exact continuous_const.mul (((continuous_apply (Fin.castAdd 6 i)).comp
    (continuous_constantCoordinatesZp p hp hp7 hp19)).comp
      (continuous_completeMap (p : ℤ_[p]) (actualInteriorInclusion u)))

theorem continuous_coeVector : Continuous (coeVector p) := by
  apply continuous_pi
  intro i
  exact continuous_subtype_val.comp (continuous_apply i)

theorem scalarEnd_isUnit (s : Submonoid.powers (p : ℤ_[p])) :
    IsUnit (algebraMap ℤ_[p] (Module.End ℤ_[p] (Fin 5 → ℚ_[p])) (s : ℤ_[p])) := by
  have hs : (s : ℤ_[p]) ≠ 0 := by
    obtain ⟨e, he⟩ := s.property
    rw [← he]
    exact pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hsQ : ((s : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    intro h
    exact hs (Subtype.ext h)
  apply (Module.End.isUnit_iff _).mpr
  constructor
  · intro x y h
    ext i
    have hi := congrFun h i
    change ((s : ℤ_[p]) : ℚ_[p]) * x i = ((s : ℤ_[p]) : ℚ_[p]) * y i at hi
    exact mul_left_cancel₀ hsQ hi
  · intro x
    refine ⟨fun i => (((s : ℤ_[p]) : ℚ_[p]))⁻¹ * x i, ?_⟩
    ext i
    change ((s : ℤ_[p]) : ℚ_[p]) * ((((s : ℤ_[p]) : ℚ_[p]))⁻¹ * x i) = x i
    rw [← mul_assoc, mul_inv_cancel₀ hsQ, one_mul]

/-- The actual projection is extended through the universal property of
localization; finite p-power denominators act by their honest inverses. -/
def rationalizedProjection : RationalizedCartier.Rationalized p hp →ₗ[ℤ_[p]]
    (Fin 5 → ℚ_[p]) :=
  LocalizedModule.lift (Submonoid.powers (p : ℤ_[p]))
    ((coeVector p).comp (rawProjection p hp hp7 hp19)) (scalarEnd_isUnit p)

theorem rationalizedProjection_integral (x : InverseTraceTail.StrictCompleted p hp) :
    rationalizedProjection p hp hp7 hp19 (RationalizedCartier.integralMap p hp x) =
      coeVector p (rawProjection p hp hp7 hp19 x) := by
  exact LocalizedModule.lift_mk_one (Submonoid.powers (p : ℤ_[p]))
    ((coeVector p).comp (rawProjection p hp hp7 hp19)) (scalarEnd_isUnit p) x

theorem selectedFactorial_zero_inclusion (r : Fin 5) :
    actualInteriorInclusion u (InverseTraceTail.selectedFactorial p hp r 0) =
      Actual.gammaClosedElement u r := by
  apply Subtype.ext
  simp only [InverseTraceTail.selectedFactorial, Nat.add_zero, pow_zero,
    NumericalTerms.kappa_one, factorialNumeratorMap_apply, map_one, one_mul,
    Actual.gammaClosedElement]
  rfl

theorem rawProjection_head (r : Fin 5) :
    rawProjection p hp hp7 hp19
      (ofModule (p : ℤ_[p]) (InverseTraceImage.headTerm p hp r)) = Pi.single r 1 := by
  ext i
  change (i.val.factorial : ℤ_[p]) *
    constantCoordinatesZp p hp hp7 hp19
      (completeMap (p : ℤ_[p]) (actualInteriorInclusion u)
        (ofModule (p : ℤ_[p]) (InverseTraceImage.headTerm p hp r)))
      (Fin.castAdd 6 i) = _
  rw [completeMap_ofModule]
  change (i.val.factorial : ℤ_[p]) *
    constantCoordinatesZp p hp hp7 hp19
      (ofModule (p : ℤ_[p])
        (actualInteriorInclusion u (InverseTraceAlgebra.inverseFactorial p hp r •
          InverseTraceTail.selectedFactorial p hp r 0))) (Fin.castAdd 6 i) = _
  rw [map_smul, map_smul, selectedFactorial_zero_inclusion,
    map_smul, constantCoordinatesZp_gamma]
  by_cases hir : i = r
  · subst i
    simpa only [Pi.smul_apply, Pi.single_apply, if_true, smul_eq_mul, mul_one] using
      (mul_comm (r.val.factorial : ℤ_[p])
        (InverseTraceAlgebra.inverseFactorial p hp r)).trans
          (InverseTraceAlgebra.inverseFactorial_mul p hp r)
  · have hcast : Fin.castAdd 6 i ≠ Fin.castAdd 6 r := by
      intro h
      exact hir (Fin.ext (congrArg (fun j : Fin 11 => j.val) h))
    simp [Pi.smul_apply, hcast, hir]

set_option maxHeartbeats 800000 in
theorem scaled_cartier_image (N : ℕ) (hN : 1 ≤ N) (r : Fin 5) :
    RationalizedCartier.cartier p hp
      (algebraMap ℤ_[p] (RationalizedCartier.Coeff p) ((p : ℤ_[p]) ^ 5) •
        InverseTraceConstruction.finitePullback p hp N r) =
      RationalizedCartier.integralMap p hp
        ((p : ℤ_[p]) ^ 5 • (∑ k ∈ Finset.range N, InverseTraceImage.rowSum p hp r k)) := by
  rw [map_smul, InverseTraceConstruction.cartier_finitePullback p hp N hN r,
    InverseTraceImage.finite_rowSum_eq_head_add_tail p hp r N hN,
    IsScalarTower.algebraMap_smul, ← map_smul]
  rfl

/-- The actual rationalized Cartier images of the finite raw pullbacks converge
to p^5 phi_r in the actual quotient's raw coordinates. No Frobenius limit is assumed. -/
theorem actual_inverse_trace_limit (r : Fin 5) :
    Filter.Tendsto
      (fun N => rationalizedProjection p hp hp7 hp19
        (RationalizedCartier.cartier p hp
          (algebraMap ℤ_[p] (RationalizedCartier.Coeff p) ((p : ℤ_[p]) ^ 5) •
            InverseTraceConstruction.finitePullback p hp (N + 1) r)))
      Filter.atTop (nhds ((p : ℚ_[p]) ^ 5 • Pi.single r (1 : ℚ_[p]))) := by
  have ht := ((continuous_coeVector p).comp
    (continuous_rawProjection p hp hp7 hp19)).tendsto
      (ofModule (p : ℤ_[p]) (InverseTraceImage.headTerm p hp r))
  have hlim := ht.comp (InverseTraceImage.finite_rowSum_tendsto_head p hp r)
  have hs := hlim.const_smul ((p : ℚ_[p]) ^ 5)
  simp only [Function.comp_apply] at hs
  have he (N : ℕ) := scaled_cartier_image p hp (N + 1) (by omega) r
  have hfunc :
      (fun N => rationalizedProjection p hp hp7 hp19
        (RationalizedCartier.cartier p hp
          (algebraMap ℤ_[p] (RationalizedCartier.Coeff p) ((p : ℤ_[p]) ^ 5) •
            InverseTraceConstruction.finitePullback p hp (N + 1) r))) =
      (fun N => (p : ℚ_[p]) ^ 5 • coeVector p
        (rawProjection p hp hp7 hp19
          (∑ k ∈ Finset.range (N + 1), InverseTraceImage.rowSum p hp r k))) := by
    funext N
    rw [he, rationalizedProjection_integral, map_smul]
    ext i
    change (((p : ℤ_[p]) ^ 5 *
      rawProjection p hp hp7 hp19
        (∑ k ∈ Finset.range (N + 1), InverseTraceImage.rowSum p hp r k) i : ℤ_[p]) : ℚ_[p]) =
      (p : ℚ_[p]) ^ 5 *
        (rawProjection p hp hp7 hp19
          (∑ k ∈ Finset.range (N + 1), InverseTraceImage.rowSum p hp r k) i : ℚ_[p])
    rw [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
  rw [hfunc]
  rw [rawProjection_head, coeVector_single] at hs
  exact hs

end

end WPCompletedCartier.InverseTraceCoordinates
