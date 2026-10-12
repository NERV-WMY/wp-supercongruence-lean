import WPActualTensorContraction
import WPLaurentResidue
import WPActualNativeConnection
import WPActualFiniteResidueAttachment

namespace WPForcedSourceStokes

noncomputable section

/-- The residue of the actual transformed original conductor. -/
noncomputable def actualConductorResidue (p : ℕ) : RatFunc ℚ :=
  rationalResidue (actualTensorPairing p bivConductorR)

/-- Both finite native residuals are retained with their original signs. -/
noncomputable def actualDelta (p : ℕ) : RatFunc ℚ :=
  rationalResidue
    (-2*(1-bivX)*actualResidualPairing bivConductorR (actualRadialResidual p) +
      actualResidualPairing (fun i j => bivEta i j-bivConductorBU i j)
        (actualAngularResidual p))

noncomputable def actualNormalSourceResidue (p : ℕ) : RatFunc ℚ :=
  rationalResidue (actualTensorPairing p bivNormalSource)

noncomputable def actualTotalPrimitive (p : ℕ) : RatFunc ℚ :=
  actualConductorResidue p+nativePrimitive p

noncomputable def actualTotalSource (p : ℕ) : RatFunc ℚ :=
  actualDelta p+nativeEndpointCorrection p

/-- The actual angular total derivative has zero formal residue. -/
theorem actual_integrated_conductor_source (p : ℕ) (hp : 0<p) :
    actualNormalSourceResidue p =
      2*((1-symbol)*rationalDerivative (actualConductorResidue p) -
        actualConductorResidue p/2)+actualDelta p := by
  have h := congrArg rationalResidue (actual_unintegrated_source_identity p hp)
  have hC : 2*(1-bivX) = RatFunc.C (2*(1-symbol)) := by
    simp only [bivX, map_mul, map_sub, map_one, _root_.map_ofNat]
  have hsplit (a b c d e : RatFunc (RatFunc ℚ)) :
      a+b+c-d+e = (a+b+c)+(-d+e) := by ring
  have hd : rationalResidue
      (-(2*(1-bivX)*actualResidualPairing bivConductorR (actualRadialResidual p))+
        actualResidualPairing (fun i j => bivEta i j-bivConductorBU i j)
          (actualAngularResidual p)) = actualDelta p := by
    unfold actualDelta
    congr 1
    ring
  rw [hsplit, rationalResidue_add, hd] at h
  simp only [rationalResidue_add, rationalResidue_neg,
    rationalResidue_partialS, add_zero, hC, rationalResidue_coefficient_mul,
    rationalResidue_partialX] at h
  change actualNormalSourceResidue p =
    -actualConductorResidue p+
      (2*(1-symbol))*rationalDerivative (actualConductorResidue p)+actualDelta p at h
  rw [h]
  ring

/-- The full literal scalar source equation, with no horizontal-state premise. -/
theorem actual_full_forced_scalar (p : ℕ) (hp : 0<p) :
    2*symbol*rationalDerivative (nativeWeightedG p)+nativeWeightedG p =
      6750*((1-symbol)*rationalDerivative (actualTotalPrimitive p)-
        actualTotalPrimitive p/2)+3375*actualTotalSource p+nativeSquareForcing p := by
  have h := actual_native_primitive_forcing p hp
  rw [native_source_angular_decomposition p hp] at h
  have ha : nativeAngularSource p =
      2*((1-symbol)*rationalDerivative (actualConductorResidue p)-
        actualConductorResidue p/2)+actualDelta p := by
    have hr := actual_integrated_conductor_source p hp
    have hn := actual_normal_source_residue_attachment p
    change actualNormalSourceResidue p = nativeAngularSource p at hn
    rw [hn] at hr
    exact hr
  rw [ha] at h
  unfold actualTotalPrimitive actualTotalSource
  rw [rationalDerivative_add]
  linear_combination h

end

end WPForcedSourceStokes
