import WPActualIntegratedSource

open scoped BigOperators

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- The first finite native endpoint, with the complete angular and radial rows. -/
noncomputable def actualFirstEndpointError (p : ℕ) : RatFunc ℚ :=
  -rationalResidue (bivS^(p-1)/(1-bivS) *
    ∑ j : Fin 3, (bivEta 2 j-bivConductorBU 2 j)*finiteNativeJet p bivB j)

/-- The last-column angular endpoint before its evaluation term is canceled. -/
noncomputable def actualLastColumnEndpoint (p : ℕ) : RatFunc ℚ :=
  lambda^p * rationalResidue
    ((∑ i : Fin 3, bivEta i 2*finiteNativeJet p bivS i) /
      (bivS^p*(bivS-bivLambda)))

/-- The actual complete conductor functional obtained from both finite residuals. -/
noncomputable def actualBetaFunctional (p : ℕ) : RatFunc ℚ :=
  lambda^p * rationalResidue
    ((∑ i : Fin 3,
      ((6*(1-bivX)*bivS/bivX)*bivConductorR i 2-bivConductorBU i 2)*
        finiteNativeJet p bivS i) /
      (bivS^(p+1)*(1-bivB)))

/-- No native forcing entry is dropped in splitting the actual source residue. -/
theorem actual_delta_endpoint_split (p : ℕ) (hp : 0<p) :
    actualDelta p = RatFunc.C (WPReview.nativeEndpoint p) *
      (actualFirstEndpointError p+actualBetaFunctional p+actualLastColumnEndpoint p) := by
  have hpS : bivS^p = bivS^(p-1)*bivS := by
    rw [← pow_succ]
    congr 1
    omega
  have hbP : bivB^p = bivLambda^p/bivS^p := by
    simp only [bivB, div_pow]
  have hden : bivS^p ≠ 0 := pow_ne_zero _ bivS_ne_zero
  have hden1 : bivS-bivLambda ≠ 0 := bivS_sub_coefficient_ne_zero lambda
  have hA : algebraMap ℚ (RatFunc (RatFunc ℚ)) (WPReview.nativeEndpoint p) =
      RatFunc.C (RatFunc.C (WPReview.nativeEndpoint p)) := outer_native_scalar _
  have hl : RatFunc.C lambda = bivLambda := rfl
  have h2 : (⟨2, by omega⟩ : Fin 3) = 2 := by ext; norm_num
  have hi :
      -2*(1-bivX)*actualResidualPairing bivConductorR (actualRadialResidual p) +
        actualResidualPairing (fun i j => bivEta i j-bivConductorBU i j)
          (actualAngularResidual p) =
      RatFunc.C (RatFunc.C (WPReview.nativeEndpoint p)) *
        (-(bivS^(p-1)/(1-bivS) *
            ∑ j : Fin 3, (bivEta 2 j-bivConductorBU 2 j)*finiteNativeJet p bivB j) +
          RatFunc.C (lambda^p) *
            ((∑ i : Fin 3,
              ((6*(1-bivX)*bivS/bivX)*bivConductorR i 2-bivConductorBU i 2)*
                finiteNativeJet p bivS i) /
              (bivS^(p+1)*(1-bivB))) +
          RatFunc.C (lambda^p) *
            ((∑ i : Fin 3, bivEta i 2*finiteNativeJet p bivS i) /
              (bivS^p*(bivS-bivLambda)))) := by
    simp only [actualResidualPairing, actualRadialResidual, actualAngularResidual,
      hA, Fin.sum_univ_succ, Fin.sum_univ_zero]
    dsimp only [Fin.succ]
    norm_num [Fin.ext_iff]
    simp only [h2, hl]
    rw [hbP, pow_succ]
    unfold bivB
    field_simp [bivS_ne_zero, bivX_ne_zero, biv_one_sub_s_ne_zero,
      hden, hden1]
    rw [hpS]
    ring
  unfold actualDelta
  rw [hi, rationalResidue_coefficient_mul]
  simp only [rationalResidue_add, rationalResidue_neg,
    rationalResidue_coefficient_mul, actualFirstEndpointError,
    actualBetaFunctional, actualLastColumnEndpoint]

/-- The ordinary-state third forcing vector cancels the factor 1-b exactly. -/
theorem actual_conductor_last_column (i : Fin 3) :
    bivConductorR i 2/(1-bivB) =
      ∑ a : Fin 3, bivJCG bivS i a*bivBsDivU a 0 := by
  have hc (a : Fin 3) : bivJCG bivB 2 a = if a=0 then 1-bivB else 0 := by
    fin_cases a <;> rfl
  simp only [bivConductorR, hc, Fin.sum_univ_succ, Fin.sum_univ_zero]
  dsimp only [Fin.succ]
  norm_num [Fin.ext_iff]
  field_simp [biv_one_sub_b_ne_zero]

theorem actual_radial_last_column (i : Fin 3) :
    bivConductorBU i 2/(1-bivB) =
      ∑ a : Fin 3, bivJCG bivS i a*bivBU a 0 := by
  have hc (a : Fin 3) : bivJCG bivB 2 a = if a=0 then 1-bivB else 0 := by
    fin_cases a <;> rfl
  simp only [bivConductorBU, hc, Fin.sum_univ_succ, Fin.sum_univ_zero]
  dsimp only [Fin.succ]
  norm_num [Fin.ext_iff]
  field_simp [biv_one_sub_b_ne_zero]

/-- The original ordinary-state conductor functional, retaining the complete BU row. -/
theorem actual_beta_functional_ordinary (p : ℕ) :
    actualBetaFunctional p = lambda^p * rationalResidue
      ((∑ a : Fin 3,
        (∑ i : Fin 3, bivJCG bivS i a*finiteNativeJet p bivS i) *
          ((6*(1-bivX)*bivS/bivX)*bivBsDivU a 0-bivBU a 0)) /
        bivS^(p+1)) := by
  unfold actualBetaFunctional
  congr 2
  have hi (i : Fin 3) :
      (((6*(1-bivX)*bivS/bivX)*bivConductorR i 2-bivConductorBU i 2)*
          finiteNativeJet p bivS i)/(1-bivB) =
      (∑ a : Fin 3, bivJCG bivS i a*
        ((6*(1-bivX)*bivS/bivX)*bivBsDivU a 0-bivBU a 0))*
          finiteNativeJet p bivS i := by
    have hsplit (c r u z d : RatFunc (RatFunc ℚ)) :
        (c*r-u)*z/d = (c*(r/d)-u/d)*z := by ring
    rw [hsplit, actual_conductor_last_column, actual_radial_last_column]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    ring
  have hsplit (u d v : RatFunc (RatFunc ℚ)) : u/(d*v)=(u/v)/d := by ring
  rw [hsplit, Finset.sum_div]
  simp only [hi]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  ring

end

end WPForcedSourceStokes
