import WPCompletedCartier.ActualRationalizedQuotient

namespace WPCompletedCartier.InverseTraceQuotient

noncomputable section
open WPResidueQuotient WPResidueQuotient.Adic
open WPCompletedCartier.ActualRationalizedQuotient

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

local instance : Module ℚ_[p] (RationalizedCartier.Rationalized p hp) :=
  QpExtension.qpModule p hp
local instance : Module ℚ_[p] (RationalizedQuotient p hp) := quotientQpModule p hp

/-- The actual finite image identity is projected to the actual rationalized
strict quotient. Its tail is the constructed factorial-convergent tail. -/
theorem cartier_finitePullbackQuotient (N : ℕ) (hN : 1 ≤ N) (r : Fin 5) :
    cartierQuotientQp p hp hp7 hp19 (finitePullbackQuotient p hp N r) =
      quotientProjection p hp (RationalizedCartier.integralMap p hp
        (ofModule (p : ℤ_[p]) (InverseTraceImage.headTerm p hp r) +
          InverseTraceTail.tail p hp N hN r)) := by
  let x : RationalizedCartier.Rationalized p hp :=
    InverseTraceConstruction.finitePullback p hp N r
  have h : quotientProjection p hp (QpExtension.cartierQp p hp x) =
      cartierQuotientQp p hp hp7 hp19 (quotientProjection p hp x) :=
    DFunLike.congr_fun (quotientProjection_intertwines p hp hp7 hp19) x
  have hi : QpExtension.cartierQp p hp x =
      RationalizedCartier.integralMap p hp
        (ofModule (p : ℤ_[p]) (InverseTraceImage.headTerm p hp r) +
          InverseTraceTail.tail p hp N hN r) :=
    (QpExtension.cartierQp_apply p hp x).trans
      (InverseTraceConstruction.cartier_finitePullback p hp N hN r)
  exact h.symm.trans (congrArg (quotientProjection p hp) hi)

theorem scaled_finitePullback (N : ℕ) (r : Fin 5) :
    (p : ℚ_[p]) ^ 5 • InverseTraceConstruction.finitePullback p hp N r =
      algebraMap ℤ_[p] (RationalizedCartier.Coeff p) ((p : ℤ_[p]) ^ 5) •
        InverseTraceConstruction.finitePullback p hp N r := by
  calc
    _ = (((p : ℤ_[p]) ^ 5 : ℤ_[p]) : ℚ_[p]) •
        InverseTraceConstruction.finitePullback p hp N r := by
      simp only [PadicInt.coe_pow, PadicInt.coe_natCast]
    _ = ((p : ℤ_[p]) ^ 5) • InverseTraceConstruction.finitePullback p hp N r :=
      QpExtension.qp_smul_integral p hp _ _
    _ = _ := (IsScalarTower.algebraMap_smul (RationalizedCartier.Coeff p)
      ((p : ℤ_[p]) ^ 5) (InverseTraceConstruction.finitePullback p hp N r)).symm

/-- No independently constructed Frobenius is needed for this finite-sum
image limit. The coordinates are an equivalence of the actual quotient. -/
theorem actual_quotient_inverse_trace_limit (r : Fin 5) :
    Filter.Tendsto
      (fun N => rawQuotientEquiv p hp hp7 hp19
        (cartierQuotientQp p hp hp7 hp19
          ((p : ℚ_[p]) ^ 5 • finitePullbackQuotient p hp (N + 1) r)))
      Filter.atTop (nhds ((p : ℚ_[p]) ^ 5 • Pi.single r (1 : ℚ_[p]))) := by
  have he (N : ℕ) :
      rawQuotientEquiv p hp hp7 hp19
        (cartierQuotientQp p hp hp7 hp19
          ((p : ℚ_[p]) ^ 5 • finitePullbackQuotient p hp (N + 1) r)) =
      InverseTraceCoordinates.rationalizedProjection p hp hp7 hp19
        (RationalizedCartier.cartier p hp
          (algebraMap ℤ_[p] (RationalizedCartier.Coeff p) ((p : ℤ_[p]) ^ 5) •
            InverseTraceConstruction.finitePullback p hp (N + 1) r)) := by
    let x : RationalizedCartier.Rationalized p hp :=
      InverseTraceConstruction.finitePullback p hp (N + 1) r
    have h : quotientProjection p hp
        (QpExtension.cartierQp p hp ((p : ℚ_[p]) ^ 5 • x)) =
        cartierQuotientQp p hp hp7 hp19
          (quotientProjection p hp ((p : ℚ_[p]) ^ 5 • x)) :=
      DFunLike.congr_fun (quotientProjection_intertwines p hp hp7 hp19)
        ((p : ℚ_[p]) ^ 5 • x)
    have hs := (quotientProjection p hp).map_smul ((p : ℚ_[p]) ^ 5) x
    have himage := (congrArg (cartierQuotientQp p hp hp7 hp19) hs.symm).trans h.symm
    have hraw := rawQuotientProjection_apply p hp hp7 hp19
      (QpExtension.cartierQp p hp ((p : ℚ_[p]) ^ 5 • x))
    have hscaled : QpExtension.cartierQp p hp ((p : ℚ_[p]) ^ 5 • x) =
        RationalizedCartier.cartier p hp
          (algebraMap ℤ_[p] (RationalizedCartier.Coeff p) ((p : ℤ_[p]) ^ 5) • x) :=
      (QpExtension.cartierQp_apply p hp ((p : ℚ_[p]) ^ 5 • x)).trans
        (congrArg (RationalizedCartier.cartier p hp)
          (scaled_finitePullback p hp (N + 1) r))
    exact (congrArg (rawQuotientEquiv p hp hp7 hp19) himage).trans
      (hraw.trans (congrArg (InverseTraceCoordinates.rationalizedProjection p hp hp7 hp19)
        hscaled))
  simpa only [he] using InverseTraceCoordinates.actual_inverse_trace_limit p hp hp7 hp19 r

end
end WPCompletedCartier.InverseTraceQuotient
