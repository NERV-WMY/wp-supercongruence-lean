import WPFieldAssembly.ActualBpairGreen
import WPFieldAssembly.ActualBpairKernelSource

set_option maxHeartbeats 1600000

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPFieldAssembly.GreenLaurentOperators WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

/-- This is the whole cleared three-band derivative numerator. -/
noncomputable def kernelDerivativeNumerator (p : ℕ) : K[T;T⁻¹] :=
  (1-T ((p-1 : ℕ) : ℤ))*
    (20*T 1+LaurentPolynomial.C (15/2 : K)+
      (LaurentPolynomial.C (113/2 : K)*T 1+4)*T (-(p : ℤ))+
      (LaurentPolynomial.C (1953/8 : K)*T 1-
        LaurentPolynomial.C (113/2 : K))*T (-2*(p : ℤ)))

/-- The origin calculation consumes the full derivative, including its two negative phases. -/
theorem literalKB_derivative_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (F : K[T;T⁻¹]) :
    (F*D (literalKB (K:=K) p)).coeff (-1)=
      originPole (F*kernelDerivativeNumerator (K:=K) p) := by
  have hd : (WPFiniteZSource.Abar : K[X]).toLaurent *
      D (literalKB (K:=K) p)=kernelDerivativeNumerator (K:=K) p := by
    simpa only [kernelDerivativeNumerator] using
      literalKB_cleared_derivative (K:=K) p hp
  have he : (WPFiniteZSource.Abar : K[X]).toLaurent *
      (F*D (literalKB (K:=K) p))=F*kernelDerivativeNumerator (K:=K) p := by
    linear_combination F*hd
  rw [←he,originPole_cleared p hp]

/-- Integration by parts uses the full original kernel and every signed coefficient. -/
theorem literalKB_D_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (F : K[T;T⁻¹]) :
    (literalKB (K:=K) p*D F).coeff (-1)=
      -originPole (F*kernelDerivativeNumerator (K:=K) p) := by
  have hz : (D (literalKB (K:=K) p*F)).coeff (-1)=0 := by
    rw [D_coeff]
    norm_num
  rw [D_mul,AddMonoidAlgebra.coeff_add,Finsupp.add_apply] at hz
  have ha := literalKB_derivative_origin (K:=K) p hp F
  rw [←ha]
  have hc : D (literalKB (K:=K) p)*F=F*D (literalKB (K:=K) p) := by ring
  rw [hc] at hz
  linear_combination hz

/-- The original native Bpair is transported with its whole period and low-H terms. -/
theorem actual_bpair_whole_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) (h4 : (4 : K)≠0) :
    ActualThreePhase.φ (K:=K) p (NativeScalarRows.nativeBpair p hp)=
      -originPole (ActualGreenResidue.greenPrimitive (K:=K) p u *
        kernelDerivativeNumerator (K:=K) p)+
      originPole (literalKB (K:=K) p *
        (WPFiniteZSource.P p u*(33-12*T 1)+
          8*(T 1-4)*LaurentPolynomial.C
            (ev (1/4) (one_div_ne_zero h4) (WPFiniteZSource.P p u))+
          4*(T 1-LaurentPolynomial.C (1/4 : K))*LaurentPolynomial.C
            (ev 4 h4 (WPFiniteZSource.P p u))))-
      (1/6 : K)*(literalKB (K:=K) p * D (HJetPullK (K:=K) p)).coeff (-1) := by
  rw [actual_bpair_green_origin_source_K p hp u hu h4,
    literalKB_derivative_origin p hp]

/-- One complete origin source retains the actual H jet and both original endpoints. -/
theorem actual_bpair_complete_origin_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) (h4 : (4 : K)≠0) :
    ActualThreePhase.φ (K:=K) p (NativeScalarRows.nativeBpair p hp)=
      originPole
        ((LaurentPolynomial.C (1/6 : K)*HJetPullK (K:=K) p-
            ActualGreenResidue.greenPrimitive (K:=K) p u)*
          kernelDerivativeNumerator (K:=K) p+
          literalKB (K:=K) p *
            (WPFiniteZSource.P p u*(33-12*T 1)+
              8*(T 1-4)*LaurentPolynomial.C
                (ev (1/4) (one_div_ne_zero h4) (WPFiniteZSource.P p u))+
              4*(T 1-LaurentPolynomial.C (1/4 : K))*LaurentPolynomial.C
                (ev 4 h4 (WPFiniteZSource.P p u)))) := by
  rw [actual_bpair_green_literal_source_K p hp u hu,
    literalKB_D_origin p hp,weightedDD_origin p hp h4,
    literalKB_D_origin p hp]
  rw [sub_mul,originPole_add,originPole_sub,
    show (LaurentPolynomial.C (1/6 : K)*HJetPullK (K:=K) p)*
        kernelDerivativeNumerator (K:=K) p=
      LaurentPolynomial.C (1/6 : K)*(HJetPullK (K:=K) p*
        kernelDerivativeNumerator (K:=K) p) by ring,
    originPole_C_mul]
  ring

end WPFieldAssembly.ActualBpairContraction
