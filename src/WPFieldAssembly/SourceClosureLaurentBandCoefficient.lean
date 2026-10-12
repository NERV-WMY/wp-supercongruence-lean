import WPFiniteLaurentDifferential

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.SourceClosureLaurentBandCoefficient

set_option maxHeartbeats 800000

/-- Disjoint polynomial bands isolate the original positive extreme coefficient. -/
theorem polynomial_three_band_top {K : Type*} [Field K]
    (F : K[X]) (p : ℕ) (hdegree : F.natDegree<p)
    (R : K[T;T⁻¹]) (c0 c1 c2 : K)
    (hR : R=LaurentPolynomial.C c0+LaurentPolynomial.C c1*(T (p : ℤ)+T (-(p : ℤ)))+
      LaurentPolynomial.C c2*(T (2*(p : ℤ))+T (-2*(p : ℤ)))) :
    (F.toLaurent*R).coeff (2*(p : ℤ)+(F.natDegree : ℤ))=
      c2*F.leadingCoeff := by
  have he : F.toLaurent*R=
      LaurentPolynomial.C c0*T 0*F.toLaurent+
        LaurentPolynomial.C c1*T (p : ℤ)*F.toLaurent+
        LaurentPolynomial.C c1*T (-(p : ℤ))*F.toLaurent+
        LaurentPolynomial.C c2*T (2*(p : ℤ))*F.toLaurent+
        LaurentPolynomial.C c2*T (-2*(p : ℤ))*F.toLaurent := by
    rw [hR,T_zero]
    ring
  rw [he]
  simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,WPFiniteJCarrier.shifted_coeff]
  have h0 : F.toLaurent.coeff (2*(p : ℤ)+(F.natDegree : ℤ)-0)=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside F _ (Or.inr (by omega))
  have h1 : F.toLaurent.coeff (2*(p : ℤ)+(F.natDegree : ℤ)-(p : ℤ))=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside F _ (Or.inr (by omega))
  have hm1 : F.toLaurent.coeff (2*(p : ℤ)+(F.natDegree : ℤ)-(-(p : ℤ)))=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside F _ (Or.inr (by omega))
  have hm2 : F.toLaurent.coeff (2*(p : ℤ)+(F.natDegree : ℤ)-(-2*(p : ℤ)))=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside F _ (Or.inr (by omega))
  rw [h0,h1,hm1,hm2,
    show 2*(p : ℤ)+(F.natDegree : ℤ)-2*(p : ℤ)=(F.natDegree : ℤ) by omega,
    WPFiniteJCarrier.toLaurent_coeff_nat,coeff_natDegree]
  ring

end WPFieldAssembly.SourceClosureLaurentBandCoefficient
