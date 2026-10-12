import WPFiniteJWeightedResidue
import WPFiniteLaurentDifferential

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteJCarrier WPFiniteJWeightedResidue
  WPFiniteLaurentDifferential

namespace WPFieldAssembly.SourceClosureVbalCrossTruncation

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

/-- The full shifted carrier is its positive polynomial once the inverse support is strict. -/
theorem shifted_carrier_is_trunc (F : K[T;T⁻¹]) (N : ℕ) (L : ℤ)
    (hinv : Above (invert F) L) (hLN : L<(N : ℤ)) :
    (trunc (T (N : ℤ)*F)).toLaurent=T (N : ℤ)*F := by
  ext j
  by_cases hj : j<0
  · rw [toLaurent_coeff_outside _ j (Or.inl hj)]
    have hs := shifted_coeff (1 : K) (N : ℤ) j F
    simp only [map_one,one_mul] at hs
    rw [hs]
    have hz := hinv ((N : ℤ)-j) (by omega)
    simpa only [invert_apply,show -((N : ℤ)-j)=j-(N : ℤ) by ring] using hz.symm
  · have hjnat : (j.toNat : ℤ)=j := Int.toNat_of_nonneg (by omega)
    rw [←hjnat,toLaurent_coeff_nat,trunc_coeff]

/-- A strictly negative carrier has no polynomial truncation, including its constant slot. -/
theorem strictly_negative_trunc (F : K[T;T⁻¹]) (hF : Above F (-1)) :
    trunc F=0 := by
  ext n
  rw [trunc_coeff,coeff_zero]
  exact hF (n : ℤ) (by omega)

/-- Every original signed phase is retained before the strict support projection. -/
noncomputable def crossFourPhase (p N : ℕ) : K[T;T⁻¹] :=
  LaurentPolynomial.C (1/250 : K)*
    (-LaurentPolynomial.C (44 : K)*T ((p : ℤ)+(N : ℤ))+
      LaurentPolynomial.C (93 : K)*T (N : ℤ)+
      LaurentPolynomial.C (93 : K)*T (-(N : ℤ)-1)-
      LaurentPolynomial.C (44 : K)*T (-(p : ℤ)-(N : ℤ)-1))

/-- Only the two upper phases survive after both actual support bounds have been supplied. -/
theorem cross_four_phase_trunc (p N : ℕ) (F : K[T;T⁻¹]) (L : ℤ)
    (hF : Above F (-1)) (hinv : Above (invert F) L) (hLN : L<(N : ℤ)) :
    trunc (crossFourPhase (K:=K) p N*F)=
      Polynomial.C (1/250 : K)*(93-44*X^p)*trunc (T (N : ℤ)*F) := by
  let P := trunc (T (N : ℤ)*F)
  have hP : P.toLaurent=T (N : ℤ)*F := shifted_carrier_is_trunc F N L hinv hLN
  have hhigh : T ((p : ℤ)+(N : ℤ))*F=(X^p*P).toLaurent := by
    rw [map_mul,Polynomial.toLaurent_X_pow,hP,←mul_assoc,←T_add]
  have hneg1 : trunc (T (-(N : ℤ)-1)*F)=0 := by
    apply strictly_negative_trunc
    exact Above_mono (Above_shift hF (-(N : ℤ)-1)) (by omega)
  have hneg2 : trunc (T (-(p : ℤ)-(N : ℤ)-1)*F)=0 := by
    apply strictly_negative_trunc
    exact Above_mono (Above_shift hF (-(p : ℤ)-(N : ℤ)-1)) (by omega)
  have hwhole : crossFourPhase (K:=K) p N*F=
      LaurentPolynomial.C (1/250 : K)*
        (-LaurentPolynomial.C (44 : K)*(X^p*P).toLaurent+
          LaurentPolynomial.C (93 : K)*P.toLaurent+
          LaurentPolynomial.C (93 : K)*(T (-(N : ℤ)-1)*F)-
          LaurentPolynomial.C (44 : K)*(T (-(p : ℤ)-(N : ℤ)-1)*F)) := by
    rw [hP,←hhigh]
    dsimp only [crossFourPhase]
    ring
  rw [hwhole]
  change _=Polynomial.C (1/250 : K)*(93-44*X^p)*P
  simp only [neg_mul,trunc_C_mul,map_add,map_sub,map_neg,trunc_toLaurent,hneg1,hneg2,
    mul_zero,add_zero,sub_zero]
  simp only [C_ofNat]
  ring

end WPFieldAssembly.SourceClosureVbalCrossTruncation
