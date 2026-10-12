import WPFieldAssembly.ActualBpairMetricAttachment

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial
open WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 2400000

/-- The complete original Z52 block has exactly the five quadratic residue terms.
The discarded correction is a polynomial at the original origin. -/
theorem actual_Z52_quadratic_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) (c : K) :
    originPole ((LaurentPolynomial.C (33 : K)-LaurentPolynomial.C (12 : K)*T 1)*
      (LaurentPolynomial.C (5/24 : K)*T (p : ℤ)*actualZ52 p u+
        LaurentPolynomial.C (2/3 : K)*(Dstar p : K[X]).toLaurent*
          (invert (actualAK p : K[X]).toLaurent-LaurentPolynomial.C c)))=
    originPole ((LaurentPolynomial.C (33 : K)-LaurentPolynomial.C (12 : K)*T 1)*
      ((LaurentPolynomial.C (5/3 : K)-LaurentPolynomial.C (11/4 : K)*T (p : ℤ))*
          invert (actualAK p : K[X]).toLaurent*(Dstar p : K[X]).toLaurent+
        (1-LaurentPolynomial.C (11/4 : K)*T (p : ℤ))*
          invert (actualAK p : K[X]).toLaurent*invert (Dstar p : K[X]).toLaurent-
        LaurentPolynomial.C (5/24 : K)*T (p : ℤ)*
          (invert (actualAK p : K[X]).toLaurent)^2)) := by
  let A := (actualAK p : K[X]).toLaurent
  let v := invert A
  let d := (Dstar p : K[X]).toLaurent
  let Xp : K[T;T⁻¹] := T (p : ℤ)
  let ph : K[T;T⁻¹] := 4*T (-(p : ℤ))-11
  let den := LaurentPolynomial.C (33 : K)-LaurentPolynomial.C (12 : K)*T 1
  let P : K[X] := (Polynomial.C 33-Polynomial.C 12*X)*
    (Polynomial.C (5/24 : K)*X^p*(actualAK p)^2-
      Polynomial.C (2/3 : K)*Dstar p*Polynomial.C c)
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := by
    convert pow_ne_zero 2 h2 using 1; norm_num
  have h24 : (24 : K)≠0 := by
    convert mul_ne_zero (pow_ne_zero 3 h2) h3 using 1; norm_num
  have hc1 : LaurentPolynomial.C (5/24 : K)*LaurentPolynomial.C (6/5 : K)=
      LaurentPolynomial.C (1/4 : K) := by
    rw [←map_mul]
    congr 1
    field_simp [h4,h5,h24]
    ring
  have hc4 : LaurentPolynomial.C (1/4 : K)*4=1 := by
    have hs : (1/4 : K)*4=1 := by field_simp [h4]
    simpa only [map_mul,map_ofNat,map_one] using
      congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hs
  have hc11 : LaurentPolynomial.C (1/4 : K)*11=LaurentPolynomial.C (11/4 : K) := by
    have hs : (1/4 : K)*11=11/4 := by ring
    simpa only [map_mul,map_ofNat] using
      congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hs
  have hc3 : LaurentPolynomial.C (2/3 : K)+1=LaurentPolynomial.C (5/3 : K) := by
    have hs : (2/3 : K)+1=5/3 := by
      field_simp [h3]
      ring
    simpa only [map_add,map_one] using
      congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hs
  have hphase : Xp*ph=4-11*Xp := by
    have ht : Xp*T (-(p : ℤ))=1 := by
      dsimp only [Xp]
      rw [←T_add,add_neg_cancel,T_zero]
    dsimp only [ph]
    linear_combination 4*ht
  have hP : P.toLaurent=den*(LaurentPolynomial.C (5/24 : K)*Xp*A^2-
      LaurentPolynomial.C (2/3 : K)*d*LaurentPolynomial.C c) := by
    simp only [P,den,Xp,A,d,map_mul,map_sub,map_pow,Polynomial.toLaurent_C,
      Polynomial.toLaurent_X,T_pow,mul_one]
  rw [actual_Z52_NC123a p hp u hu]
  change originPole (den*(LaurentPolynomial.C (5/24 : K)*Xp*
      (A^2-v^2+LaurentPolynomial.C (6/5 : K)*ph*v*(d+invert d))+
        LaurentPolynomial.C (2/3 : K)*d*(v-LaurentPolynomial.C c)))=_
  have he : den*(LaurentPolynomial.C (5/24 : K)*Xp*
      (A^2-v^2+LaurentPolynomial.C (6/5 : K)*ph*v*(d+invert d))+
        LaurentPolynomial.C (2/3 : K)*d*(v-LaurentPolynomial.C c))=
      den*((LaurentPolynomial.C (5/3 : K)-LaurentPolynomial.C (11/4 : K)*Xp)*v*d+
        (1-LaurentPolynomial.C (11/4 : K)*Xp)*v*invert d-
        LaurentPolynomial.C (5/24 : K)*Xp*v^2)+P.toLaurent := by
    rw [hP]
    linear_combination den*v*(d+invert d)*
      ((Xp*ph)*hc1+LaurentPolynomial.C (1/4 : K)*hphase+hc4-Xp*hc11)+den*v*d*hc3
  rw [he,originPole_add,originPole_polynomial,add_zero]

/-- Both original R52 halves are kept until the regular polynomial part is removed. -/
theorem actual_R52_metric_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (c : K) :
    originPole (WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*
      (LaurentPolynomial.C (5*WPFiniteNC122.h p/4 : K)*T (p : ℤ)*actualR52 p-
        LaurentPolynomial.C (10*WPFiniteNC122.h p/3 : K)*
          (invert (actualAK p : K[X]).toLaurent-LaurentPolynomial.C c)))=
      actualNativeMetric (K:=K) p := by
  let h : K := WPFiniteNC122.h p
  let A := (actualAK p : K[X]).toLaurent
  let v := invert A
  let Xp : K[T;T⁻¹] := T (p : ℤ)
  let ph : K[T;T⁻¹] := 4*T (-(p : ℤ))-11
  let s := (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent^((p-1)/2)
  let P : K[X] := WPFiniteWSource.squaredCoordinate^((p-1)/2)*
    (-Polynomial.C (5*h/4)*X^p*(Polynomial.C 4*X^p-Polynomial.C 11)*actualAK p+
      Polynomial.C (10*h/3)*Polynomial.C c)
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hc4 : LaurentPolynomial.C (5*h/4)*4+LaurentPolynomial.C (10*h/3)=
      LaurentPolynomial.C h*LaurentPolynomial.C (25/3 : K) := by
    have hs : (5*h/4)*4+10*h/3=h*(25/3) := by
      field_simp [h3,h4]
      ring
    simpa only [map_add,map_mul,map_ofNat] using
      congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hs
  have hc11 : LaurentPolynomial.C (5*h/4)*11=
      LaurentPolynomial.C h*LaurentPolynomial.C (55/4 : K) := by
    have hs : (5*h/4)*11=h*(55/4) := by ring
    simpa only [map_mul,map_ofNat] using
      congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hs
  have hphase : Xp*ph=4-11*Xp := by
    have ht : Xp*T (-(p : ℤ))=1 := by
      dsimp only [Xp]
      rw [←T_add,add_neg_cancel,T_zero]
    dsimp only [ph]
    linear_combination 4*ht
  have hP : P.toLaurent=s*(-LaurentPolynomial.C (5*h/4)*Xp*(4*Xp-11)*A+
      LaurentPolynomial.C (10*h/3)*LaurentPolynomial.C c) := by
    simp only [P,s,Xp,A,map_mul,map_add,map_sub,map_neg,map_pow,
      Polynomial.toLaurent_C,Polynomial.toLaurent_X,T_pow,mul_one,map_ofNat]
  change originPole (s*(LaurentPolynomial.C (5*h/4)*Xp*(-ph*v-(4*Xp-11)*A)-
      LaurentPolynomial.C (10*h/3)*(v-LaurentPolynomial.C c)))=_
  have he : s*(LaurentPolynomial.C (5*h/4)*Xp*(-ph*v-(4*Xp-11)*A)-
      LaurentPolynomial.C (10*h/3)*(v-LaurentPolynomial.C c))=
      LaurentPolynomial.C (-h)*(s*(LaurentPolynomial.C (25/3 : K)-
        LaurentPolynomial.C (55/4 : K)*Xp)*v)+P.toLaurent := by
    rw [hP,map_neg]
    linear_combination -s*v*(LaurentPolynomial.C (5*h/4)*hphase+hc4-Xp*hc11)
  rw [he,originPole_add,originPole_polynomial,add_zero,originPole_C_mul]
  rfl

/-- The phase-scaled original Z52 is exactly the quadratic part of the actual pure norm source. -/
theorem actual_Z52_pure_quadratic_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    LaurentPolynomial.C (5/24 : K)*T (p : ℤ)*actualZ52 p u=
      LaurentPolynomial.C (5/24 : K)*T (p : ℤ)*
        ((actualAK p : K[X]).toLaurent^2-(invert (actualAK p : K[X]).toLaurent)^2)+
      LaurentPolynomial.C (1/4 : K)*(4-11*T (p : ℤ))*
        invert (actualAK p : K[X]).toLaurent*Dsym p := by
  let A := (actualAK p : K[X]).toLaurent
  let v := invert A
  let ph : K[T;T⁻¹] := 4*T (-(p : ℤ))-11
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : K)≠0 := WPFiniteField.denominator_ne_zero p 6
    (Finset.mem_Ico.mpr (by omega))
  have h24 : (24 : K)≠0 := by
    rw [show (24 : K)=4*6 by norm_num]
    exact mul_ne_zero h4 h6
  have hc : (5/24 : K)*(6/5)=1/4 := by
    field_simp [h4,h5,h24]
    ring
  have hC := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc
  rw [map_mul] at hC
  have ht : (T (p : ℤ)*T (-(p : ℤ)) : K[T;T⁻¹])=1 := by
    rw [←T_add,add_neg_cancel,T_zero]
  have hphase : T (p : ℤ)*ph=4-11*T (p : ℤ) := by
    dsimp only [ph]
    linear_combination 4*ht
  rw [actual_Z52_NC123a p hp u hu]
  change LaurentPolynomial.C (5/24 : K)*T (p : ℤ)*
      (A^2-v^2+LaurentPolynomial.C (6/5 : K)*ph*v*Dsym p)=
    LaurentPolynomial.C (5/24 : K)*T (p : ℤ)*(A^2-v^2)+
      LaurentPolynomial.C (1/4 : K)*(4-11*T (p : ℤ))*v*Dsym p
  linear_combination (T (p : ℤ)*ph*v*Dsym p)*hC+
    (LaurentPolynomial.C (1/4 : K)*v*Dsym p)*hphase

end WPFieldAssembly.ActualBpairContraction
