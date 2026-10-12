import WPFieldAssembly.SourceClosureConicRatioDescent

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.SourceClosureConicRatioDescent

namespace WPFieldAssembly.SourceClosureLaurentRatioDivision

set_option maxHeartbeats 1600000

/-- A multiple of p clears any finite Laurent source while preserving the ratio equation. -/
theorem conic_laurent_ratio_division {K : Type*} [Field K] (p : ℕ) [CharP K p]
    (hp : 1≤p) (f A y m : K[X]) (M : K[T;T⁻¹]) (hy : y≠0)
    (h2 : (2 : K)≠0) (h3 : (3 : K)≠0) (h4 : (4 : K)≠0) (h5 : (5 : K)≠0)
    (hf : f.comp (5*X^2-1)=y^2)
    (hw : A*(y*m.derivative-y.derivative*m)=1-y^2)
    (hs : f.toLaurent*D M-2*M*D f.toLaurent=0) :
    ∃ R : K[T;T⁻¹], M=f.toLaurent^2*R ∧ D R=0 := by
  obtain ⟨n,Q0,hQ0⟩ := LaurentPolynomial.exists_T_pow M
  let k := p*n
  have hnk : n≤k := by dsimp only [k]; nlinarith
  let Q : K[X] := X^(k-n)*Q0
  have hclear : Q.toLaurent=T (k : ℤ)*M := by
    dsimp only [Q]
    rw [map_mul,Polynomial.toLaurent_X_pow,hQ0]
    have hcast : ((k-n : ℕ) : ℤ)+(n : ℤ)=(k : ℤ) := by omega
    calc
      T ((k-n : ℕ) : ℤ)*(M*T (n : ℤ))=
          (T ((k-n : ℕ) : ℤ)*T (n : ℤ))*M := by ring
      _=T (k : ℤ)*M := by rw [←T_add,hcast]
  have hdk (j : ℤ) (hj : (p : ℤ)∣j) : D (T j : K[T;T⁻¹])=0 := by
    have hc : (j : K)=0 := by
      obtain ⟨a,ha⟩ := hj
      rw [ha,Int.cast_mul,Int.cast_natCast,CharP.cast_eq_zero,zero_mul]
    have hd := D_monomial (K:=K) (1 : K) j
    simpa only [map_one,one_mul,hc,map_zero,zero_mul] using hd
  have hkdiv : (p : ℤ)∣(k : ℤ) := by
    refine ⟨(n : ℤ),?_⟩
    simp only [k,Nat.cast_mul]
  have hkderiv := hdk (k : ℤ) hkdiv
  have hpoly : f*Q.derivative-2*Q*f.derivative=0 := by
    apply Polynomial.toLaurent_injective
    simp only [map_sub,map_mul,map_ofNat,map_zero,←D_toLaurent]
    rw [hclear,D_mul,hkderiv,zero_mul,zero_add]
    linear_combination T (k : ℤ)*hs
  obtain ⟨B,hB,hDB⟩ := actual_conic_ratio_division f Q A y m hy h2 h3 h4 h5 hf hw hpoly
  let R := T (-(k : ℤ))*B.toLaurent
  have hunit : (T (-(k : ℤ))*T (k : ℤ) : K[T;T⁻¹])=1 := by
    rw [←T_add,neg_add_cancel,T_zero]
  have hfactor : M=f.toLaurent^2*R := by
    have he := congrArg (fun P : K[X] => P.toLaurent) hB
    rw [hclear,map_mul,map_pow] at he
    dsimp only [R]
    linear_combination T (-(k : ℤ))*he-M*hunit
  refine ⟨R,hfactor,?_⟩
  have hneg := hdk (-(k : ℤ)) (dvd_neg.mpr hkdiv)
  simp only [R,D_mul,hneg,D_toLaurent,hDB,map_zero,zero_mul,mul_zero,zero_add]

end WPFieldAssembly.SourceClosureLaurentRatioDivision
