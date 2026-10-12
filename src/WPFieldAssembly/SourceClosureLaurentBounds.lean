import WPFiniteLaurentDifferential

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.SourceClosureLaurentBounds

set_option maxHeartbeats 1600000

/-- Exact leading-degree cancellation bounds a whole Laurent quotient, without deleting slots. -/
theorem above_cancel_polynomial {K : Type*} [Field K] (f : K[X]) (hf : f≠0)
    (R : K[T;T⁻¹]) (b : ℤ) (hprod : Above (f.toLaurent*R) b) :
    Above R (b-(f.natDegree : ℤ)) := by
  by_cases hr : R=0
  · intro j _
    rw [hr]
    rfl
  obtain ⟨n,Q,hQ⟩ := LaurentPolynomial.exists_T_pow R
  have hq0 : Q≠0 := by
    intro hz
    have ht : (T (n : ℤ) : K[T;T⁻¹])≠0 := by
      intro hz
      have he := congrArg (fun F : K[T;T⁻¹] => F.coeff (n : ℤ)) hz
      exact one_ne_zero (by
        simpa only [LaurentPolynomial.T_apply,if_true,AddMonoidAlgebra.coeff_zero,
          Finsupp.zero_apply] using he)
    rw [hz,map_zero] at hQ
    exact (mul_ne_zero hr ht) hQ.symm
  have hbound : Above (f*Q).toLaurent (b+(n : ℤ)) := by
    have he := Above_shift hprod (n : ℤ)
    rw [map_mul,hQ]
    convert he using 1 <;> ring
  have hdegree : ((f*Q).natDegree : ℤ)≤b+(n : ℤ) := by
    by_contra hn
    have hz := hbound ((f*Q).natDegree : ℤ) (by omega)
    rw [WPFiniteJCarrier.toLaurent_coeff_nat,coeff_natDegree] at hz
    exact (leadingCoeff_ne_zero.mpr (mul_ne_zero hf hq0)) hz
  rw [natDegree_mul hf hq0,Nat.cast_add] at hdegree
  intro j hj
  have hshift : Q.toLaurent.coeff (j+(n : ℤ))=R.coeff j := by
    rw [hQ,mul_comm]
    have ht := WPFiniteJCarrier.shifted_coeff (1 : K) (n : ℤ) (j+(n : ℤ)) R
    simpa only [map_one,one_mul,add_sub_cancel_right] using ht
  rw [←hshift]
  exact WPFiniteJCarrier.toLaurent_coeff_outside Q _ (Or.inr (by omega))

/-- The strict three-p band leaves exactly five derivative-invisible exponents. -/
theorem derivative_kernel_five_support (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (R : (ZMod p)[T;T⁻¹]) (hD : D R=0)
    (htop : Above R (3*(p : ℤ)-3)) (hbot : Above (invert R) (3*(p : ℤ)-3))
    (j : ℤ) (hj : j≠-2*(p : ℤ) ∧ j≠-(p : ℤ) ∧ j≠0 ∧
      j≠(p : ℤ) ∧ j≠2*(p : ℤ)) : R.coeff j=0 := by
  by_contra hc
  have hd := congrArg (fun L : (ZMod p)[T;T⁻¹] => L.coeff (j-1)) hD
  rw [D_coeff,sub_add_cancel,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] at hd
  have hj0 : (j : ZMod p)=0 := (mul_eq_zero.mp hd).resolve_right hc
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hj0
  obtain ⟨k,hk⟩ := hj0
  have hupper : j≤3*(p : ℤ)-3 := by
    by_contra hn
    exact hc (htop j (by omega))
  have hlower : -3*(p : ℤ)+3≤j := by
    by_contra hn
    have hz := hbot (-j) (by omega)
    rw [invert_apply,neg_neg] at hz
    exact hc hz
  have hkupper : k≤2 := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_left (by omega : 3≤k) (by omega : 0≤(p : ℤ))
    omega
  have hklower : -2≤k := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_left (by omega : k≤-3) (by omega : 0≤(p : ℤ))
    omega
  have hcases : k=-2 ∨ k=-1 ∨ k=0 ∨ k=1 ∨ k=2 := by omega
  rcases hcases with he | he | he | he | he <;> rw [he] at hk <;> omega

/-- All five kernel coefficients are explicit; neither extreme coefficient is assigned a value. -/
theorem derivative_kernel_five_expansion (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (R : (ZMod p)[T;T⁻¹]) (hD : D R=0)
    (htop : Above R (3*(p : ℤ)-3)) (hbot : Above (invert R) (3*(p : ℤ)-3)) :
    R=LaurentPolynomial.C (R.coeff (-2*(p : ℤ)))*T (-2*(p : ℤ))+
      LaurentPolynomial.C (R.coeff (-(p : ℤ)))*T (-(p : ℤ))+
      LaurentPolynomial.C (R.coeff 0)+
      LaurentPolynomial.C (R.coeff (p : ℤ))*T (p : ℤ)+
      LaurentPolynomial.C (R.coeff (2*(p : ℤ)))*T (2*(p : ℤ)) := by
  ext j
  have hpz : 0<(p : ℤ) := by omega
  have hc : R.coeff j=0 ∨ j=-2*(p : ℤ) ∨ j=-(p : ℤ) ∨ j=0 ∨
      j=(p : ℤ) ∨ j=2*(p : ℤ) := by
    by_cases hj : j=-2*(p : ℤ) ∨ j=-(p : ℤ) ∨ j=0 ∨ j=(p : ℤ) ∨ j=2*(p : ℤ)
    · exact Or.inr hj
    · exact Or.inl (derivative_kernel_five_support p hp R hD htop hbot j (by tauto))
  simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,←single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single,Finsupp.single_apply,LaurentPolynomial.C_apply]
  rcases hc with hc | hc | hc | hc | hc | hc
  · split_ifs <;> first | omega | simp_all only [add_zero]
  · subst j
    simp only [if_true,if_neg (by omega : -(p : ℤ)≠-2*(p : ℤ)),
      if_neg (by omega : -2*(p : ℤ)≠0),if_neg (by omega : (p : ℤ)≠-2*(p : ℤ)),
      if_neg (by omega : 2*(p : ℤ)≠-2*(p : ℤ)),add_zero]
  · subst j
    simp only [if_true,if_neg (by omega : -2*(p : ℤ)≠-(p : ℤ)),
      if_neg (by omega : -(p : ℤ)≠0),if_neg (by omega : (p : ℤ)≠-(p : ℤ)),
      if_neg (by omega : 2*(p : ℤ)≠-(p : ℤ)),add_zero,zero_add]
  · subst j
    simp only [if_true,if_neg (by omega : -2*(p : ℤ)≠0),
      if_neg (by omega : -(p : ℤ)≠0),if_neg (by omega : (p : ℤ)≠0),
      if_neg (by omega : 2*(p : ℤ)≠0),add_zero,zero_add]
  · subst j
    simp only [if_true,if_neg (by omega : -2*(p : ℤ)≠(p : ℤ)),
      if_neg (by omega : -(p : ℤ)≠(p : ℤ)),if_neg (by omega : (p : ℤ)≠0),
      if_neg (by omega : 2*(p : ℤ)≠(p : ℤ)),add_zero,zero_add]
  · subst j
    simp only [if_true,if_neg (by omega : -2*(p : ℤ)≠2*(p : ℤ)),
      if_neg (by omega : -(p : ℤ)≠2*(p : ℤ)),if_neg (by omega : 2*(p : ℤ)≠0),
      if_neg (by omega : (p : ℤ)≠2*(p : ℤ)),zero_add]

end WPFieldAssembly.SourceClosureLaurentBounds
