import WPFieldAssembly.ActualKwFieldTrace
import WPFiniteEntropy

open scoped Polynomial LaurentPolynomial BigOperators
open LaurentPolynomial

namespace WPFieldAssembly.ActualKwWeightedTrace

set_option maxHeartbeats 1600000

section Endpoint
variable {K : Type*} [CommRing K]

/-- The endpoint coefficient keeps the signed Laurent support. -/
noncomputable def endpointWeight (a b : K) (n : ℤ) : K :=
  if 0<n then -(2*b^n.toNat+a^n.toNat) else 0

noncomputable def endpointTrace (a b : K) : K[T;T⁻¹] →ₗ[K] K :=
  (Finsupp.linearCombination K (endpointWeight a b)).comp
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

@[simp] theorem endpointTrace_monomial (a b d : K) (n : ℤ) :
    endpointTrace a b (C d*T n)=d*endpointWeight a b n := by
  rw [←single_eq_C_mul_T]
  change Finsupp.linearCombination K _ (Finsupp.single n d)=_
  rw [Finsupp.linearCombination_single,smul_eq_mul]

theorem endpointTrace_C_mul (a b d : K) (L : K[T;T⁻¹]) :
    endpointTrace a b (C d*L)=d*endpointTrace a b L := by
  simpa only [smul_eq_C_mul,smul_eq_mul] using (endpointTrace a b).map_smul d L

theorem endpointWeight_nonpositive (a b : K) (n : ℤ) (hn : n≤0) :
    endpointWeight a b n=0 := by simp [endpointWeight,show ¬0<n by omega]

theorem endpointWeight_nat (a b : K) (n : ℕ) :
    endpointWeight a b n = if n=0 then 0 else -(2*b^n+a^n) := by
  by_cases hn : n=0
  · simp [hn,endpointWeight]
  · rw [endpointWeight,if_pos (by omega),if_neg hn,Int.toNat_natCast]

theorem endpointTrace_polynomial (a b : K) (E : K[X]) :
    endpointTrace a b E.toLaurent = -2*E.eval b-E.eval a+3*E.coeff 0 := by
  induction E using Polynomial.induction_on' with
  | add E F hE hF =>
    rw [map_add,map_add,hE,hF,Polynomial.eval_add,Polynomial.eval_add,Polynomial.coeff_add]
    ring
  | monomial n d =>
    rw [←Polynomial.C_mul_X_pow_eq_monomial,Polynomial.toLaurent_C_mul_X_pow,
      endpointTrace_monomial,endpointWeight_nat]
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow]
    by_cases hn : n=0
    · subst n
      simp
      ring
    · rw [if_neg hn,if_neg (Ne.symm hn)]
      ring

theorem endpointTrace_inverted_polynomial (a b : K) (E : K[X]) :
    endpointTrace a b (invert E.toLaurent)=0 := by
  induction E using Polynomial.induction_on' with
  | add E F hE hF => simp only [map_add,hE,hF,add_zero]
  | monomial n d =>
    rw [←Polynomial.C_mul_X_pow_eq_monomial,Polynomial.toLaurent_C_mul_X_pow,
      map_mul,invert_C,invert_T,endpointTrace_monomial,
      endpointWeight_nonpositive a b _ (by omega),mul_zero]

end Endpoint

/-- The original cleared numerator of dlogQ over the literal Abar. -/
noncomputable def rationalDlogQ : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ :=
  (LaurentPoleTrace.trace 1).comp
    ({ toFun := fun L => 3*T (-1)*(4-11*T 1)*L
       map_add' := by intro L M; ring
       map_smul' := by
         intro a L
         simp only [smul_eq_C_mul,RingHom.id_apply]
         ring } : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ[T;T⁻¹])

theorem literal_density_monomial {K : Type*} [CommRing K] (d : K) (n : ℤ) :
    3*T (-1)*(4-11*T 1)*(C d*T n : K[T;T⁻¹])=
      C (12*d)*T (n-1)-C (33*d)*T n := by
  have ht : (T (-1) : K[T;T⁻¹])*T n=T (n-1) := by
    rw [←T_add]
    congr 1
    omega
  have h1 : (T (-1) : K[T;T⁻¹])*T 1=1 := by rw [←T_add]; norm_num
  simp only [map_mul,map_ofNat]
  calc
    _ = 12*C d*(T (-1)*T n)-33*C d*((T (-1)*T 1)*T n) := by ring
    _ = _ := by rw [ht,h1,one_mul]

theorem rationalDlogQ_monomial (d : ℚ) (n : ℤ) :
    rationalDlogQ (C d*T n)=d*endpointWeight (1/4 : ℚ) 4 n := by
  change LaurentPoleTrace.trace 1 (3*T (-1)*(4-11*T 1)*(C d*T n))=_
  rw [literal_density_monomial,map_sub,LaurentPoleTrace.trace_monomial,
    LaurentPoleTrace.trace_monomial]
  by_cases hn : 0<n
  · have hk : n.toNat=n.toNat-1+1 := by omega
    have he : ((n.toNat-1 : ℕ) : ℤ)=n-1 := by omega
    have he' : (n.toNat : ℤ)=n := Int.toNat_of_nonneg (by omega)
    have hw1 := LaurentPoleTrace.weight_one_nat (n.toNat-1)
    have hw0 := LaurentPoleTrace.weight_one_nat n.toNat
    rw [he] at hw1
    rw [he'] at hw0
    rw [hw1,hw0]
    simp only [endpointWeight,if_pos hn]
    have ha : (1/4 : ℚ)^n.toNat=(1/4 : ℚ)^(n.toNat-1)*(1/4) := by
      conv_lhs => rw [hk,pow_succ]
    have hb : (4 : ℚ)^n.toNat=(4 : ℚ)^(n.toNat-1)*4 := by
      conv_lhs => rw [hk,pow_succ]
    rw [ha,hb]
    ring
  · rw [LaurentPoleTrace.weight_support 1 (n-1) (by omega),
      LaurentPoleTrace.weight_support 1 n (by omega),
      endpointWeight_nonpositive _ _ n (by omega)]
    ring

theorem rationalDlogQ_endpoint (L : ℚ[T;T⁻¹]) :
    rationalDlogQ L=endpointTrace (1/4 : ℚ) 4 L := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM => rw [map_add,map_add,hL,hM]
  | C_mul_T n d => rw [rationalDlogQ_monomial,endpointTrace_monomial]

noncomputable def fieldDlogQ (p : ℕ) [Fact p.Prime] :
    (ZMod p)[T;T⁻¹] →ₗ[ZMod p] ZMod p :=
  (LaurentPoleField.fieldTrace p 1).comp
    ({ toFun := fun L => 3*T (-1)*(4-11*T 1)*L
       map_add' := by intro L M; ring
       map_smul' := by
         intro a L
         simp only [smul_eq_C_mul,RingHom.id_apply]
         ring } : (ZMod p)[T;T⁻¹] →ₗ[ZMod p] (ZMod p)[T;T⁻¹])

theorem fieldWeight_one_nat (p n : ℕ) [Fact p.Prime] (hp : 19≤p) :
    LaurentPoleField.fieldWeight p 1 (n : ℤ) =
      -((1/4 : ZMod p)^n-4^n)/15 := by
  have h4 : (4 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  cases n with
  | zero => norm_num [LaurentPoleField.fieldWeight,LaurentPoleField.fieldZcoeff]
  | succ n =>
    have he : ((n+1 : ℕ) : ℤ)-1=(n : ℤ) := by omega
    simp only [LaurentPoleField.fieldWeight,pow_one,Nat.cast_one]
    change -(-1/4 : ZMod p)*LaurentPoleField.fieldZcoeff p
      (((n+1 : ℕ) : ℤ)-1) (LaurentPoleField.fieldReciprocal p)=_
    rw [he]
    simp only [LaurentPoleField.fieldZcoeff,Int.natCast_nonneg,if_pos,
      Int.toNat_natCast,LaurentPoleField.fieldReciprocal,PowerSeries.coeff_mk]
    field_simp [h4,h15]
    ring

theorem fieldWeight_one_nonpositive (p : ℕ) [Fact p.Prime] (n : ℤ) (hn : n≤0) :
    LaurentPoleField.fieldWeight p 1 n=0 := by
  rw [LaurentPoleField.fieldWeight,LaurentPoleField.fieldZcoeff,if_neg (by omega)]
  simp

theorem fieldDlogQ_monomial (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (d : ZMod p) (n : ℤ) :
    fieldDlogQ p (C d*T n)=d*endpointWeight (1/4 : ZMod p) 4 n := by
  change LaurentPoleField.fieldTrace p 1 (3*T (-1)*(4-11*T 1)*(C d*T n))=_
  rw [literal_density_monomial,map_sub,LaurentPoleField.fieldTrace_monomial,
    LaurentPoleField.fieldTrace_monomial]
  by_cases hn : 0<n
  · have hk : n.toNat=n.toNat-1+1 := by omega
    have he : ((n.toNat-1 : ℕ) : ℤ)=n-1 := by omega
    have he' : (n.toNat : ℤ)=n := Int.toNat_of_nonneg (by omega)
    have hw1 := fieldWeight_one_nat p (n.toNat-1) hp
    have hw0 := fieldWeight_one_nat p n.toNat hp
    rw [he] at hw1
    rw [he'] at hw0
    rw [hw1,hw0]
    simp only [endpointWeight,if_pos hn]
    have ha : (1/4 : ZMod p)^n.toNat=(1/4 : ZMod p)^(n.toNat-1)*(1/4) := by
      conv_lhs => rw [hk,pow_succ]
    have hb : (4 : ZMod p)^n.toNat=(4 : ZMod p)^(n.toNat-1)*4 := by
      conv_lhs => rw [hk,pow_succ]
    rw [ha,hb]
    have h4 : (4 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
      (Finset.mem_Ico.mpr (by omega))
    have h15 : (15 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
      (Finset.mem_Ico.mpr (by omega))
    field_simp [h4,h15]
    ring
  · rw [fieldWeight_one_nonpositive p (n-1) (by omega),
      fieldWeight_one_nonpositive p n (by omega),
      endpointWeight_nonpositive _ _ n (by omega)]
    ring

theorem fieldDlogQ_endpoint (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (L : (ZMod p)[T;T⁻¹]) : fieldDlogQ p L=endpointTrace (1/4 : ZMod p) 4 L := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM => rw [map_add,map_add,hL,hM]
  | C_mul_T n d => rw [fieldDlogQ_monomial p hp,endpointTrace_monomial]

section FiniteBands
variable {K : Type*} [Field K]

noncomputable def negativeLog (p : ℕ) (z : K) : K[T;T⁻¹] :=
  ∑ j ∈ Finset.Ico 1 p, C (z^j/(j : K))*T (-(j : ℤ))

noncomputable def positiveLog (p : ℕ) (z : K) : K[T;T⁻¹] :=
  ∑ j ∈ Finset.Ico 1 p, C (z^j/(j : K))*T (j : ℤ)

noncomputable def finiteLogValue (p : ℕ) (z : K) : K :=
  ∑ j ∈ Finset.Ico 1 p, z^j/(j : K)

/-- The triangle includes its entire diagonal k=n. -/
noncomputable def triangle (n : ℕ) (y z : K) : K :=
  ∑ k ∈ Finset.Ico 1 (n+1), z^k*y^(n-k)/(k : K)

noncomputable def finiteH (N : ℕ) (e : ℕ → K) (y z : K) : K :=
  ∑ n ∈ Finset.range (N+1), e n*triangle n y z

theorem triangle_zero (z : K) : triangle 0 (0 : K) z=0 := by
  simp [triangle]

theorem triangle_diagonal (n : ℕ) (z : K) :
    triangle n (0 : K) z = if n=0 then 0 else z^n/(n : K) := by
  by_cases hn : n=0
  · simp [hn,triangle]
  · unfold triangle
    rw [Finset.sum_eq_single n]
    · simp [hn]
    · intro j hj hjn
      have hjle := (Finset.mem_Ico.mp hj).2
      simp [zero_pow (by omega : n-j≠0)]
    · intro hnot
      exact False.elim (hnot (Finset.mem_Ico.mpr (by omega)))

theorem finiteH_diagonal (N : ℕ) (e : ℕ → K) (z : K) :
    finiteH N e 0 z =
      ∑ n ∈ Finset.range (N+1), e n*(if n=0 then 0 else z^n/(n : K)) := by
  simp only [finiteH,triangle_diagonal]

theorem endpointWeight_negative_band (a b : K) (n j : ℕ) :
    endpointWeight a b ((n : ℤ)-j) =
      if j≤n then -(2*b^(n-j)+a^(n-j))+3*(0 : K)^(n-j) else 0 := by
  by_cases hj : j<n
  · have hs : ((n : ℤ)-j).toNat=n-j := by omega
    rw [endpointWeight,if_pos (by omega),if_pos (by omega),hs,
      zero_pow (by omega : n-j≠0)]
    ring
  · by_cases he : j=n
    · subst j
      norm_num [endpointWeight]
    · rw [endpointWeight_nonpositive _ _ _ (by omega),if_neg (by omega)]

theorem negativeLog_trace_monomial (p n : ℕ) (hn : n<p) (a b z : K) :
    endpointTrace a b (T (n : ℤ)*negativeLog p z) =
      -2*triangle n b z-triangle n a z+3*triangle n 0 z := by
  have ht : ∀ j : ℕ, (T (n : ℤ) : K[T;T⁻¹])*
      (C (z^j/(j : K))*T (-(j : ℤ)))=C (z^j/(j : K))*T ((n : ℤ)-j) := by
    intro j
    rw [mul_comm (T (n : ℤ)),mul_assoc,←T_add]
    congr 2
    omega
  rw [negativeLog,Finset.mul_sum,map_sum]
  simp only [ht,endpointTrace_monomial]
  have hsub : Finset.Ico 1 (n+1) ⊆ Finset.Ico 1 p :=
    Finset.Ico_subset_Ico_right (by omega)
  have hz : ∑ j ∈ Finset.Ico 1 p,
      z^j/(j : K)*endpointWeight a b ((n : ℤ)-j) =
      ∑ j ∈ Finset.Ico 1 (n+1), z^j/(j : K)*endpointWeight a b ((n : ℤ)-j) := by
    symm
    apply Finset.sum_subset hsub
    intro j hj hnot
    rw [endpointWeight_nonpositive a b _ (by
      have hpj := Finset.mem_Ico.mp hj
      have hnj : n<j := by
        by_contra h
        exact hnot (Finset.mem_Ico.mpr ⟨hpj.1,by omega⟩)
      omega),mul_zero]
  rw [hz]
  calc
    _ = ∑ j ∈ Finset.Ico 1 (n+1),
        (-2*(z^j*b^(n-j)/(j : K))-z^j*a^(n-j)/(j : K)+
          3*(z^j*(0 : K)^(n-j)/(j : K))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [endpointWeight_negative_band,if_pos (by
        have := (Finset.mem_Ico.mp hj).2
        omega)]
      ring
    _ = _ := by
      simp only [triangle,Finset.sum_add_distrib,Finset.sum_sub_distrib,
        Finset.mul_sum,neg_mul]

theorem inv_power_mul_power_low (x : K) (hx : x≠0) (n j : ℕ) (hj : j≤n) :
    x⁻¹^n*x^j=x⁻¹^(n-j) := by
  calc
    _ = (x⁻¹^j*x^j)*x⁻¹^(n-j) := by
      nth_rw 1 [show n=j+(n-j) by omega]
      rw [pow_add]
      ring
    _ = _ := by rw [←mul_pow,inv_mul_cancel₀ hx,one_pow,one_mul]

theorem inv_power_mul_power_high (x : K) (hx : x≠0) (n j : ℕ) (hj : n≤j) :
    x⁻¹^n*x^j=x^(j-n) := by
  calc
    _ = (x⁻¹^n*x^n)*x^(j-n) := by
      nth_rw 1 [show j=n+(j-n) by omega]
      rw [pow_add]
      ring
    _ = _ := by rw [←mul_pow,inv_mul_cancel₀ hx,one_pow,one_mul]

theorem endpointWeight_positive_band (a b : K) (ha : a≠0) (hb : b≠0) (n j : ℕ) :
    endpointWeight a b ((j : ℤ)-n) =
      -(2*b⁻¹^n*b^j+a⁻¹^n*a^j)+
        (if j≤n then 2*b⁻¹^(n-j)+a⁻¹^(n-j) else 0) := by
  by_cases hj : j≤n
  · rw [endpointWeight_nonpositive _ _ _ (by omega),if_pos hj]
    rw [mul_assoc (2 : K) (b⁻¹^n) (b^j),
      inv_power_mul_power_low b hb n j hj,inv_power_mul_power_low a ha n j hj]
    ring
  · have hs : ((j : ℤ)-n).toNat=j-n := by omega
    simp only [endpointWeight,if_pos (show (0 : ℤ)<(j : ℤ)-n by omega),hs,
      if_neg hj,add_zero]
    rw [mul_assoc (2 : K) (b⁻¹^n) (b^j),inv_power_mul_power_high b hb n j (by omega),
      inv_power_mul_power_high a ha n j (by omega)]

theorem positiveLog_trace_inverted_monomial (p n : ℕ) (hn : n<p)
    (a b z : K) (ha : a≠0) (hb : b≠0) :
    endpointTrace a b (T (-(n : ℤ))*positiveLog p z) =
      -2*b⁻¹^n*finiteLogValue p (b*z)-a⁻¹^n*finiteLogValue p (a*z)+
        2*triangle n b⁻¹ z+triangle n a⁻¹ z := by
  have ht : ∀ j : ℕ, (T (-(n : ℤ)) : K[T;T⁻¹])*
      (C (z^j/(j : K))*T (j : ℤ))=C (z^j/(j : K))*T ((j : ℤ)-n) := by
    intro j
    rw [mul_comm (T (-(n : ℤ))),mul_assoc,←T_add]
    congr 2
  rw [positiveLog,Finset.mul_sum,map_sum]
  simp only [ht,endpointTrace_monomial]
  have hsub : Finset.Ico 1 (n+1) ⊆ Finset.Ico 1 p :=
    Finset.Ico_subset_Ico_right (by omega)
  have hc : ∑ j ∈ Finset.Ico 1 p,
      (if j≤n then 2*(z^j*b⁻¹^(n-j)/(j : K))+z^j*a⁻¹^(n-j)/(j : K) else 0) =
      2*triangle n b⁻¹ z+triangle n a⁻¹ z := by
    rw [←Finset.sum_subset hsub (by
      intro j hj hnot
      have hj1 := (Finset.mem_Ico.mp hj).1
      have hjn : ¬j≤n := by
        intro h
        exact hnot (Finset.mem_Ico.mpr ⟨hj1,by omega⟩)
      rw [if_neg hjn])]
    calc
      _ = ∑ j ∈ Finset.Ico 1 (n+1),
          (2*(z^j*b⁻¹^(n-j)/(j : K))+z^j*a⁻¹^(n-j)/(j : K)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [if_pos (by have := (Finset.mem_Ico.mp hj).2; omega)]
      _ = _ := by simp only [triangle,Finset.sum_add_distrib,Finset.mul_sum]
  calc
    _ = (∑ j ∈ Finset.Ico 1 p,
        (-2*b⁻¹^n*((b*z)^j/(j : K))-a⁻¹^n*((a*z)^j/(j : K))))+
        ∑ j ∈ Finset.Ico 1 p,
          (if j≤n then 2*(z^j*b⁻¹^(n-j)/(j : K))+z^j*a⁻¹^(n-j)/(j : K) else 0) := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [endpointWeight_positive_band a b ha hb,mul_pow,mul_pow]
      by_cases hjn : j≤n
      · rw [if_pos hjn,if_pos hjn]
        ring
      · rw [if_neg hjn,if_neg hjn]
        ring
    _ = _ := by
      rw [hc]
      simp only [finiteLogValue,Finset.sum_sub_distrib,Finset.mul_sum]
      ring

theorem finiteLogValue_retained (p : ℕ) [Fact p.Prime] (z : ZMod p) :
    finiteLogValue p z=WPFiniteInversion.ell p z := rfl

/-- Every source coefficient through N is retained before any reduction. -/
noncomputable def finiteSource (N : ℕ) (e : ℕ → K) : K[T;T⁻¹] :=
  ∑ n ∈ Finset.range (N+1), C (e n)*T (n : ℤ)

noncomputable def sourceValue (N : ℕ) (e : ℕ → K) (y : K) : K :=
  ∑ n ∈ Finset.range (N+1), e n*y^n

theorem finiteSource_negativeLog_trace (p N : ℕ) (hN : N<p)
    (e : ℕ → K) (a b z : K) :
    endpointTrace a b (finiteSource N e*negativeLog p z) =
      -2*finiteH N e b z-finiteH N e a z+3*finiteH N e 0 z := by
  rw [finiteSource,Finset.sum_mul,map_sum]
  simp only [mul_assoc,endpointTrace_C_mul]
  calc
    _ = ∑ n ∈ Finset.range (N+1), e n*
        (-2*triangle n b z-triangle n a z+3*triangle n 0 z) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [negativeLog_trace_monomial p n (by
        have := Finset.mem_range.mp hn
        omega)]
    _ = _ := by
      calc
        _ = ∑ n∈Finset.range (N+1),
            (-2*(e n*triangle n b z)-e n*triangle n a z+3*(e n*triangle n 0 z)) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = _ := by simp only [finiteH,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]

theorem finiteSource_inverted_negativeLog_trace (p N : ℕ) (e : ℕ → K)
    (a b z : K) :
    endpointTrace a b (invert (finiteSource N e)*negativeLog p z)=0 := by
  rw [finiteSource,map_sum,Finset.sum_mul,map_sum]
  apply Finset.sum_eq_zero
  intro n hn
  simp only [map_mul,invert_C,invert_T]
  rw [negativeLog,Finset.mul_sum,map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have ht : (C (e n)*T (-(n : ℤ)) : K[T;T⁻¹])*
      (C (z^j/(j : K))*T (-(j : ℤ))) =
      C (e n*(z^j/(j : K)))*T (-((n : ℤ)+j)) := by
    rw [map_mul,show -((n : ℤ)+j)=-(n : ℤ)+(-(j : ℤ)) by omega,T_add]
    ring
  rw [ht,endpointTrace_monomial,endpointWeight_nonpositive _ _ _ (by omega),mul_zero]

theorem finiteSource_inverted_positiveLog_trace (p N : ℕ) (hN : N<p)
    (e : ℕ → K) (a b z : K) (ha : a≠0) (hb : b≠0) :
    endpointTrace a b (invert (finiteSource N e)*positiveLog p z) =
      -2*sourceValue N e b⁻¹*finiteLogValue p (b*z)-
        sourceValue N e a⁻¹*finiteLogValue p (a*z)+
        2*finiteH N e b⁻¹ z+finiteH N e a⁻¹ z := by
  rw [finiteSource,map_sum,Finset.sum_mul,map_sum]
  simp only [map_mul,invert_C,invert_T,mul_assoc,endpointTrace_C_mul]
  calc
    _ = ∑ n ∈ Finset.range (N+1), e n*
        (-2*b⁻¹^n*finiteLogValue p (b*z)-a⁻¹^n*finiteLogValue p (a*z)+
          2*triangle n b⁻¹ z+triangle n a⁻¹ z) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [positiveLog_trace_inverted_monomial p n (by
        have := Finset.mem_range.mp hn
        omega) a b z ha hb]
    _ = _ := by
      calc
        _ = ∑ n∈Finset.range (N+1),
            (-2*(e n*b⁻¹^n)*finiteLogValue p (b*z)-
              (e n*a⁻¹^n)*finiteLogValue p (a*z)+
                2*(e n*triangle n b⁻¹ z)+e n*triangle n a⁻¹ z) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = _ := by
          simp only [sourceValue,finiteH,Finset.mul_sum,Finset.sum_mul,
            Finset.sum_add_distrib,Finset.sum_sub_distrib,mul_assoc]

theorem positiveLog_trace_monomial (p n : ℕ) (a b z : K) :
    endpointTrace a b (T (n : ℤ)*positiveLog p z) =
      -2*b^n*finiteLogValue p (b*z)-a^n*finiteLogValue p (a*z) := by
  rw [positiveLog,Finset.mul_sum,map_sum]
  calc
    _ = ∑ j ∈ Finset.Ico 1 p,
        (-2*b^n*((b*z)^j/(j : K))-a^n*((a*z)^j/(j : K))) := by
      apply Finset.sum_congr rfl
      intro j hj
      have ht : (T (n : ℤ) : K[T;T⁻¹])*(C (z^j/(j : K))*T (j : ℤ))=
          C (z^j/(j : K))*T ((n+j : ℕ) : ℤ) := by
        rw [mul_comm (T (n : ℤ)),mul_assoc,←T_add]
        congr 2
        omega
      rw [ht,endpointTrace_monomial,endpointWeight_nat,if_neg (by
        have := (Finset.mem_Ico.mp hj).1
        omega),pow_add,pow_add,mul_pow,mul_pow]
      ring
    _ = _ := by simp only [finiteLogValue,Finset.sum_sub_distrib,Finset.mul_sum]

theorem finiteSource_positiveLog_trace (p N : ℕ) (e : ℕ → K) (a b z : K) :
    endpointTrace a b (finiteSource N e*positiveLog p z) =
      -2*sourceValue N e b*finiteLogValue p (b*z)-
        sourceValue N e a*finiteLogValue p (a*z) := by
  rw [finiteSource,Finset.sum_mul,map_sum]
  simp only [mul_assoc,endpointTrace_C_mul,positiveLog_trace_monomial]
  calc
    _ = ∑ n∈Finset.range (N+1),
        (-2*(e n*b^n)*finiteLogValue p (b*z)-(e n*a^n)*finiteLogValue p (a*z)) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = _ := by
      simp only [sourceValue,Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_mul,mul_assoc]

theorem full_source_negativeLog_trace (p N : ℕ) (hN : N<p)
    (e : ℕ → K) (a b z : K) :
    endpointTrace a b ((finiteSource N e+invert (finiteSource N e))*negativeLog p z) =
      -2*finiteH N e b z-finiteH N e a z+3*finiteH N e 0 z := by
  rw [add_mul,map_add,finiteSource_negativeLog_trace p N hN,
    finiteSource_inverted_negativeLog_trace,add_zero]

theorem full_source_positiveLog_trace (p N : ℕ) (hN : N<p)
    (e : ℕ → K) (a b z : K) (ha : a≠0) (hb : b≠0) :
    endpointTrace a b ((finiteSource N e+invert (finiteSource N e))*positiveLog p z) =
      -2*(sourceValue N e b+sourceValue N e b⁻¹)*finiteLogValue p (b*z)-
        (sourceValue N e a+sourceValue N e a⁻¹)*finiteLogValue p (a*z)+
        2*finiteH N e b⁻¹ z+finiteH N e a⁻¹ z := by
  rw [add_mul,map_add,finiteSource_positiveLog_trace,
    finiteSource_inverted_positiveLog_trace p N hN e a b z ha hb]
  ring

end FiniteBands

end WPFieldAssembly.ActualKwWeightedTrace
