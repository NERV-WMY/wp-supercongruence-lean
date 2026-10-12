import WPFieldAssembly.ActualKwFirstCarry
import WPFieldAssembly.ActualKwWeightedTrace
import Mathlib.Algebra.Polynomial.Reverse

open scoped Polynomial LaurentPolynomial PowerSeries BigOperators
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.ActualKwSeriesAttachment

set_option maxHeartbeats 1600000

/- Statement fidelity: the p+1 trace uses the original numerator
9*5^(p-1)*X^(p-1)*(4X-11)^p*(4-11X). Its reflection at degree 2p
identifies the rational Kw infinity series with its actual dlogQ trace.
All signed Laurent inputs are retained. The comparison source is supplied
separately by its owner; this module assigns no actual source or scalar value. -/

theorem zcoeff_X_pow_mul (n : ℤ) (k : ℕ) (F : ℚ⟦X⟧) :
    LaurentPoleTrace.zcoeff n (PowerSeries.X^k*F)=
      LaurentPoleTrace.zcoeff (n-(k : ℤ)) F := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have he : n-1-(k : ℤ)=n-((k+1 : ℕ) : ℤ) := by omega
    calc
      _ = LaurentPoleTrace.zcoeff n (PowerSeries.X*(PowerSeries.X^k*F)) := by
        congr 1
        rw [pow_succ]
        ring
      _ = LaurentPoleTrace.zcoeff (n-1) (PowerSeries.X^k*F) :=
        LaurentPoleTrace.zcoeff_X_mul n _
      _ = _ := by rw [ih,he]

theorem reflected_polynomial_expansion (d : ℕ) (P : ℚ[X]) (hP : P.natDegree≤d) :
    reflect d P = ∑ j ∈ P.support, Polynomial.C (P.coeff j)*X^(d-j) := by
  let R : ℚ[X] →+ ℚ[X] :=
    { toFun := reflect d
      map_zero' := reflect_zero
      map_add' := fun P Q => reflect_add P Q d }
  have hs := congrArg R (sum_C_mul_X_pow_eq P)
  rw [Polynomial.sum_def,map_sum] at hs
  change (∑ j ∈ P.support, reflect d (Polynomial.C (P.coeff j)*X^j))=reflect d P at hs
  rw [←hs]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd : j≤d := (le_natDegree_of_ne_zero (mem_support_iff.mp hj)).trans hP
  rw [reflect_C_mul_X_pow,revAt_le hjd]

theorem reflected_series_expansion (d : ℕ) (P : ℚ[X]) (hP : P.natDegree≤d) :
    (reflect d P : ℚ⟦X⟧)=
      ∑ j ∈ P.support, PowerSeries.C (P.coeff j)*PowerSeries.X^(d-j) := by
  rw [reflected_polynomial_expansion d P hP]
  change Polynomial.coeToPowerSeries.ringHom
    (∑ j ∈ P.support, Polynomial.C (P.coeff j)*X^(d-j))=_
  simp only [map_sum,map_mul,map_pow,Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C,Polynomial.coe_X]

theorem original_laurent_expansion (P : ℚ[X]) :
    P.toLaurent=∑ j ∈ P.support, LaurentPolynomial.C (P.coeff j)*T (j : ℤ) := by
  have hs := congrArg (fun P : ℚ[X] => P.toLaurent) (sum_C_mul_X_pow_eq P)
  rw [Polynomial.sum_def,map_sum] at hs
  simp only [Polynomial.toLaurent_C_mul_X_pow] at hs
  exact hs.symm

theorem reflected_trace_monomial (m d : ℕ) (P : ℚ[X]) (hP : P.natDegree≤d)
    (n : ℤ) :
    LaurentPoleTrace.trace m (P.toLaurent*T n)=
      -(-1/4 : ℚ)^m*LaurentPoleTrace.zcoeff (n-(2*(m : ℤ)-1)+(d : ℤ))
        ((reflect d P : ℚ⟦X⟧)*LaurentPoleTrace.reciprocal^m) := by
  rw [original_laurent_expansion,Finset.sum_mul,map_sum,
    reflected_series_expansion d P hP,Finset.sum_mul,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd : j≤d := (le_natDegree_of_ne_zero (mem_support_iff.mp hj)).trans hP
  have he : n-(2*(m : ℤ)-1)+(d : ℤ)-((d-j : ℕ) : ℤ)=
      ((j : ℤ)+n)-(2*(m : ℤ)-1) := by omega
  rw [mul_assoc,←T_add,LaurentPoleTrace.trace_monomial]
  rw [mul_assoc,LaurentPoleTrace.zcoeff_C_mul,zcoeff_X_pow_mul,he,
    LaurentPoleTrace.weight]
  ring

noncomputable def seriesDlogKernel : ℚ⟦X⟧ :=
  PowerSeries.C (-1/4 : ℚ)*(PowerSeries.C 12*PowerSeries.X-PowerSeries.C 33)*
    LaurentPoleTrace.reciprocal

noncomputable def seriesWeightedTrace (F : ℚ⟦X⟧) : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ :=
  (Finsupp.linearCombination ℚ
    (fun n : ℤ => -LaurentPoleTrace.zcoeff (n-1) (F*seriesDlogKernel))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

@[simp] theorem seriesWeightedTrace_monomial (F : ℚ⟦X⟧) (d : ℚ) (n : ℤ) :
    seriesWeightedTrace F (LaurentPolynomial.C d*T n)=
      -d*LaurentPoleTrace.zcoeff (n-1) (F*seriesDlogKernel) := by
  rw [←single_eq_C_mul_T]
  change Finsupp.linearCombination ℚ _ (Finsupp.single n d)=_
  rw [Finsupp.linearCombination_single,smul_eq_mul]
  ring

noncomputable def originalWeightedNumerator (p : ℕ) : ℚ[X] :=
  Polynomial.C (9*5^(p-1) : ℚ)*X^(p-1)*
    (Polynomial.C 4*X-Polynomial.C 11)^p*(Polynomial.C 4-Polynomial.C 11*X)

theorem originalWeightedNumerator_laurent (p : ℕ) :
    (originalWeightedNumerator p).toLaurent=
      LaurentPolynomial.C (9*5^(p-1) : ℚ)*T ((p-1 : ℕ) : ℤ)*
        (4*T 1-11)^p*(4-11*T 1) := by
  simp only [originalWeightedNumerator,map_mul,map_pow,map_sub,
    Polynomial.toLaurent_C,Polynomial.toLaurent_X,LaurentPolynomial.T_pow,mul_one]
  rfl

noncomputable def actualWeightedTrace (p : ℕ) : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ :=
  (LaurentPoleTrace.trace (p+1)).comp
    ({ toFun := fun L => (originalWeightedNumerator p).toLaurent*L
       map_add' := by intro L M; ring
       map_smul' := by
         intro a L
         simp only [LaurentPolynomial.smul_eq_C_mul,RingHom.id_apply]
         ring } : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ[T;T⁻¹])

theorem reflected_linear_power (P : ℚ[X]) (hP : P.natDegree≤1) (p : ℕ) :
    reflect p (P^p)=(reflect 1 P)^p := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hd : (P^p).natDegree≤p := by
      simpa only [Nat.mul_one] using natDegree_pow_le_of_le p hP
    rw [pow_succ,reflect_mul _ _ hd hP,ih,pow_succ]

theorem originalWeightedNumerator_degree (p : ℕ) (hp : 0<p) :
    (originalWeightedNumerator p).natDegree≤2*p := by
  have h1 : (Polynomial.C 4*X-Polynomial.C 11 : ℚ[X]).natDegree≤1 := by
    apply (natDegree_sub_le _ _).trans
    simp
  have h2 : (Polynomial.C 4-Polynomial.C 11*X : ℚ[X]).natDegree≤1 := by
    apply (natDegree_sub_le _ _).trans
    simp
  have hd0 : (Polynomial.C (9*5^(p-1) : ℚ)*X^(p-1)).natDegree≤p-1 := by
    simpa only [natDegree_X_pow] using natDegree_C_mul_le (9*5^(p-1) : ℚ) (X^(p-1))
  have hd1 : ((Polynomial.C 4*X-Polynomial.C 11 : ℚ[X])^p).natDegree≤p := by
    simpa only [Nat.mul_one] using natDegree_pow_le_of_le p h1
  have hd2 := natDegree_mul_le_of_le hd0 hd1
  have hd3 := natDegree_mul_le_of_le hd2 h2
  unfold originalWeightedNumerator
  omega

theorem originalWeightedNumerator_reflect (p : ℕ) (hp : 0<p) :
    reflect (2*p) (originalWeightedNumerator p) =
      Polynomial.C (9*5^(p-1) : ℚ)*(Polynomial.C 4-Polynomial.C 11*X)^p*
        (Polynomial.C 4*X-Polynomial.C 11) := by
  have h1 : (Polynomial.C 4*X-Polynomial.C 11 : ℚ[X]).natDegree≤1 := by
    apply (natDegree_sub_le _ _).trans
    simp
  have h2 : (Polynomial.C 4-Polynomial.C 11*X : ℚ[X]).natDegree≤1 := by
    apply (natDegree_sub_le _ _).trans
    simp
  have hr1 : reflect 1 (Polynomial.C 4*X-Polynomial.C 11 : ℚ[X])=
      Polynomial.C 4-Polynomial.C 11*X := by
    rw [reflect_sub,reflect_C_mul,reflect_one_X]
    norm_num
  have hr2 : reflect 1 (Polynomial.C 4-Polynomial.C 11*X : ℚ[X])=
      Polynomial.C 4*X-Polynomial.C 11 := by
    rw [reflect_sub,reflect_C_mul,reflect_one_X]
    norm_num
  have hdp : ((Polynomial.C 4*X-Polynomial.C 11 : ℚ[X])^p).natDegree≤p := by
    simpa only [Nat.mul_one] using natDegree_pow_le_of_le p h1
  have hdx : (X^(p-1) : ℚ[X]).natDegree≤p-1 := by simp
  have hd := natDegree_mul_le_of_le hdx hdp
  have he : originalWeightedNumerator p=Polynomial.C (9*5^(p-1) : ℚ)*
      (X^(p-1)*(Polynomial.C 4*X-Polynomial.C 11)^p*
        (Polynomial.C 4-Polynomial.C 11*X)) := by unfold originalWeightedNumerator; ring
  rw [he]
  rw [show 2*p=((p-1)+p)+1 by omega,reflect_C_mul,
    reflect_mul _ _ hd h2,reflect_mul _ _ hdx hdp,
    reflect_monomial,revAt_le (le_refl _),Nat.sub_self,
    reflected_linear_power _ h1,hr1,hr2]
  simp
  ring

theorem literalKw_series_kernel (p : ℕ) (hp : 0<p) :
    ActualKwFirstCarry.literalKwInfinity p*seriesDlogKernel =
      PowerSeries.C ((-1/4 : ℚ)^(p+1))*
        (reflect (2*p) (originalWeightedNumerator p) : ℚ⟦X⟧)*
          LaurentPoleTrace.reciprocal^(p+1) := by
  rw [originalWeightedNumerator_reflect p hp]
  simp only [Polynomial.coe_mul,Polynomial.coe_C,Polynomial.coe_pow,
    Polynomial.coe_sub,Polynomial.coe_X]
  unfold ActualKwFirstCarry.literalKwInfinity seriesDlogKernel
  rw [pow_succ,pow_succ,map_mul]
  have hs : (PowerSeries.C (9*5^(p-1) : ℚ) : ℚ⟦X⟧)=
      PowerSeries.C (3*5^(p-1) : ℚ)*3 := by
    change PowerSeries.C (9*5^(p-1) : ℚ)=PowerSeries.C (3*5^(p-1) : ℚ)*PowerSeries.C 3
    rw [←map_mul]
    congr 1
    ring
  rw [hs]
  simp only [map_mul,map_ofNat]
  ring

theorem actualWeightedTrace_series (p : ℕ) (hp : 0<p) (L : ℚ[T;T⁻¹]) :
    actualWeightedTrace p L=seriesWeightedTrace (ActualKwFirstCarry.literalKwInfinity p) L := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM => rw [map_add,map_add,hL,hM]
  | C_mul_T n d =>
    change LaurentPoleTrace.trace (p+1)
      ((originalWeightedNumerator p).toLaurent*(LaurentPolynomial.C d*T n))=_
    rw [mul_comm (originalWeightedNumerator p).toLaurent,mul_assoc,
      LaurentPoleTrace.trace_C_mul,seriesWeightedTrace_monomial,
      literalKw_series_kernel p hp]
    rw [mul_comm (T n),reflected_trace_monomial (p+1) (2*p)
      (originalWeightedNumerator p) (originalWeightedNumerator_degree p hp)]
    have he : n-(2*((p+1 : ℕ) : ℤ)-1)+((2*p : ℕ) : ℤ)=n-1 := by omega
    rw [he,mul_assoc,LaurentPoleTrace.zcoeff_C_mul]
    ring

theorem seriesWeightedTrace_add (F G : ℚ⟦X⟧) (L : ℚ[T;T⁻¹]) :
    seriesWeightedTrace (F+G) L=seriesWeightedTrace F L+seriesWeightedTrace G L := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM => rw [map_add,map_add,map_add,hL,hM]; ring
  | C_mul_T n d =>
    rw [seriesWeightedTrace_monomial,seriesWeightedTrace_monomial,
      seriesWeightedTrace_monomial,add_mul,map_add]
    ring

theorem seriesWeightedTrace_C_mul (F : ℚ⟦X⟧) (a : ℚ) (L : ℚ[T;T⁻¹]) :
    seriesWeightedTrace (PowerSeries.C a*F) L=a*seriesWeightedTrace F L := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM => rw [map_add,map_add,hL,hM]; ring
  | C_mul_T n d =>
    rw [seriesWeightedTrace_monomial,seriesWeightedTrace_monomial,
      mul_assoc,LaurentPoleTrace.zcoeff_C_mul]
    ring

theorem actualKwCarryQ_normalization (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    ActualKwFirstCarry.actualKwCarryQ p=
      PowerSeries.C (-3*5^(p-1) : ℚ)*ActualKwFirstCarry.actualUnitCarryQ p := by
  rw [←ActualKwFirstCarry.actualKwCarryIntegral_value p hp,
    ActualKwFirstCarry.actualKwCarryIntegral,map_mul,PowerSeries.map_C,
    ActualKwFirstCarry.actualUnitCarryIntegral_value p hp]
  rfl

/-- The original whole weighted trace is split in Q before coefficient reduction. -/
theorem actualWeightedTrace_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (L : ℚ[T;T⁻¹]) :
    actualWeightedTrace p L =
      (-3*5^(p-1) : ℚ)*seriesWeightedTrace
        (ActualKwFirstCarry.frobeniusUnit p (1/4 : ℚ) 4 (11/4)) L+
        (p : ℚ)*seriesWeightedTrace (ActualKwFirstCarry.actualKwCarryQ p) L := by
  rw [actualWeightedTrace_series p (by omega),ActualKwFirstCarry.literalKwInfinity_firstTaylor p hp,
    seriesWeightedTrace_add,seriesWeightedTrace_C_mul,seriesWeightedTrace_C_mul,
    actualKwCarryQ_normalization p hp]

theorem actualWeightedTrace_divided_difference (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (L : ℚ[T;T⁻¹]) :
    (1/(p : ℚ))*(actualWeightedTrace p L-
      (-3*5^(p-1) : ℚ)*seriesWeightedTrace
        (ActualKwFirstCarry.frobeniusUnit p (1/4 : ℚ) 4 (11/4)) L)=
        seriesWeightedTrace (ActualKwFirstCarry.actualKwCarryQ p) L := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : p≠0)
  rw [actualWeightedTrace_firstTaylor p hp]
  field_simp [hpq]; ring

theorem seriesDlogKernel_expansion :
    seriesDlogKernel=PowerSeries.C (-3 : ℚ)*PowerSeries.X*LaurentPoleTrace.reciprocal+
      PowerSeries.C (33/4 : ℚ)*LaurentPoleTrace.reciprocal := by
  have h12 : (PowerSeries.C (-1/4 : ℚ) : ℚ⟦X⟧)*PowerSeries.C 12=
      PowerSeries.C (-3 : ℚ) := by rw [←map_mul]; norm_num
  have h33 : (PowerSeries.C (-1/4 : ℚ) : ℚ⟦X⟧)*PowerSeries.C 33=
      PowerSeries.C (-33/4 : ℚ) := by rw [←map_mul]; norm_num
  unfold seriesDlogKernel
  calc
    _ = (PowerSeries.C (-1/4 : ℚ)*PowerSeries.C 12)*PowerSeries.X*
        LaurentPoleTrace.reciprocal-(PowerSeries.C (-1/4 : ℚ)*PowerSeries.C 33)*
          LaurentPoleTrace.reciprocal := by ring
    _ = _ := by
      rw [h12,h33]
      simp only [show (-33/4 : ℚ)=-(33/4) by ring,map_neg]
      ring

theorem seriesWeightedTrace_one (L : ℚ[T;T⁻¹]) :
    seriesWeightedTrace 1 L=ActualKwWeightedTrace.rationalDlogQ L := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM => rw [map_add,map_add,hL,hM]
  | C_mul_T n d =>
    rw [seriesWeightedTrace_monomial,one_mul,seriesDlogKernel_expansion,map_add,
      mul_assoc,LaurentPoleTrace.zcoeff_C_mul,LaurentPoleTrace.zcoeff_C_mul,
      LaurentPoleTrace.zcoeff_X_mul]
    change _=LaurentPoleTrace.trace 1 (3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C d*T n))
    rw [ActualKwWeightedTrace.literal_density_monomial,map_sub,
      LaurentPoleTrace.trace_monomial,LaurentPoleTrace.trace_monomial,
      LaurentPoleTrace.weight,LaurentPoleTrace.weight]
    norm_num only [pow_one,Nat.cast_one]
    ring

/-- The cutoff is justified by the input degree, including every signed lower slot. -/
theorem zcoeff_product_full_band (B : ℕ) (n : ℤ) (hn : n≤(B : ℤ)) (F G : ℚ⟦X⟧) :
    LaurentPoleTrace.zcoeff (n-1) (F*G)=
      ∑ r ∈ Finset.range B, PowerSeries.coeff r F*
        LaurentPoleTrace.zcoeff (n-1-(r : ℤ)) G := by
  by_cases hpos : 0<n
  · let m := (n-1).toNat
    have he : n-1=(m : ℤ) := by dsimp only [m]; omega
    have hb : m+1≤B := by omega
    rw [he,LaurentPoleTrace.zcoeff_nat,PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hs : Finset.range (m+1) ⊆ Finset.range B := Finset.range_mono hb
    symm
    calc
      _ = ∑ r ∈ Finset.range (m+1), PowerSeries.coeff r F*
          LaurentPoleTrace.zcoeff ((m : ℤ)-(r : ℤ)) G := by
        symm
        apply Finset.sum_subset hs
        intro r hr hnot
        rw [LaurentPoleTrace.zcoeff_neg _ (by
          have hm : m<r := by
            by_contra h
            exact hnot (Finset.mem_range.mpr (by omega))
          omega),mul_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r hr
        have her : (m : ℤ)-(r : ℤ)=((m-r : ℕ) : ℤ) := by
          have := Finset.mem_range.mp hr
          omega
        rw [her,LaurentPoleTrace.zcoeff_nat]
  · rw [LaurentPoleTrace.zcoeff_neg _ (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro r hr
    rw [LaurentPoleTrace.zcoeff_neg _ (by omega),mul_zero]

noncomputable def finiteCoupling (B : ℕ) (F : ℚ⟦X⟧) : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ :=
  { toFun := fun L => ∑ r ∈ Finset.range B,
      PowerSeries.coeff r F*ActualKwWeightedTrace.rationalDlogQ (T (-(r : ℤ))*L)
    map_add' := by
      intro L M
      simp only [mul_add,map_add,mul_add,Finset.sum_add_distrib]
    map_smul' := by
      intro a L
      simp only [LaurentPolynomial.smul_eq_C_mul,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
      apply Finset.sum_congr rfl
      intro r hr
      have hC : (T (-(r : ℤ)) : ℚ[T;T⁻¹])*(LaurentPolynomial.C a*L)=
          LaurentPolynomial.C a*(T (-(r : ℤ))*L) := by ring
      rw [hC,←LaurentPolynomial.smul_eq_C_mul,map_smul,smul_eq_mul]
      ring
      }

theorem finiteCoupling_monomial (B : ℕ) (F : ℚ⟦X⟧) (d : ℚ) (n : ℤ)
    (hn : n≤(B : ℤ)) :
    finiteCoupling B F (LaurentPolynomial.C d*T n)=
      seriesWeightedTrace F (LaurentPolynomial.C d*T n) := by
  rw [seriesWeightedTrace_monomial,zcoeff_product_full_band B n hn,Finset.mul_sum]
  change (∑ r∈Finset.range B, PowerSeries.coeff r F*
    ActualKwWeightedTrace.rationalDlogQ (T (-(r : ℤ))*(LaurentPolynomial.C d*T n)))=_
  apply Finset.sum_congr rfl
  intro r hr
  have ht : (T (-(r : ℤ)) : ℚ[T;T⁻¹])*(LaurentPolynomial.C d*T n)=
      LaurentPolynomial.C d*T (n-(r : ℤ)) := by
    rw [mul_comm (T (-(r : ℤ))),mul_assoc,←T_add]
    congr 2
  rw [ht,←seriesWeightedTrace_one,seriesWeightedTrace_monomial,one_mul]
  have he : (n-(r : ℤ))-1=n-1-(r : ℤ) := by omega
  rw [he]
  ring

theorem finiteCoupling_full_source (B : ℕ) (F : ℚ⟦X⟧) (I : Finset ℤ) (e : ℤ → ℚ)
    (hI : ∀ n∈I, n≤(B : ℤ)) :
    finiteCoupling B F (∑ n∈I, LaurentPolynomial.C (e n)*T n)=
      seriesWeightedTrace F (∑ n∈I, LaurentPolynomial.C (e n)*T n) := by
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact finiteCoupling_monomial B F (e n) n (hI n hn)

open WPPIntegralReduction WPActualChiSource WPActualEtaIntegrality

noncomputable def dlogQNumerator {K : Type*} [CommRing K] : K[T;T⁻¹] :=
  3*T (-1)*(4-11*T 1)

theorem dlogQNumerator_map {K J : Type*} [CommRing K] [CommRing J] (f : K →+* J) :
    coefficientMap f (dlogQNumerator : K[T;T⁻¹])=(dlogQNumerator : J[T;T⁻¹]) := by
  simp only [dlogQNumerator,map_mul,map_sub,map_ofNat,coefficientMap_T]

noncomputable def integralDlogQ (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (L : (integralRationals p)[T;T⁻¹]) : integralRationals p :=
  ⟨ActualKwWeightedTrace.rationalDlogQ (coefficientMap (integralRationals p).subtype L), by
    have hI := coefficientMap_subtype_integral p ((dlogQNumerator :
      (integralRationals p)[T;T⁻¹])*L)
    rw [map_mul,dlogQNumerator_map] at hI
    exact LaurentPoleIntegral.trace_integral p 1 hp _ hI⟩

theorem integralDlogQ_value (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (L : (integralRationals p)[T;T⁻¹]) :
    (integralDlogQ p hp L).val=
      ActualKwWeightedTrace.rationalDlogQ (coefficientMap (integralRationals p).subtype L) := rfl

theorem integralDlogQ_field (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (L : (integralRationals p)[T;T⁻¹]) :
    residueHom p (integralDlogQ p hp L)=
      ActualKwWeightedTrace.fieldDlogQ p (coefficientMap (residueHom p) L) := by
  have hI := coefficientMap_subtype_integral p ((dlogQNumerator :
    (integralRationals p)[T;T⁻¹])*L)
  have ht := LaurentPoleField.trace_reduce p 1 hp _ hI
  have hsub : coefficientMap (integralRationals p).subtype
      ((dlogQNumerator : (integralRationals p)[T;T⁻¹])*L)=
        dlogQNumerator*coefficientMap (integralRationals p).subtype L := by
    rw [map_mul,dlogQNumerator_map]
  have hres : coefficientMap (residueHom p)
      ((dlogQNumerator : (integralRationals p)[T;T⁻¹])*L)=
        dlogQNumerator*coefficientMap (residueHom p) L := by
    rw [map_mul,dlogQNumerator_map]
  rw [ActualKwFieldTrace.reduce_integral_map,hsub,hres] at ht
  exact ht

noncomputable def actualFiniteCarryIntegral (p B : ℕ) [Fact p.Prime] (hp : 19≤p)
    (L : (integralRationals p)[T;T⁻¹]) : integralRationals p :=
  ∑ r∈Finset.range B, PowerSeries.coeff r (ActualKwFirstCarry.actualKwCarryIntegral p)*
    integralDlogQ p hp (T (-(r : ℤ))*L)

theorem actualFiniteCarryIntegral_value (p B : ℕ) [Fact p.Prime] (hp : 19≤p)
    (L : (integralRationals p)[T;T⁻¹]) :
    (actualFiniteCarryIntegral p B hp L).val=
      finiteCoupling B (ActualKwFirstCarry.actualKwCarryQ p)
        (coefficientMap (integralRationals p).subtype L) := by
  change (integralRationals p).subtype (actualFiniteCarryIntegral p B hp L)=_
  rw [actualFiniteCarryIntegral,map_sum]
  change (∑ r∈Finset.range B, (integralRationals p).subtype
    (PowerSeries.coeff r (ActualKwFirstCarry.actualKwCarryIntegral p)*
      integralDlogQ p hp (T (-(r : ℤ))*L)))=_
  apply Finset.sum_congr rfl
  intro r hr
  rw [map_mul,←PowerSeries.coeff_map,ActualKwFirstCarry.actualKwCarryIntegral_value p hp]
  change PowerSeries.coeff r (ActualKwFirstCarry.actualKwCarryQ p)*
    (integralDlogQ p hp (T (-(r : ℤ))*L)).val=_
  have hm : coefficientMap (integralRationals p).subtype (T (-(r : ℤ))*L)=
      T (-(r : ℤ))*coefficientMap (integralRationals p).subtype L := by
    rw [map_mul,coefficientMap_T]
  rw [integralDlogQ_value,hm]

theorem actualFiniteCarryIntegral_field (p B : ℕ) [Fact p.Prime] (hp : 19≤p)
    (hB : B≤2*p) (L : (integralRationals p)[T;T⁻¹]) :
    residueHom p (actualFiniteCarryIntegral p B hp L)=
      (-3 : ZMod p)*(∑ r∈Finset.range B,
        PowerSeries.coeff r (ActualKwFirstCarry.literalFirstTwoPhases p)*
          ActualKwWeightedTrace.fieldDlogQ p
            (T (-(r : ℤ))*coefficientMap (residueHom p) L)) := by
  rw [actualFiniteCarryIntegral,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hm : coefficientMap (residueHom p) (T (-(r : ℤ))*L)=
      T (-(r : ℤ))*coefficientMap (residueHom p) L := by
    rw [map_mul,coefficientMap_T]
  rw [map_mul,ActualKwFirstCarry.actualKwCarry_coeff_field p r hp (by
      have := Finset.mem_range.mp hr
      omega),integralDlogQ_field p hp,hm]
  ring

/-- No top coefficient is discarded when the whole actual rational difference is divided. -/
theorem actualWeightedTrace_divided_full_source (p B : ℕ) [Fact p.Prime] (hp : 19≤p)
    (L : (integralRationals p)[T;T⁻¹]) (I : Finset ℤ) (e : ℤ → ℚ)
    (hL : coefficientMap (integralRationals p).subtype L=
      ∑ n∈I, LaurentPolynomial.C (e n)*T n)
    (hI : ∀ n∈I, n≤(B : ℤ)) :
    (1/(p : ℚ))*(actualWeightedTrace p (coefficientMap (integralRationals p).subtype L)-
      (-3*5^(p-1) : ℚ)*seriesWeightedTrace
        (ActualKwFirstCarry.frobeniusUnit p (1/4 : ℚ) 4 (11/4))
          (coefficientMap (integralRationals p).subtype L))=
      (actualFiniteCarryIntegral p B hp L).val := by
  rw [actualWeightedTrace_divided_difference p hp,actualFiniteCarryIntegral_value p B hp,
    hL,finiteCoupling_full_source B _ I e hI]

end WPFieldAssembly.ActualKwSeriesAttachment
