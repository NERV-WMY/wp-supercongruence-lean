import WPFieldAssembly.SourceClosureUVEndpoint
import WPFieldAssembly.SourceClosureUVPrimitiveSource
import WPFieldAssembly.SourceClosureLogInversion

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.SourceClosureUVEndpoint
  WPFieldAssembly.SourceClosureUVPrimitiveSource
  WPFieldAssembly.SourceClosureLogInversion

namespace WPFieldAssembly.SourceClosureUVPositiveSource

/- STATEMENT_FIDELITY: whole UW17 positive source. The original P's
   invisible 0,+p,-p slots, endpoint residues and Frobenius correction
   are retained. Clearing poles is an identity, not a free derivative
   premise. The actual rational VS remains a separate attachment. -/

variable {K : Type*} [Field K]

noncomputable def originalK (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K :=
  4*WPFiniteABSourceTail.epsilon p*WPFifthEntropy.C p u/15

noncomputable def originalZ (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    K[T;T⁻¹] :=
  (WPFiniteWSource.W p).toLaurent+invert (WPFiniteWSource.W p).toLaurent+
    LaurentPolynomial.C (originalK p u)

noncomputable def twiceGammaNumerator : K[T;T⁻¹] :=
  T 1*(T 1-LaurentPolynomial.C (1/4 : K))*(T 1-4)+
    2*T 1*(T 1+1)*(2*T 1-LaurentPolynomial.C (1/4 : K)-4)-
      2*poleProductOverX

noncomputable def gammaANumerator : K[T;T⁻¹] :=
  T 1*(T 1+1)*(2*T 1-LaurentPolynomial.C (1/4 : K)-4)-poleProductOverX

theorem originalK0_derivative (p : ℕ) [Fact p.Prime] [CharP K p] :
    D (originalK0 p : K[T;T⁻¹])=0 := by
  have hp0 : ((p : ℤ) : K)=0 := by
    simpa only [Int.cast_natCast] using CharP.cast_eq_zero K p
  rw [originalK0,mul_add,map_sub,map_add,D_C,D_monomial,D_monomial]
  simp only [Int.cast_neg,hp0,neg_zero,mul_zero,map_zero,zero_mul,zero_add,sub_zero]

theorem originalInvisibleP_sum (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) :
    originalInvisibleP p u+invert (originalInvisibleP p u)=
      originalK0 p*LaurentPolynomial.C (originalK p u) := by
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have heps : (WPFiniteABSourceTail.epsilon p : K)≠0 := pow_ne_zero _ h5
  have h0 : LaurentPolynomial.C (17*WPFifthEntropy.C p u/15)+
      LaurentPolynomial.C (17*WPFifthEntropy.C p u/15)=
      LaurentPolynomial.C (17/(2*WPFiniteABSourceTail.epsilon p) : K)*
        LaurentPolynomial.C (originalK p u) := by
    rw [←map_add,←map_mul]
    congr 1
    unfold originalK
    field_simp [heps,h2,h15]
    ring
  have hside : LaurentPolynomial.C (WPFiniteABSourceTail.uSlot p u)+
      LaurentPolynomial.C (4*(WPFiniteNC122.q p-WPFifthEntropy.C p u)/15)=
      -LaurentPolynomial.C (2/WPFiniteABSourceTail.epsilon p : K)*
        LaurentPolynomial.C (originalK p u) := by
    rw [←map_neg,←map_add,←map_mul]
    congr 1
    unfold WPFiniteABSourceTail.uSlot originalK
    field_simp [heps,h15]
    ring
  simp only [originalInvisibleP,map_add,map_mul,invert_C,invert_T,neg_neg,originalK0]
  linear_combination h0+(T (p : ℤ)+T (-(p : ℤ)))*hside

/-- Original full S factorization, including all three invisible P slots. -/
theorem originalS_factorization (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) :
    WPFiniteZSource.P p u+invert (WPFiniteZSource.P p u)=
      originalK0 p*originalZ p u := by
  have hk : invert (originalK0 p : K[T;T⁻¹])=originalK0 p := by
    simp only [originalK0,map_sub,map_mul,map_add,invert_C,invert_T,neg_neg]
    ring
  simp only [originalP_decomposition p u,map_add,map_mul,hk,
    originalJlog_invert p hp,originalZ]
  linear_combination originalInvisibleP_sum (K:=K) p hp u

/-- Endpoint residues collect exactly, without dropping the ordinary residue. -/
theorem originalHsym_source_collected (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    4*poleProduct*D (originalHsym p)=
      2*poleProductOverX*invert (WPFiniteWSource.W p : K[X]).toLaurent-
      2*twiceGammaNumerator*originalZ p u+
      4*LaurentPolynomial.C (originalZE p u)*gammaANumerator+
      LaurentPolynomial.C (originalK p u)*poleProductOverX := by
  have hm : (2 : K)*((WPFiniteWSource.W p).eval (-1))+originalK p u=0 := by
    rw [originalW_branch p hp u hu]
    unfold originalK
    ring
  have hmc := congrArg LaurentPolynomial.C hm
  simp only [map_add,map_mul,map_ofNat,map_zero] at hmc
  have hs := originalHsym_source_expanded (K:=K) p hp
  dsimp only at hs
  simp only [originalZ,originalZE,map_add]
  change 4*poleProduct*D (originalHsym p)=
    2*poleProductOverX*invert (WPFiniteWSource.W p : K[X]).toLaurent-
      2*twiceGammaNumerator*
        ((WPFiniteWSource.W p).toLaurent+invert (WPFiniteWSource.W p).toLaurent+
          LaurentPolynomial.C (originalK p u))+
      4*(LaurentPolynomial.C ((WPFiniteWSource.W p).eval (1/4 : K))+
        LaurentPolynomial.C ((WPFiniteWSource.W p).eval (4 : K))+
          LaurentPolynomial.C (originalK p u))*gammaANumerator+
      LaurentPolynomial.C (originalK p u)*poleProductOverX
  unfold poleProduct poleProductOverX at hs
  unfold twiceGammaNumerator gammaANumerator poleProduct poleProductOverX
  linear_combination 2*hs+
    (T 1-1)*(T 1-LaurentPolynomial.C (1/4 : K))*(T 1-4)*hmc

theorem scaledLog_unit_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (c : K) (hc : c≠0) (hcp : c^p=c) :
    (T 1-LaurentPolynomial.C c)*
      D (SourceClosureUniversalLog.scaledLog p c⁻¹)=T ((p-1 : ℕ) : ℤ)-1 := by
  have hcpi : (c⁻¹)^p=c⁻¹ := by rw [inv_pow,hcp]
  have hs := congrArg (fun P : K[X] => P.toLaurent)
    (WPFinitePSource.LP_scaled_cleared_source p c⁻¹ hcpi)
  simp only [map_mul,map_sub,map_one,Polynomial.toLaurent_C,
    Polynomial.toLaurent_X_pow,Polynomial.toLaurent_X] at hs
  rw [←D_toLaurent] at hs
  change (1-LaurentPolynomial.C c⁻¹*T 1)*
    D (SourceClosureUniversalLog.scaledLog p c⁻¹)=
      LaurentPolynomial.C c⁻¹*(1-T ((p-1 : ℕ) : ℤ)) at hs
  have hi : LaurentPolynomial.C c*LaurentPolynomial.C c⁻¹=1 := by
    rw [←map_mul,mul_inv_cancel₀ hc,map_one]
  linear_combination -LaurentPolynomial.C c*hs-
    (T 1*D (SourceClosureUniversalLog.scaledLog p c⁻¹)+1-T ((p-1 : ℕ) : ℤ))*hi

/-- The canonical unit logarithm retains its exact Frobenius correction. -/
theorem unitLogPrimitive_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (c k : K) (hc : c≠0) (hcp : c^p=c) :
    (T 1-LaurentPolynomial.C c)*
      D (LaurentPolynomial.C k*(T (-(p : ℤ))-LaurentPolynomial.C c)*
        SourceClosureUniversalLog.scaledLog p c⁻¹)=
      LaurentPolynomial.C k*
        (LaurentPolynomial.C c+LaurentPolynomial.C c⁻¹-T (p : ℤ)-T (-(p : ℤ)))+
      LaurentPolynomial.C k*(T 1-LaurentPolynomial.C c)*
        (T ((p-1 : ℕ) : ℤ)-LaurentPolynomial.C c⁻¹*T (-1)) := by
  have hp : 1≤p := (Fact.out : p.Prime).one_lt.le
  have hd : D ((T (-(p : ℤ))-LaurentPolynomial.C c)*
      SourceClosureUniversalLog.scaledLog p c⁻¹)=
      (T (-(p : ℤ))-LaurentPolynomial.C c)*
        D (SourceClosureUniversalLog.scaledLog p c⁻¹) := by
    rw [sub_mul,map_sub,D_frobenius_shift p _ _ (dvd_neg.mpr (dvd_refl _)),D_C_mul]
    ring
  have hsource := scaledLog_unit_source p c hc hcp
  have hi : LaurentPolynomial.C c*LaurentPolynomial.C c⁻¹=1 := by
    rw [←map_mul,mul_inv_cancel₀ hc,map_one]
  have ht1 : (T (-(p : ℤ))*T ((p-1 : ℕ) : ℤ) : K[T;T⁻¹])=T (-1) := by
    rw [←T_add]
    congr 1
    omega
  have ht2 : (T 1*T ((p-1 : ℕ) : ℤ) : K[T;T⁻¹])=T (p : ℤ) := by
    rw [←T_add]
    congr 1
    omega
  have ht0 : (T 1*T (-1) : K[T;T⁻¹])=1 := by rw [←T_add]; norm_num
  rw [mul_assoc,D_C_mul,hd]
  linear_combination
    LaurentPolynomial.C k*(T (-(p : ℤ))-LaurentPolynomial.C c)*hsource+
    LaurentPolynomial.C k*ht1-LaurentPolynomial.C k*ht2+
    LaurentPolynomial.C k*LaurentPolynomial.C c⁻¹*ht0-
    LaurentPolynomial.C k*T (-1)*hi

theorem originalK0_factor (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (originalK0 p : K[T;T⁻¹])=
      LaurentPolynomial.C (2/WPFiniteABSourceTail.epsilon p : K)*
        (LaurentPolynomial.C (1/4 : K)+4-T (p : ℤ)-T (-(p : ℤ))) := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have heps : (WPFiniteABSourceTail.epsilon p : K)≠0 := pow_ne_zero _ h5
  have hc : (2/WPFiniteABSourceTail.epsilon p : K)*((1/4)+4)=
      17/(2*WPFiniteABSourceTail.epsilon p) := by
    field_simp [h2,h4,heps]
    ring
  have hC := congrArg LaurentPolynomial.C hc
  simp only [map_mul,map_add,map_ofNat] at hC
  unfold originalK0
  linear_combination -hC

noncomputable def originalFrobeniusSource (p : ℕ) : K[T;T⁻¹] :=
  T ((p-1 : ℕ) : ℤ)-T (-(p : ℤ)-1)

/-- Both original unit primitives retain the complete signed correction. -/
theorem originalJab_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (T 1-LaurentPolynomial.C (1/4 : K))*(T 1-4)*
      D (originalJa p+originalJb p)=
      originalK0 p*
        (2*T 1-LaurentPolynomial.C (1/4 : K)-4-
          (T 1-LaurentPolynomial.C (1/4 : K))*(T 1-4)*T (-1))+
      LaurentPolynomial.C (2/WPFiniteABSourceTail.epsilon p : K)*
        (T 1-LaurentPolynomial.C (1/4 : K))*(T 1-4)*originalFrobeniusSource p := by
  have hp1 : 1≤p := (Fact.out : p.Prime).one_lt.le
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have ha : (1/4 : K)≠0 := div_ne_zero one_ne_zero h4
  have h4p : (4 : K)^p=4 := WPFiniteField.natCast_pow_char p 4
  have hap : (1/4 : K)^p=1/4 := by rw [div_pow,one_pow,h4p]
  have hJa := unitLogPrimitive_source p (1/4 : K)
    (2/WPFiniteABSourceTail.epsilon p) ha hap
  have hJb := unitLogPrimitive_source p (4 : K)
    (2/WPFiniteABSourceTail.epsilon p) h4 h4p
  simp only [show (1/4 : K)⁻¹=4 by simp only [one_div,inv_inv],map_ofNat] at hJa
  simp only [show (4 : K)⁻¹=1/4 by simp only [one_div],map_ofNat] at hJb
  change (T 1-LaurentPolynomial.C (1/4 : K))*D (originalJa p)=_ at hJa
  change (T 1-4)*D (originalJb p)=_ at hJb
  have htP : (T (p : ℤ)*T (-1) : K[T;T⁻¹])=T ((p-1 : ℕ) : ℤ) := by
    rw [←T_add]
    congr 1
    omega
  have htM : (T (-(p : ℤ))*T (-1) : K[T;T⁻¹])=T (-(p : ℤ)-1) := by
    rw [←T_add]
    congr 1
  rw [originalK0_factor p hp]
  simp only [map_add,originalFrobeniusSource]
  linear_combination
    (T 1-4)*hJa+(T 1-LaurentPolynomial.C (1/4 : K))*hJb-
    LaurentPolynomial.C (2/WPFiniteABSourceTail.epsilon p : K)*
      (T 1-LaurentPolynomial.C (1/4 : K))*(T 1-4)*htP-
    LaurentPolynomial.C (2/WPFiniteABSourceTail.epsilon p : K)*
      (T 1-LaurentPolynomial.C (1/4 : K))*(T 1-4)*htM

theorem originalInvisibleP_correction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) :
    originalK0 p*LaurentPolynomial.C (originalK p u)-
      2*invert (originalInvisibleP p u)=
      LaurentPolynomial.C (-8*WPFiniteNC122.q p/15 : K)*
        (T (p : ℤ)-T (-(p : ℤ))) := by
  have hc : LaurentPolynomial.C (WPFiniteABSourceTail.uSlot p u)-
      LaurentPolynomial.C (4*(WPFiniteNC122.q p-WPFifthEntropy.C p u)/15)=
      LaurentPolynomial.C (-8*WPFiniteNC122.q p/15 : K) := by
    rw [←map_sub]
    congr 1
    unfold WPFiniteABSourceTail.uSlot
    ring
  rw [←originalInvisibleP_sum p hp u]
  simp only [originalInvisibleP,map_add,map_mul,invert_C,invert_T,neg_neg]
  linear_combination (T (p : ℤ)-T (-(p : ℤ)))*hc

noncomputable def originalAlpha (p : ℕ) [Fact p.Prime] [CharP K p] : K :=
  -(2*WPFiniteNC122.q p+3*(WPFiniteInversion.integerFermatQuotient p 3 : K))/15

noncomputable def fourPositiveSourceNumerator (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) : K[T;T⁻¹] :=
  2*poleProductOverX*invert (WPFiniteZSource.P p u)-
    2*twiceGammaNumerator*(WPFiniteZSource.P p u+invert (WPFiniteZSource.P p u))

/-- The actual whole positive source, including every nonunit coefficient. -/
theorem originalUcan_positive_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    4*poleProduct*D (originalUcan p u)=fourPositiveSourceNumerator p u-
      4*LaurentPolynomial.C (originalAlpha p)*poleProduct*originalFrobeniusSource p := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h30 : (30 : K)≠0 := by
    rw [show (30 : K)=2*15 by ring]
    exact mul_ne_zero h2 h15
  have heps : (WPFiniteABSourceTail.epsilon p : K)≠0 := pow_ne_zero _ h5
  have hhalf : (2 : K[T;T⁻¹])*LaurentPolynomial.C (1/2 : K)=1 := by
    change LaurentPolynomial.C (2 : K)*LaurentPolynomial.C (1/2 : K)=1
    rw [←map_mul,mul_one_div_cancel h2,map_one]
  have ht : (T 1*T (-1) : K[T;T⁻¹])=1 := by rw [←T_add]; norm_num
  have hF : T 1*(originalFrobeniusSource p : K[T;T⁻¹])=
      T (p : ℤ)-T (-(p : ℤ)) := by
    rw [originalFrobeniusSource,mul_sub,←T_add,←T_add]
    congr 1 <;> congr 1 <;> omega
  have hscalar : (-8*WPFiniteNC122.q p/15 : K)-
      4*originalZE p u*(2/WPFiniteABSourceTail.epsilon p)+4*originalAlpha p=0 := by
    rw [originalZE_value p hp u hu]
    unfold originalAlpha
    field_simp [heps,h2,h15,h30]
    ring
  have hscalarC := congrArg LaurentPolynomial.C hscalar
  simp only [map_add,map_sub,map_mul,map_ofNat,map_zero] at hscalarC
  have hH := originalHsym_source_collected p hp u hu
  have hJ := originalJab_source (K:=K) p hp
  have hJQ : poleProduct*D (originalJa p+originalJb p)=
      originalK0 p*gammaANumerator+
        LaurentPolynomial.C (2/WPFiniteABSourceTail.epsilon p : K)*
          poleProduct*originalFrobeniusSource p := by
    unfold poleProduct gammaANumerator poleProductOverX
    linear_combination T 1*(T 1+1)*hJ-
      originalK0 p*(T 1+1)*(T 1-LaurentPolynomial.C (1/4 : K))*(T 1-4)*ht
  have hI := originalInvisibleP_correction p hp u
  have hk : invert (originalK0 p : K[T;T⁻¹])=originalK0 p := by
    simp only [originalK0,map_sub,map_mul,map_add,invert_C,invert_T,neg_neg]
    ring
  rw [fourPositiveSourceNumerator,originalS_factorization p hp u]
  simp only [originalP_decomposition p u,map_add,map_mul,hk,originalJlog_invert p hp]
  rw [originalUcan,map_sub,map_sub,D_mul,originalK0_derivative,
    zero_mul,zero_add,D_C_mul,D_C_mul,SourceClosureUniversalLog.originalJ2log_derivative]
  have hQ : (poleProduct : K[T;T⁻¹])=T 1*poleProductOverX := by
    unfold poleProduct poleProductOverX
    ring
  rw [hQ] at hH hJQ ⊢
  linear_combination
    originalK0 p*hH-4*LaurentPolynomial.C (originalZE p u)*hJQ-
    2*T 1*poleProductOverX*T (-1)*SourceClosureUniversalLog.originalJlog p*hhalf-
    2*poleProductOverX*SourceClosureUniversalLog.originalJlog p*ht+
    poleProductOverX*hI-
    LaurentPolynomial.C (-8*WPFiniteNC122.q p/15 : K)*poleProductOverX*hF+
    T 1*poleProductOverX*originalFrobeniusSource p*hscalarC

theorem linearPole_nonzero (c : K) :
    (T 1-LaurentPolynomial.C c : K[T;T⁻¹])≠0 := by
  intro hz
  have he := congrArg (fun P : K[T;T⁻¹] => P.coeff 1) hz
  simp only [AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,T_apply,
    original_coeff_C,if_neg (by decide : (0 : ℤ)≠1),sub_zero] at he
  exact one_ne_zero he

theorem fourPoleProduct_nonzero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (4*poleProduct : K[T;T⁻¹])≠0 := by
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hC4 : (LaurentPolynomial.C (4 : K) : K[T;T⁻¹])≠0 := by
    intro hz
    have he := congrArg (fun P : K[T;T⁻¹] => P.coeff 0) hz
    simp only [original_coeff_C] at he
    exact h4 he
  have hx : (T 1 : K[T;T⁻¹])≠0 := by
    have ht : (T 1*T (-1) : K[T;T⁻¹])=1 := by rw [←T_add]; norm_num
    intro hz
    rw [hz,zero_mul] at ht
    exact zero_ne_one ht
  have hm : (T 1+1 : K[T;T⁻¹])≠0 := by
    simpa only [map_neg,map_one,sub_neg_eq_add] using linearPole_nonzero (-1 : K)
  have hb : (T 1-4 : K[T;T⁻¹])≠0 := linearPole_nonzero (4 : K)
  have hq : (poleProduct : K[T;T⁻¹])≠0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hx hm) (linearPole_nonzero (1/4 : K))) hb
  exact mul_ne_zero (by simpa only [map_ofNat] using hC4) hq

theorem originalPositiveQuotient_exists (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    ∃ B : K[T;T⁻¹], 4*poleProduct*B=fourPositiveSourceNumerator p u := by
  refine ⟨D (originalUcan p u)+LaurentPolynomial.C (originalAlpha p)*
    originalFrobeniusSource p,?_⟩
  linear_combination originalUcan_positive_source p hp u hu

/-- The unique Laurent quotient of the original positive numerator. -/
noncomputable def originalBgamma (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) : K[T;T⁻¹] :=
  Classical.choose (originalPositiveQuotient_exists p hp u hu)

theorem originalBgamma_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    4*poleProduct*originalBgamma p hp u hu=fourPositiveSourceNumerator p u :=
  Classical.choose_spec (originalPositiveQuotient_exists p hp u hu)

theorem originalBgamma_unique (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) (B : K[T;T⁻¹])
    (hB : 4*poleProduct*B=fourPositiveSourceNumerator p u) :
    B=originalBgamma p hp u hu := by
  apply mul_left_cancel₀ (fourPoleProduct_nonzero p hp)
  rw [hB,originalBgamma_source]

/-- The full derivative follows from the original quotient, with no source premise. -/
theorem originalUcan_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    D (originalUcan p u)=originalBgamma p hp u hu-
      LaurentPolynomial.C (originalAlpha p)*originalFrobeniusSource p := by
  apply mul_left_cancel₀ (fourPoleProduct_nonzero p hp)
  rw [mul_sub,originalBgamma_source,originalUcan_positive_source p hp u hu]
  ring

theorem originalU_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    D (originalU p u)=originalBgamma p hp u hu-
      LaurentPolynomial.C (originalAlpha p)*originalFrobeniusSource p := by
  rw [originalU,map_sub,D_C,sub_zero,originalUcan_derivative p hp u hu]

end WPFieldAssembly.SourceClosureUVPositiveSource
