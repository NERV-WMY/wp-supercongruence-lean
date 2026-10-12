import WPFieldAssembly.ActualKwFiniteHBridge
import WPFiniteDReciprocity
import WPFiniteEntropy
import WPFiniteSignTrace

open scoped BigOperators

namespace WPFieldAssembly.ActualKwOrderedEndpoints

open Polynomial ActualKwFiniteHBridge ActualKwWeightedTrace

set_option maxHeartbeats 2400000

/- These are the original SB47 and UW18 carriers. Every D_N sum retains
the full k=j diagonal. Endpoint substitution precedes every contraction. -/

variable {K : Type*} [Field K]

private theorem two_ne_zero_of_four (h4 : (4 : K)≠0) : (2 : K)≠0 := by
  intro hz
  apply h4
  calc
    (4 : K)=2*2 := by ring
    _ = 0 := by rw [hz]; ring

noncomputable def originalG (p : ℕ) (s : K) : K :=
  WPFiniteLoop.D ((p-1)/2) (4*s) 4-WPFiniteLoop.D ((p-1)/2) s 1+
    2*WPFiniteLoop.D ((p-1)/2) (4*s) 1-2*WPFiniteLoop.D ((p-1)/2) s (1/4)

noncomputable def originalD5 (p : ℕ) (u : K) : K :=
  WPFiniteLoop.S p (2*u) (2*u)-WPFiniteLoop.S p u u

noncomputable def originalT5 (p : ℕ) (u : K) : K :=
  WPFiniteLoop.A p u-2*WPFiniteDReciprocity.At p u+
    WPFiniteDReciprocity.Bt p u+originalD5 p u

noncomputable def rationalOrderedRows (p : ℕ) : K :=
  (-4*(WPFiniteLoop.S p 1 2-WPFiniteLoop.S p (1/2) 1)+
    22*(WPFiniteLoop.S p 1 1-WPFiniteLoop.S p (1/2) (1/2))+
    11*(WPFiniteLoop.S p 2 2-WPFiniteLoop.S p 1 1)+
    7*(WPFiniteLoop.S p 2 1-WPFiniteLoop.S p 1 (1/2)))/10

noncomputable def movingTw (p : ℕ) : K :=
  -2*movingMinus p (1/4 : K) 4 (1/4)+movingMinus p (1/4 : K) 4 4-
    (4/5 : K)*((1/4 : K)*movingRplus p (1/4)+4*movingRplus p 4-
      (11/4 : K)*movingRplus p (11/4))

theorem literalF1_trace_movingTw (p : ℕ) [Fact p.Prime] (hp : 19≤p) (d : ZMod p) :
    (-3 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
      (ActualKwPhaseTrace.literalF1Laurent p*
        (LaurentPolynomial.C (1/15 : ZMod p)*(17-4*LaurentPolynomial.T (p : ℤ)-
          4*LaurentPolynomial.T (-(p : ℤ)))*
          (((WPFiniteWSource.deltaE p : (ZMod p)[X]).comp WPFiniteWSource.squaredCoordinate).toLaurent+
            LaurentPolynomial.invert
              ((WPFiniteWSource.deltaE p : (ZMod p)[X]).comp WPFiniteWSource.squaredCoordinate).toLaurent)+
          LaurentPolynomial.C d))=movingTw p := by
  exact literalF1_movingEven_Tw p hp d

theorem originalG_square (p : ℕ) (t : K) :
    originalG p (t^2)=WPFiniteLoop.B p t+2*WPFiniteLoop.A p t := by
  simp only [originalG,WPFiniteLoop.A,WPFiniteLoop.B,WPFiniteLoop.S]
  have h2 : (2*t)^2=4*t^2 := by ring
  have h22 : (2 : K)^2=4 := by norm_num
  have h12 : (1/2 : K)^2=1/4 := by
    simp only [div_pow,one_pow]
    norm_num
  rw [h2,h22,h12]
  ring

/-- The original four D_N terms are exactly the full signed trace. -/
theorem originalG_full_trace (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) (t : K) :
    originalG p (t^2)=
      WPFiniteSignTrace.fullTraceS p (2*t) 2-WPFiniteSignTrace.fullTraceS p t 1+
        2*WPFiniteSignTrace.fullTraceS p (2*t) 1-
          2*WPFiniteSignTrace.fullTraceS p t (1/2) := by
  simp only [WPFiniteSignTrace.full_trace_eq_half_cutoff p hp]
  rw [originalG_square]
  unfold WPFiniteLoop.A WPFiniteLoop.B
  ring

theorem originalG_c_full_trace (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p)
    (w : K) (hw : w^2=3/11) :
    originalG p (3/11)=
      WPFiniteSignTrace.fullTraceS p (2*w) 2-WPFiniteSignTrace.fullTraceS p w 1+
        2*WPFiniteSignTrace.fullTraceS p (2*w) 1-
          2*WPFiniteSignTrace.fullTraceS p w (1/2) := by
  rw [←hw]
  exact originalG_full_trace p hp w

theorem movingH_G_pair (p : ℕ) (v : K) (h4 : (4 : K)≠0) (h5 : (5 : K)≠0) :
    2*movingH p (1/4 : K) v+movingH p 4 v=
      (originalG p ((1+v)/5)-originalG p (1/5))/2 := by
  have hA : (4/5 : K)*(1+1/4)=1 := by field_simp [h4,h5]; ring
  have ha : (1/5 : K)*(1+1/4)=1/4 := by field_simp [h4,h5]; ring
  have hB : (4/5 : K)*(1+4)=4 := by field_simp [h5]; ring
  have hb : (1/5 : K)*(1+4)=1 := by field_simp [h5]; ring
  have hv : (4/5 : K)*(1+v)=4*((1+v)/5) := by ring
  have hv' : (1/5 : K)*(1+v)=(1+v)/5 := by ring
  have h45 : (4/5 : K)=4*(1/5) := by ring
  simp only [movingH,originalG]
  simp only [hA,ha,hB,hb]
  simp only [hv,hv']
  simp only [h45]
  field_simp [two_ne_zero_of_four h4]
  ring

theorem movingH_c_G (p : ℕ) (h4 : (4 : K)≠0) (h5 : (5 : K)≠0)
    (h11 : (11 : K)≠0) :
    2*movingH p (1/4 : K) (4/11)+movingH p 4 (4/11)=
      (originalG p (3/11)-originalG p (1/5))/2 := by
  have he : (1+(4/11 : K))/5=3/11 := by field_simp [h5,h11]; ring
  rw [movingH_G_pair p _ h4 h5,he]

theorem movingH_aa (p : ℕ) (u : K) (hu : u^2=1/5)
    (h4 : (4 : K)≠0) (h5 : (5 : K)≠0) :
    2*movingH p (1/4 : K) (1/4)=
      WPFiniteLoop.S p 1 1-WPFiniteLoop.S p (1/2) (1/2)-WPFiniteLoop.A p u := by
  have hA : (4/5 : K)*(1+1/4)=1 := by field_simp [h4,h5]; ring
  have ha : (1/5 : K)*(1+1/4)=1/4 := by field_simp [h4,h5]; ring
  have ht : (2*u)^2=4/5 := by
    calc
      (2*u)^2=(4 : K)*u^2 := by ring
      _ = 4/5 := by rw [hu]; ring
  have hh : (1/2 : K)^2=1/4 := by simp only [div_pow,one_pow]; norm_num
  simp only [movingH,hA,ha,WPFiniteLoop.A,WPFiniteLoop.S,ht,hu,hh,one_pow]
  field_simp [two_ne_zero_of_four h4]
  ring

theorem movingH_bb (p : ℕ) (u : K) (hu : u^2=1/5)
    (h2 : (2 : K)≠0) (h5 : (5 : K)≠0) :
    2*movingH p (4 : K) 4=
      WPFiniteLoop.S p 2 2-WPFiniteLoop.S p 1 1-WPFiniteLoop.B p u := by
  have hB : (4/5 : K)*(1+4)=4 := by field_simp [h5]; ring
  have hb : (1/5 : K)*(1+4)=1 := by field_simp [h5]; ring
  have ht : (2*u)^2=4/5 := by
    calc
      (2*u)^2=(4 : K)*u^2 := by ring
      _ = 4/5 := by rw [hu]; ring
  simp only [movingH,hB,hb,WPFiniteLoop.B,WPFiniteLoop.S,ht,hu,one_pow]
  norm_num only [show (2 : K)^2=4 by norm_num]
  field_simp [h2]
  ring

theorem movingH_ba (p : ℕ) (u : K) (hu : u^2=1/5)
    (h4 : (4 : K)≠0) (h5 : (5 : K)≠0) :
    2*movingH p (4 : K) (1/4)=
      WPFiniteLoop.S p 1 2-WPFiniteLoop.S p (1/2) 1-WPFiniteLoop.B p u := by
  have hA : (4/5 : K)*(1+1/4)=1 := by field_simp [h4,h5]; ring
  have ha : (1/5 : K)*(1+1/4)=1/4 := by field_simp [h4,h5]; ring
  have hB : (4/5 : K)*(1+4)=4 := by field_simp [h5]; ring
  have hb : (1/5 : K)*(1+4)=1 := by field_simp [h5]; ring
  have ht : (2*u)^2=4/5 := by
    calc
      (2*u)^2=(4 : K)*u^2 := by ring
      _ = 4/5 := by rw [hu]; ring
  have hh : (1/2 : K)^2=1/4 := by simp only [div_pow,one_pow]; norm_num
  simp only [movingH,hA,ha,hB,hb,WPFiniteLoop.B,WPFiniteLoop.S,ht,hu,hh,one_pow]
  norm_num only [show (2 : K)^2=4 by norm_num]
  field_simp [two_ne_zero_of_four h4]
  ring

theorem movingH_ab (p : ℕ) (u : K) (hu : u^2=1/5)
    (h4 : (4 : K)≠0) (h5 : (5 : K)≠0) :
    2*movingH p (1/4 : K) (4 : K)=
      WPFiniteLoop.S p 2 1-WPFiniteLoop.S p 1 (1/2)-WPFiniteLoop.A p u := by
  have hA : (4/5 : K)*(1+1/4)=1 := by field_simp [h4,h5]; ring
  have ha : (1/5 : K)*(1+1/4)=1/4 := by field_simp [h4,h5]; ring
  have hB : (4/5 : K)*(1+4)=4 := by field_simp [h5]; ring
  have hb : (1/5 : K)*(1+4)=1 := by field_simp [h5]; ring
  have ht : (2*u)^2=4/5 := by
    calc
      (2*u)^2=(4 : K)*u^2 := by ring
      _ = 4/5 := by rw [hu]; ring
  have hh : (1/2 : K)^2=1/4 := by simp only [div_pow,one_pow]; norm_num
  simp only [movingH,hA,ha,hB,hb,WPFiniteLoop.A,WPFiniteLoop.S,ht,hu,hh,one_pow]
  norm_num only [show (2 : K)^2=4 by norm_num]
  field_simp [two_ne_zero_of_four h4]
  ring

theorem movingH_zero_a (p : ℕ) (u : K) (hu : u^2=1/5)
    (h4 : (4 : K)≠0) (h5 : (5 : K)≠0) :
    2*movingH p (0 : K) (1/4)=WPFiniteDReciprocity.At p u-originalD5 p u := by
  have hA : (4/5 : K)*(1+1/4)=1 := by field_simp [h4,h5]; ring
  have ha : (1/5 : K)*(1+1/4)=1/4 := by field_simp [h4,h5]; ring
  have ht : (2*u)^2=4/5 := by
    calc
      (2*u)^2=(4 : K)*u^2 := by ring
      _ = 4/5 := by rw [hu]; ring
  have hh : (1/2 : K)^2=1/4 := by simp only [div_pow,one_pow]; norm_num
  simp only [movingH,hA,ha,add_zero,mul_one,WPFiniteDReciprocity.At,
    originalD5,WPFiniteLoop.S,ht,hu,hh,one_pow]
  field_simp [two_ne_zero_of_four h4]
  ring

theorem movingH_zero_b (p : ℕ) (u : K) (hu : u^2=1/5)
    (h2 : (2 : K)≠0) (h5 : (5 : K)≠0) :
    2*movingH p (0 : K) 4=WPFiniteDReciprocity.Bt p u-originalD5 p u := by
  have hB : (4/5 : K)*(1+4)=4 := by field_simp [h5]; ring
  have hb : (1/5 : K)*(1+4)=1 := by field_simp [h5]; ring
  have ht : (2*u)^2=4/5 := by
    calc
      (2*u)^2=(4 : K)*u^2 := by ring
      _ = 4/5 := by rw [hu]; ring
  simp only [movingH,hB,hb,add_zero,mul_one,WPFiniteDReciprocity.Bt,
    originalD5,WPFiniteLoop.S,ht,hu,one_pow]
  norm_num only [show (2 : K)^2=4 by norm_num]
  field_simp [h2]
  ring

theorem fifthOrdered_T5 (p : ℕ) (u : K) (hu : u^2=1/5)
    (h2 : (2 : K)≠0) (h5 : (5 : K)≠0) :
    3*WPFiniteDReciprocity.At p u-3*WPFiniteDReciprocity.Bt p u/2-
      3*originalD5 p u/2-7*WPFiniteLoop.A p u/10+2*WPFiniteLoop.B p u/5=
        -3*originalT5 p u/2+2*originalG p (1/5)/5 := by
  rw [←hu,originalG_square]
  unfold originalT5
  have h10 : (10 : K)≠0 := by (convert mul_ne_zero h2 h5 using 1; norm_num)
  field_simp [h2,h5,h10]
  ring

theorem movingTw_ordered_raw (p : ℕ) (h4 : (4 : K)≠0) (h5 : (5 : K)≠0)
    (h11 : (11 : K)≠0) :
    movingTw (K:=K) p=
      (4*movingH p 4 (1/4)-22*movingH p (1/4) (1/4)-
        11*movingH p 4 4-7*movingH p (1/4) 4)/5+
      (11/10 : K)*(originalG p (3/11)-originalG p (1/5))-
        6*movingH p 0 (1/4)+3*movingH p 0 4+
      movingDend p/5*(11*(2*finiteLogValue p (16/11)+finiteLogValue p (1/11))-
        2*finiteLogValue p 16-33*finiteLogValue p 1-16*finiteLogValue p (1/16)) := by
  have h2 := two_ne_zero_of_four h4
  have h10 : (10 : K)≠0 := by (convert mul_ne_zero h2 h5 using 1; norm_num)
  have h16 : (16 : K)≠0 := by (convert mul_ne_zero h4 h4 using 1; norm_num)
  have hinva : ((1/4 : K)⁻¹)=4 := by simp only [one_div,inv_inv]
  have hinvb : ((4 : K)⁻¹)=1/4 := by simp only [one_div]
  have hinvc : ((11/4 : K)⁻¹)=4/11 := by field_simp [h4,h11]
  have hab : (4/(1/4 : K))=16 := by (field_simp [h4]; ring)
  have haa : ((1/4 : K)/(1/4))=1 := div_self (one_div_ne_zero h4)
  have hbb : ((4 : K)/4)=1 := div_self h4
  have hba : ((1/4 : K)/4)=1/16 := by (field_simp [h4,h16]; ring)
  have hbc : ((4 : K)/(11/4))=16/11 := by (field_simp [h4,h11]; ring)
  have hac : ((1/4 : K)/(11/4))=1/11 := by field_simp [h4,h11]
  have hG := movingH_c_G (K:=K) p h4 h5 h11
  have hG' : (2*movingH p (1/4 : K) (4/11)+movingH p 4 (4/11))*2=
      originalG p (3/11)-originalG p (1/5) := (eq_div_iff h2).1 hG
  rw [←hG']
  unfold movingTw movingMinus movingRplus
  rw [hinva,hinvb,hinvc,hab,haa,hbb,hba,hbc,hac]
  field_simp [h2,h5,h10]
  ring

theorem finiteLog_one (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    finiteLogValue p (1 : K)=0 := by
  have he := congrArg (ZMod.castHom (dvd_refl p) K)
    (WPFiniteInversion.ell_one_eq_zero p (by omega))
  simpa only [←WPFiniteField.ell_castHom,map_one,map_zero,
    WPFiniteField.ell,finiteLogValue] using he

theorem finiteLog_sixteen_inverse (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    16*finiteLogValue p (1/16 : K)=-finiteLogValue p (16 : K) := by
  have h16 : (16 : K)≠0 := WPFiniteField.denominator_ne_zero p 16
    (Finset.mem_Ico.mpr (by omega))
  have hpow : (16 : K)^p=16 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K:=K) p 16
  have he := WPFiniteField.ell_inversion p (16 : K) h16
  rw [hpow] at he
  change finiteLogValue p (16 : K)⁻¹=-(16 : K)⁻¹*finiteLogValue p (16 : K) at he
  simp only [←one_div] at he
  field_simp [h16] at he
  linear_combination he

/-- Exact SB103d ordered expression before the literal Q11 entropy reduction. -/
theorem movingTw_ordered (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    movingTw (K:=K) p=
      (4*movingH p 4 (1/4)-22*movingH p (1/4) (1/4)-
        11*movingH p 4 4-7*movingH p (1/4) 4)/5+
      (11/10 : K)*(originalG p (3/11)-originalG p (1/5))-
        6*movingH p 0 (1/4)+3*movingH p 0 4+
      movingDend p/5*(11*(2*finiteLogValue p (16/11)+finiteLogValue p (1/11))-
        finiteLogValue p 16) := by
  have hu (n : ℕ) (hn : 0<n) (hlt : n<p) : (n : K)≠0 :=
    WPFiniteField.denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hn,hlt⟩)
  rw [movingTw_ordered_raw p (hu 4 (by omega) (by omega))
    (hu 5 (by omega) (by omega)) (hu 11 (by omega) (by omega)),finiteLog_one p hp]
  have he := finiteLog_sixteen_inverse (K:=K) p hp
  linear_combination -(movingDend p/5)*he

/-- The original T5 and both G carriers are retained, together with every rational sign row. -/
theorem movingTw_fifth_ordered (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p)
    (u : K) (hu : u^2=1/5) :
    -movingTw (K:=K) p=rationalOrderedRows p-3*originalT5 p u/2+
      2*originalG p (1/5)/5-11*originalG p (3/11)/10-
        movingDend p/5*(11*(2*finiteLogValue p (16/11)+finiteLogValue p (1/11))-
          finiteLogValue p 16) := by
  have hn (n : ℕ) (hpos : 0<n) (hlt : n<p) : (n : K)≠0 :=
    WPFiniteField.denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hpos,hlt⟩)
  have h2 : (2 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 2 (by omega) (by omega)
  have h4 : (4 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 4 (by omega) (by omega)
  have h5 : (5 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 5 (by omega) (by omega)
  have h10 : (10 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 10 (by omega) (by omega)
  have haa := movingH_aa p u hu h4 h5
  have hbb := movingH_bb p u hu h2 h5
  have hba := movingH_ba p u hu h4 h5
  have hab := movingH_ab p u hu h4 h5
  have h0a := movingH_zero_a p u hu h4 h5
  have h0b := movingH_zero_b p u hu h2 h5
  have hg : originalG p (1/5 : K)=WPFiniteLoop.B p u+2*WPFiniteLoop.A p u := by
    rw [←hu,originalG_square]
  rw [movingTw_ordered p hp]
  rw [hg]
  unfold rationalOrderedRows originalT5
  have hdiv (x y : K) (he : 2*x=y) : x=y/2 :=
    (eq_div_iff h2).2 (by simpa only [mul_comm] using he)
  rw [hdiv _ _ haa,hdiv _ _ hbb,hdiv _ _ hba,hdiv _ _ hab,
    hdiv _ _ h0a,hdiv _ _ h0b]
  field_simp [h2,h5,h10]
  ring

section IntegerEntropy

/-- The entire homogeneous entropy quotient is formed in the integers. -/
def integerEntropyPair (p : ℕ) (a t : ℤ) : ℤ :=
  (t^p-a^p-(t-a)^p)/(p : ℤ)

theorem integerEntropyPair_source (p : ℕ) [Fact p.Prime] (hp : 3≤p) (a t : ℤ) :
    t^p-a^p-(t-a)^p=(p : ℤ)*
      (-(∑ j∈Finset.Ico 1 p, ((p.choose j : ℤ)/(p : ℤ))*(-a)^j*t^(p-j))) := by
  have hprime : p.Prime := Fact.out
  have hodd := hprime.odd_of_ne_two (by omega)
  have hbin := add_pow (-a) t p
  rw [Finset.sum_range_succ,←Finset.sum_range_add_sum_Ico _ hprime.one_le] at hbin
  simp only [Finset.sum_range_one,pow_zero,Nat.choose_zero_right,Nat.cast_one,
    mul_one,Nat.choose_self,Nat.sub_self,Nat.sub_zero,one_mul,hodd.neg_pow] at hbin
  have hsum : (∑ j∈Finset.Ico 1 p, (-a)^j*t^(p-j)*(p.choose j : ℤ))=
      (p : ℤ)*(∑ j∈Finset.Ico 1 p, ((p.choose j : ℤ)/(p : ℤ))*(-a)^j*t^(p-j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hd : (p : ℤ)∣(p.choose j : ℤ) := by
      exact_mod_cast hprime.dvd_choose_self (by have := (Finset.mem_Ico.mp hj).1; omega)
        (Finset.mem_Ico.mp hj).2
    rw [←mul_assoc,←mul_assoc,Int.mul_ediv_cancel' hd]
    ring
  rw [show -a+t=t-a by ring,hsum] at hbin
  linear_combination -hbin

theorem integerEntropyPair_binomial (p : ℕ) [Fact p.Prime] (hp : 3≤p) (a t : ℤ) :
    integerEntropyPair p a t=
      -(∑ j∈Finset.Ico 1 p, ((p.choose j : ℤ)/(p : ℤ))*(-a)^j*t^(p-j)) := by
  have hs := integerEntropyPair_source p hp a t
  have hd : (p : ℤ)∣t^p-a^p-(t-a)^p := ⟨_,hs⟩
  apply mul_right_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℤ)≠0)
  rw [integerEntropyPair,Int.ediv_mul_cancel hd,hs]
  ring

theorem integerEntropyPair_cast (p : ℕ) [Fact p.Prime] (hp : 3≤p)
    (a t : ℤ) (ht : (t : ZMod p)≠0) :
    (integerEntropyPair p a t : ZMod p)=(t : ZMod p)*
      finiteLogValue p ((a : ZMod p)/(t : ZMod p)) := by
  rw [integerEntropyPair_binomial p hp]
  push_cast
  rw [←Finset.sum_neg_distrib]
  have htF : (t : ZMod p)^p=(t : ZMod p) := by
    exact ZMod.pow_card _
  conv_rhs => lhs; rw [←htF]
  rw [finiteLogValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [WPFiniteInversion.divided_choose_cast p j hj,neg_pow,
    pow_sub₀ _ ht (Finset.mem_Ico.mp hj).2.le,div_pow]
  have hs : (-1 : ZMod p)^(j-1)*(-1)^j=-1 := by
    have he : (-1 : ZMod p)^j=(-1)^(j-1)*(-1) := by
      rw [←pow_succ,Nat.sub_add_cancel (Finset.mem_Ico.mp hj).1]
    rw [he]
    calc
      _ = -((-1 : ZMod p)^(j-1))^2 := by ring
      _ = -1 := by rw [←pow_mul,Nat.mul_comm,pow_mul]; norm_num
  simp only [div_eq_mul_inv]
  linear_combination -((a : ZMod p)^j*(t : ZMod p)^p*((t : ZMod p)^j)⁻¹*
    (j : ZMod p)⁻¹)*hs

theorem integerEntropyPair_fermat (p : ℕ) [Fact p.Prime]
    (a t : ℤ) (ha : (a : ZMod p)≠0) (ht : (t : ZMod p)≠0)
    (hb : ((t-a : ℤ) : ZMod p)≠0) :
    integerEntropyPair p a t=t*WPFiniteInversion.integerFermatQuotient p t-
      a*WPFiniteInversion.integerFermatQuotient p a-
        (t-a)*WPFiniteInversion.integerFermatQuotient p (t-a) := by
  have hprime : p.Prime := Fact.out
  have hp0 : (p : ℤ)≠0 := by exact_mod_cast hprime.ne_zero
  have hqA := WPFiniteInversion.integerFermatQuotient_mul p a ha
  have hqT := WPFiniteInversion.integerFermatQuotient_mul p t ht
  have hqB := WPFiniteInversion.integerFermatQuotient_mul p (t-a) hb
  have hpow (z : ℤ) : z^p=z^(p-1)*z := by
    rw [←pow_succ,Nat.sub_add_cancel hprime.one_le]
  have hs : t^p-a^p-(t-a)^p=(p : ℤ)*
      (t*WPFiniteInversion.integerFermatQuotient p t-
        a*WPFiniteInversion.integerFermatQuotient p a-
          (t-a)*WPFiniteInversion.integerFermatQuotient p (t-a)) := by
    rw [hpow t,hpow a,hpow (t-a)]
    linear_combination -t*hqT+a*hqA+(t-a)*hqB
  have hd : (p : ℤ)∣t^p-a^p-(t-a)^p := ⟨_,hs⟩
  apply mul_right_cancel₀ hp0
  rw [integerEntropyPair,Int.ediv_mul_cancel hd,hs]
  ring

theorem finiteLog_fraction_fermat (p : ℕ) [Fact p.Prime] (hp : 3≤p)
    (a t : ℤ) (ha : (a : ZMod p)≠0) (ht : (t : ZMod p)≠0)
    (hb : ((t-a : ℤ) : ZMod p)≠0) :
    finiteLogValue p ((a : ZMod p)/(t : ZMod p))=
      (WPFiniteInversion.integerFermatQuotient p t : ZMod p)-
        (a : ZMod p)/(t : ZMod p)*(WPFiniteInversion.integerFermatQuotient p a : ZMod p)-
          ((t-a : ℤ) : ZMod p)/(t : ZMod p)*
            (WPFiniteInversion.integerFermatQuotient p (t-a) : ZMod p) := by
  have he := integerEntropyPair_cast p hp a t ht
  rw [integerEntropyPair_fermat p a t ha ht hb] at he
  push_cast at he
  have hm : (t : ZMod p)*
      ((WPFiniteInversion.integerFermatQuotient p t : ZMod p)-
        (a : ZMod p)/(t : ZMod p)*(WPFiniteInversion.integerFermatQuotient p a : ZMod p)-
          ((t-a : ℤ) : ZMod p)/(t : ZMod p)*
            (WPFiniteInversion.integerFermatQuotient p (t-a) : ZMod p))=
      (t : ZMod p)*(WPFiniteInversion.integerFermatQuotient p t : ZMod p)-
        (a : ZMod p)*(WPFiniteInversion.integerFermatQuotient p a : ZMod p)-
          ((t-a : ℤ) : ZMod p)*
            (WPFiniteInversion.integerFermatQuotient p (t-a) : ZMod p) := by
    field_simp [ht]
  apply mul_left_cancel₀ ht
  rw [hm]
  simpa only [Int.cast_sub] using he.symm

theorem integerFermatQuotient_product (p : ℕ) [Fact p.Prime]
    (a b : ℤ) (ha : (a : ZMod p)≠0) (hb : (b : ZMod p)≠0) :
    WPFiniteInversion.integerFermatQuotient p (a*b)=
      WPFiniteInversion.integerFermatQuotient p a+WPFiniteInversion.integerFermatQuotient p b+
        (p : ℤ)*WPFiniteInversion.integerFermatQuotient p a*
          WPFiniteInversion.integerFermatQuotient p b := by
  have hab : ((a*b : ℤ) : ZMod p)≠0 := by simpa only [Int.cast_mul] using mul_ne_zero ha hb
  have hqa := WPFiniteInversion.integerFermatQuotient_mul p a ha
  have hqb := WPFiniteInversion.integerFermatQuotient_mul p b hb
  have hqab := WPFiniteInversion.integerFermatQuotient_mul p (a*b) hab
  apply mul_right_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℤ)≠0)
  rw [hqab,mul_pow]
  linear_combination -(b^(p-1))*hqa-
    (1+(p : ℤ)*WPFiniteInversion.integerFermatQuotient p a)*hqb

theorem integerFermatQuotient_product_cast (p : ℕ) [Fact p.Prime]
    (a b : ℤ) (ha : (a : ZMod p)≠0) (hb : (b : ZMod p)≠0) :
    (WPFiniteInversion.integerFermatQuotient p (a*b) : ZMod p)=
      (WPFiniteInversion.integerFermatQuotient p a : ZMod p)+
        (WPFiniteInversion.integerFermatQuotient p b : ZMod p) := by
  rw [integerFermatQuotient_product p a b ha hb]
  simp

end IntegerEntropy

theorem integerFermatQuotient_neg (p : ℕ) [Fact p.Prime] (hp : 3≤p) (a : ℤ) :
    WPFiniteInversion.integerFermatQuotient p (-a)=
      WPFiniteInversion.integerFermatQuotient p a := by
  have heven : Even (p-1) := by
    rcases (Fact.out : p.Prime).odd_of_ne_two (by omega) with ⟨n,hn⟩
    exact ⟨n,by omega⟩
  unfold WPFiniteInversion.integerFermatQuotient
  rw [heven.neg_pow]

theorem finiteLog_c_ordered_zmod (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    finiteLogValue p (16/11 : ZMod p)=
      (WPFiniteInversion.integerFermatQuotient p 11 : ZMod p)-
        (64/11 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)+
          (5/11 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 5 : ZMod p) ∧
    finiteLogValue p (1/11 : ZMod p)=
      (WPFiniteInversion.integerFermatQuotient p 11 : ZMod p)-
        (10/11 : ZMod p)*((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)+
          (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)) ∧
    finiteLogValue p (16 : ZMod p)=
      15*((WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)+
        (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p))-
          64*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
  have hu (n : ℕ) (hn : 0<n) (hlt : n<p) : (n : ZMod p)≠0 :=
    WPFiniteInversion.denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hn,hlt⟩)
  have h2 := hu 2 (by omega) (by omega)
  have h3 := hu 3 (by omega) (by omega)
  have h4 := hu 4 (by omega) (by omega)
  have h5 := hu 5 (by omega) (by omega)
  have h10 := hu 10 (by omega) (by omega)
  have h11 := hu 11 (by omega) (by omega)
  have h15 := hu 15 (by omega) (by omega)
  have h16 := hu 16 (by omega) (by omega)
  have hq16 := integerFermatQuotient_product_cast p 4 4
    (by simpa only [Int.cast_ofNat,Nat.cast_ofNat] using h4)
    (by simpa only [Int.cast_ofNat,Nat.cast_ofNat] using h4)
  norm_num only [show (4*4 : ℤ)=16 by norm_num] at hq16
  rw [WPFiniteInversion.integerFermatQuotient_four_cast p (by omega)] at hq16
  have hq10 := integerFermatQuotient_product_cast p 2 5
    (by simpa only [Int.cast_ofNat,Nat.cast_ofNat] using h2)
    (by simpa only [Int.cast_ofNat,Nat.cast_ofNat] using h5)
  norm_num only [show (2*5 : ℤ)=10 by norm_num] at hq10
  have hq15 := integerFermatQuotient_product_cast p 3 5
    (by simpa only [Int.cast_ofNat,Nat.cast_ofNat] using h3)
    (by simpa only [Int.cast_ofNat,Nat.cast_ofNat] using h5)
  norm_num only [show (3*5 : ℤ)=15 by norm_num] at hq15
  have hc := finiteLog_fraction_fermat p (by omega) 16 11
    (by simpa only [Int.cast_ofNat,Nat.cast_ofNat] using h16)
    (by simpa only [Int.cast_ofNat,Nat.cast_ofNat] using h11)
    (by simpa only [show (11-16 : ℤ)=-5 by norm_num,Int.cast_neg,Int.cast_ofNat,Nat.cast_ofNat]
      using neg_ne_zero.mpr h5)
  have hd := finiteLog_fraction_fermat p (by omega) 1 11 (by norm_num)
    (by simpa only [Int.cast_ofNat,Nat.cast_ofNat] using h11)
    (by simpa only [show (11-1 : ℤ)=10 by norm_num,Int.cast_ofNat,Nat.cast_ofNat] using h10)
  norm_num only [Int.cast_ofNat,show (11-16 : ℤ)=-5 by norm_num,
    show (11-1 : ℤ)=10 by norm_num,Int.cast_neg,sub_zero] at hc hd
  rw [integerFermatQuotient_neg p (by omega) 5,hq16] at hc
  rw [hq10] at hd
  have hs' := finiteLog_fraction_fermat p (by omega) 16 1
    (by simpa only [Int.cast_ofNat,Nat.cast_ofNat] using h16) (by norm_num)
    (by simpa only [show (1-16 : ℤ)=-15 by norm_num,Int.cast_neg,Int.cast_ofNat,Nat.cast_ofNat]
      using neg_ne_zero.mpr h15)
  norm_num only [Int.cast_ofNat,show (1-16 : ℤ)=-15 by norm_num,Int.cast_neg,div_one] at hs'
  rw [integerFermatQuotient_neg p (by omega) 15,hq16,hq15] at hs'
  have hq1 : WPFiniteInversion.integerFermatQuotient p 1=0 := by
    simp only [WPFiniteInversion.integerFermatQuotient,one_pow,sub_self,Int.zero_ediv]
  rw [hq1,Int.cast_zero] at hd hs'
  refine ⟨?_,?_,?_⟩
  · rw [hc]
    ring
  · rw [hd]
    ring
  · rw [hs']
    ring

theorem finiteLog_c_ordered (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    2*finiteLogValue p (16/11 : K)+finiteLogValue p (1/11 : K)=
      3*(WPFiniteInversion.integerFermatQuotient p 11 : K)-
        (138/11 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K) ∧
    finiteLogValue p (16 : K)=
      15*((WPFiniteInversion.integerFermatQuotient p 3 : K)+
        (WPFiniteInversion.integerFermatQuotient p 5 : K))-
          64*(WPFiniteInversion.integerFermatQuotient p 2 : K) := by
  rcases finiteLog_c_ordered_zmod p hp with ⟨hc,hd,hs⟩
  let f : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hm (z : ZMod p) : f (finiteLogValue p z)=finiteLogValue p (f z) := by
    simp only [finiteLogValue,map_sum,map_div₀,map_pow,map_natCast]
  have hc' := congrArg f hc
  have hd' := congrArg f hd
  have hs' := congrArg f hs
  simp only [hm,map_div₀,map_ofNat,map_one,map_sub,map_add,map_mul,map_intCast] at hc' hd' hs'
  refine ⟨?_,hs'⟩
  rw [hc',hd']
  ring

theorem movingTw_SB103d (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    movingTw (K:=K) p=
      (4*movingH p 4 (1/4)-22*movingH p (1/4) (1/4)-
        11*movingH p 4 4-7*movingH p (1/4) 4)/5+
      (11/10 : K)*(originalG p (3/11)-originalG p (1/5))-
        6*movingH p 0 (1/4)+3*movingH p 0 4+
      movingDend p/5*(33*(WPFiniteInversion.integerFermatQuotient p 11 : K)-
        138*(WPFiniteInversion.integerFermatQuotient p 2 : K)-finiteLogValue p 16) := by
  have h11 : (11 : K)≠0 := WPFiniteField.denominator_ne_zero p 11
    (Finset.mem_Ico.mpr (by omega))
  rw [movingTw_ordered p hp,(finiteLog_c_ordered (K:=K) p hp).1]
  field_simp [h11]
  ring

theorem movingTw_SB103e (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p)
    (u : K) (hu : u^2=1/5) :
    -movingTw (K:=K) p=rationalOrderedRows p-3*originalT5 p u/2+
      2*originalG p (1/5)/5-11*originalG p (3/11)/10-
        movingDend p/5*(33*(WPFiniteInversion.integerFermatQuotient p 11 : K)-
          138*(WPFiniteInversion.integerFermatQuotient p 2 : K)-finiteLogValue p 16) := by
  have h11 : (11 : K)≠0 := WPFiniteField.denominator_ne_zero p 11
    (Finset.mem_Ico.mpr (by omega))
  rw [movingTw_fifth_ordered p hp u hu,(finiteLog_c_ordered (K:=K) p hp).1]
  field_simp [h11]
  ring

/-- The original UW18f T5 cancels in this exact weighted contribution. -/
theorem original_T5_consumer_cancellation (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    (2/3 : K)*(-movingTw p)+originalT5 p u=
      (2/3 : K)*rationalOrderedRows p+(4/15 : K)*originalG p (1/5)-
        (11/15 : K)*originalG p (3/11)-2*movingDend p/15*
          (33*(WPFiniteInversion.integerFermatQuotient p 11 : K)-
            138*(WPFiniteInversion.integerFermatQuotient p 2 : K)-finiteLogValue p 16) := by
  have hn (n : ℕ) (hpos : 0<n) (hlt : n<p) : (n : K)≠0 :=
    WPFiniteField.denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hpos,hlt⟩)
  have h2 : (2 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 2 (by omega) (by omega)
  have h3 : (3 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 3 (by omega) (by omega)
  have h5 : (5 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 5 (by omega) (by omega)
  have h10 : (10 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 10 (by omega) (by omega)
  have h15 : (15 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 15 (by omega) (by omega)
  rw [movingTw_SB103e p hp u hu]
  field_simp [h2,h3,h5,h10,h15]
  ring

/-- The exact original logarithm quotients remain attached to both G carriers. -/
theorem original_T5_consumer_fermat (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    (2/3 : K)*(-movingTw p)+originalT5 p u=
      (2/3 : K)*rationalOrderedRows p+(4/15 : K)*originalG p (1/5)-
        (11/15 : K)*originalG p (3/11)-(2/15 : K)*
          ((WPFiniteInversion.integerFermatQuotient p 2 : K)+
            3*(WPFiniteInversion.integerFermatQuotient p 3 : K)/4)*
          (33*(WPFiniteInversion.integerFermatQuotient p 11 : K)-
            74*(WPFiniteInversion.integerFermatQuotient p 2 : K)-
              15*(WPFiniteInversion.integerFermatQuotient p 3 : K)-
                15*(WPFiniteInversion.integerFermatQuotient p 5 : K)) := by
  rw [original_T5_consumer_cancellation p hp u hu,movingDend_fermat p hp,
    (finiteLog_c_ordered (K:=K) p hp).2]
  ring

end WPFieldAssembly.ActualKwOrderedEndpoints
