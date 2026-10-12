import WPFieldAssembly.ActualKwRationalRowAttachment
import WPFieldAssembly.ActualBpairHAttachment
import WPFiniteFifthSourceContraction

namespace WPFieldAssembly.NativeClosureMixedJ

open ActualKwFiniteHBridge ActualKwOrderedEndpoints ActualKwRationalRowAttachment
open ActualRationalSignRows ActualBpairContraction WPFiniteField

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/-- The six original ordered primitives in the normalized HPJ part.
The separate source transport from the W-unit primitives is not assumed here. -/
noncomputable def HPJRow (p : ℕ) : K :=
  (208/225 : K)*branchH p (1/4) (1/4)+(368/225 : K)*branchH p 4 (1/4)-
    (43/225 : K)*branchH p (1/4) 4-(38/225 : K)*branchH p 4 4-
    (22/5 : K)*branchH p 0 (1/4)+(11/5 : K)*branchH p 0 4

/-- The six primitive coefficients from the raw mixed-J residue calculation. -/
noncomputable def mixedJHRow (p : ℕ) : K :=
  -(232/225 : K)*branchH p (1/4) (1/4)-(76/45 : K)*branchH p 4 (1/4)+
    (67/225 : K)*branchH p (1/4) 4+(2/9 : K)*branchH p 4 4+
    (176/75 : K)*branchH p 0 (1/4)-(11/75 : K)*branchH p 0 4

/-- This particular seven-row bracket cancels its full R(-2) coefficient. -/
theorem mixedJ_ordered_bracket (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    3*WPFiniteLoop.S p (1 : K) 1-2*WPFiniteLoop.S p (1/2 : K) (1/2)+
      WPFiniteLoop.S p (1 : K) 2-WPFiniteLoop.S p (1/2 : K) 1-
      2*WPFiniteLoop.S p (2 : K) 1+2*WPFiniteLoop.S p (1 : K) (1/2)-
      WPFiniteLoop.S p (2 : K) 2 =
        12*(q2 (K:=K) p-3*q3 p/4)^2 := by
  have hn (n : ℕ) (hpos : 0<n) (hlt : n<p) : (n : K)≠0 :=
    denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hpos,hlt⟩)
  have h2 : (2 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 2 (by omega) (by omega)
  have h3 : (3 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 3 (by omega) (by omega)
  have h4 : (4 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 4 (by omega) (by omega)
  have h6 : (6 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 6 (by omega) (by omega)
  have h12 : (12 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 12 (by omega) (by omega)
  rw [native_S_one_one p hp,native_S_half_half p hp,native_S_one_two p hp,
    native_S_half_one p hp,native_S_two_one p hp,native_S_one_half p hp,
    native_S_two_two p hp]
  field_simp [h2,h3,h4,h6,h12]
  ring

/-- The actual six finite H endpoints contract jointly, before any T5 dictionary. -/
theorem mixedJ_movingH_joint (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    -(8/75 : K)*movingH p (1/4) (1/4)-(4/75 : K)*movingH p 4 (1/4)+
      (8/75 : K)*movingH p (1/4) 4+(4/75 : K)*movingH p 4 4-
      (154/75 : K)*movingH p 0 (1/4)+(154/75 : K)*movingH p 0 4 =
        (77/75 : K)*(WPFiniteDReciprocity.Bt p u-WPFiniteDReciprocity.At p u)-
          (8/25 : K)*(q2 (K:=K) p-3*q3 p/4)^2 := by
  have hn (n : ℕ) (hpos : 0<n) (hlt : n<p) : (n : K)≠0 :=
    denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hpos,hlt⟩)
  have h2 : (2 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 2 (by omega) (by omega)
  have h3 : (3 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 3 (by omega) (by omega)
  have h4 : (4 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 4 (by omega) (by omega)
  have h5 : (5 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 5 (by omega) (by omega)
  have h25 : (25 : K)≠0 := by
    rw [show (25 : K)=5^2 by ring]; exact pow_ne_zero _ h5
  have h75 : (75 : K)≠0 := by
    rw [show (75 : K)=3*5^2 by ring]; exact mul_ne_zero h3 (pow_ne_zero _ h5)
  have haa := movingH_aa p u hu h4 h5
  have hba := movingH_ba p u hu h4 h5
  have hab := movingH_ab p u hu h4 h5
  have hbb := movingH_bb p u hu h2 h5
  have h0a := movingH_zero_a p u hu h4 h5
  have h0b := movingH_zero_b p u hu h2 h5
  have hb := mixedJ_ordered_bracket (K:=K) p hp
  have hnumer :
      -8*movingH p (1/4) (1/4)-4*movingH p 4 (1/4)+
        8*movingH p (1/4) 4+4*movingH p 4 4-
        154*movingH p 0 (1/4)+154*movingH p 0 4 =
      77*(WPFiniteDReciprocity.Bt p u-WPFiniteDReciprocity.At p u)-
        2*(3*WPFiniteLoop.S p (1 : K) 1-2*WPFiniteLoop.S p (1/2 : K) (1/2)+
          WPFiniteLoop.S p (1 : K) 2-WPFiniteLoop.S p (1/2 : K) 1-
          2*WPFiniteLoop.S p (2 : K) 1+2*WPFiniteLoop.S p (1 : K) (1/2)-
          WPFiniteLoop.S p (2 : K) 2) := by
    linear_combination -4*haa-2*hba+4*hab+2*hbb-77*h0a+77*h0b
  rw [hb] at hnumer
  calc
    _ = ((-8 : K)*movingH p (1/4) (1/4)-4*movingH p 4 (1/4)+
        8*movingH p (1/4) 4+4*movingH p 4 4-
        154*movingH p 0 (1/4)+154*movingH p 0 4)/75 := by ring
    _ = _ := by
      rw [hnumer]
      field_simp [h4,h25,h75]
      ring

/-- All k=i diagonals remain in the genuine branchH source and ordered rows. -/
theorem actual_HPJ_mixedJ_H_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    HPJRow (K:=K) p+mixedJHRow p =
      (77/75 : K)*(WPFiniteDReciprocity.Bt p u-WPFiniteDReciprocity.At p u)-
        (8/25 : K)*(q2 (K:=K) p-3*q3 p/4)^2 := by
  have h3 : (3 : K)≠0 := denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h9 : (9 : K)≠0 := by
    rw [show (9 : K)=3^2 by ring]; exact pow_ne_zero _ h3
  have h45 : (45 : K)≠0 := by
    rw [show (45 : K)=3^2*5 by ring]; exact mul_ne_zero (pow_ne_zero _ h3) h5
  have h75 : (75 : K)≠0 := by
    rw [show (75 : K)=3*5^2 by ring]; exact mul_ne_zero h3 (pow_ne_zero _ h5)
  have h225 : (225 : K)≠0 := by
    rw [show (225 : K)=3^2*5^2 by ring]; exact mul_ne_zero (pow_ne_zero _ h3) (pow_ne_zero _ h5)
  rw [HPJRow,mixedJHRow]
  simp only [branchH_movingH p hp]
  rw [←mixedJ_movingH_joint p hp u hu]
  field_simp [h5,h9,h45,h75,h225]
  ring

/-- Original a0=L(T0)-h is retained; the Q3 coefficient cancels in E(T0). -/
theorem actual_even_T0 (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p)
    (u : K) (hu : u^2=1/5) :
    E p (WPFiniteNC122.T0 u) =
      11*WPFifthEntropy.C p u/5-(16/5 : K)*q2 p+
        (3/2 : K)*(WPFiniteInversion.integerFermatQuotient p 5 : K) := by
  have h2 : (2 : K)≠0 := denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have he := WPFiniteFifthSourceContraction.actual_a0_fifth p hp u hu
  unfold WPFiniteNC122.a0 WPFiniteNC122.L WPFiniteNC122.h
    WPFiniteNC122.q WPFiniteJNormalization.r WPFiniteFifthSourceContraction.k at he
  unfold q2
  field_simp [h2,h5] at he ⊢
  linear_combination he

/-- The 121/125 logarithm uses products 11^2 and 5^3, without a 125<p restriction. -/
theorem actual_ell_121_125_zmod (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    WPFiniteField.ell p (121/125 : ZMod p) =
      3*(WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)-
      (8/125 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-
      (242/125 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 11 : ZMod p) := by
  have hn (n : ℕ) (hpos : 0<n) (hlt : n<p) : (n : ZMod p)≠0 :=
    WPFiniteInversion.denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hpos,hlt⟩)
  have h4 : (4 : ZMod p)≠0 := by simpa only [Nat.cast_ofNat] using hn 4 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := by simpa only [Nat.cast_ofNat] using hn 5 (by omega) (by omega)
  have h11 : (11 : ZMod p)≠0 := by simpa only [Nat.cast_ofNat] using hn 11 (by omega) (by omega)
  have h25 : (25 : ZMod p)≠0 := by
    rw [show (25 : ZMod p)=5^2 by ring]; exact pow_ne_zero _ h5
  have h125 : (125 : ZMod p)≠0 := by
    rw [show (125 : ZMod p)=5^3 by ring]; exact pow_ne_zero _ h5
  have h121 : (121 : ZMod p)≠0 := by
    rw [show (121 : ZMod p)=11^2 by ring]; exact pow_ne_zero _ h11
  have hq25 := integerFermatQuotient_product_cast p 5 5
    (by simpa only [Int.cast_ofNat] using h5) (by simpa only [Int.cast_ofNat] using h5)
  have hq125 := integerFermatQuotient_product_cast p 25 5
    (by simpa only [Int.cast_ofNat] using h25) (by simpa only [Int.cast_ofNat] using h5)
  have hq121 := integerFermatQuotient_product_cast p 11 11
    (by simpa only [Int.cast_ofNat] using h11) (by simpa only [Int.cast_ofNat] using h11)
  have he := finiteLog_fraction_fermat p (by omega) 121 125
    (by simpa only [Int.cast_ofNat] using h121) (by simpa only [Int.cast_ofNat] using h125)
    (by simpa only [show (125-121 : ℤ)=4 by norm_num,Int.cast_ofNat] using h4)
  norm_num only [show (5*5 : ℤ)=25 by norm_num] at hq25
  norm_num only [show (25*5 : ℤ)=125 by norm_num] at hq125
  norm_num only [show (11*11 : ℤ)=121 by norm_num] at hq121
  norm_num only [show (125-121 : ℤ)=4 by norm_num,Int.cast_ofNat] at he
  change ActualKwWeightedTrace.finiteLogValue p (121/125 : ZMod p)=_ 
  rw [he,hq125,hq25,hq121,WPFiniteInversion.integerFermatQuotient_four_cast p (by omega)]
  ring

/-- The genuine prime-field identity is transported to any field of characteristic p. -/
theorem actual_ell_121_125 (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    ell p (121/125 : K) =
      3*(WPFiniteInversion.integerFermatQuotient p 5 : K)-
      (8/125 : K)*q2 p-
      (242/125 : K)*(WPFiniteInversion.integerFermatQuotient p 11 : K) := by
  let f : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hm (z : ZMod p) : f (WPFiniteField.ell p z)=ell p (f z) := by
    simp only [ell,map_sum,map_div₀,map_pow,map_natCast]
  have he := congrArg f (actual_ell_121_125_zmod p hp)
  simp only [hm,map_div₀,map_ofNat,map_sub,map_mul,map_intCast] at he
  exact he

/-- The literal odd-origin value, with the complete original odd cutoff. -/
noncomputable def originalROOrigin (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K :=
  5/u^p*O p (WPFiniteNC122.T0 u)

/-- Both square roots give the same actual mixed-J odd-origin endpoint. -/
theorem actual_RO_origin (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p)
    (u : K) (hu : u^2=1/5) :
    originalROOrigin p u =
      25*WPFifthEntropy.C p u-36*q2 p+
        11*(WPFiniteInversion.integerFermatQuotient p 11 : K) := by
  have h2 : (2 : K)≠0 := denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h11 : (11 : K)≠0 := denominator_ne_zero p 11 (Finset.mem_Ico.mpr (by omega))
  have h25 : (25 : K)≠0 := by
    rw [show (25 : K)=5^2 by ring]; exact pow_ne_zero _ h5
  have h125 : (125 : K)≠0 := by
    rw [show (125 : K)=5^3 by ring]; exact pow_ne_zero _ h5
  have hu0 : u≠0 := by
    intro hz
    rw [hz,zero_pow (by omega : (2 : ℕ)≠0)] at hu
    exact (one_div_ne_zero h5) hu.symm
  have hup : u^p≠0 := pow_ne_zero _ hu0
  have hsquare : (WPFiniteNC122.T0 u)^2=(121/125 : K) := by
    unfold WPFiniteNC122.T0
    rw [div_pow,mul_pow,hu]
    field_simp [h5,h25,h125]
    ring
  have hprod : u*WPFiniteNC122.T0 u=(-11/25 : K) := by
    unfold WPFiniteNC122.T0
    calc
      _ = -11*u^2/5 := by ring
      _ = _ := by rw [hu]; field_simp [h5,h25]; ring
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h11p : (11 : K)^p=11 := by
    simpa only [Nat.cast_ofNat] using natCast_pow_char (K:=K) p 11
  have h25p : (25 : K)^p=25 := by
    simpa only [Nat.cast_ofNat] using natCast_pow_char (K:=K) p 25
  have hphase : u^p*(WPFiniteNC122.T0 u)^p=(-11/25 : K) := by
    rw [←mul_pow,hprod,div_pow,hodd.neg_pow,h11p,h25p]
  have hscale : 5/u^p=(-125/11 : K)*(WPFiniteNC122.T0 u)^p := by
    field_simp [hup,h11]
    field_simp [h25] at hphase
    linear_combination 5*hphase
  have he := WPFifthEntropy.ell_square_even_odd p hp (WPFiniteNC122.T0 u)
  have hEO : (WPFiniteNC122.T0 u)^p*O p (WPFiniteNC122.T0 u) =
      ell p ((WPFiniteNC122.T0 u)^2)/2-E p (WPFiniteNC122.T0 u) := by
    linear_combination he
  rw [originalROOrigin,hscale,mul_assoc,hEO,hsquare,actual_ell_121_125 p hp,
    actual_even_T0 p hp u hu]
  field_simp [h2,h5,h11,h25,h125]
  ring

end WPFieldAssembly.NativeClosureMixedJ

