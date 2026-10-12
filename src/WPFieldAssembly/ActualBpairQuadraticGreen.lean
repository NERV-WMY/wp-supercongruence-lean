import WPFieldAssembly.ActualBpairMetricAttachment
import WPFieldAssembly.ActualBpairHAttachment
import WPFieldAssembly.ActualKwRationalRowAttachment
import WPFieldAssembly.ScalarFinalSuccessorG2Dlog

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPFieldAssembly.GreenLaurentOperators WPFieldAssembly.ActualSimplePoleResidue
open WPFieldAssembly.ActualCubicNativeSource WPFieldAssembly.ActualBpairNativeTail
open WPFieldAssembly.ActualKwOrderedEndpoints WPFieldAssembly.ActualKwRationalRowAttachment

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 2400000

private theorem green_smooth_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (a b c : ℕ) : ((2 : K)^a * 3^b * 5^c) ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero a h2) (pow_ne_zero b h3))
    (pow_ne_zero c h5)

private theorem divide_two (a b : K) (h2 : (2 : K)≠0) (h : 2*a=b) : a=b/2 := by
  apply (eq_div_iff h2).mpr
  linear_combination h

/-- The whole nonpositive logarithm triangle is contracted using all four native rational rows. -/
theorem branchH_rational_triangle_NC126 (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    (2/15 : K)*((1/4 : K)*(2*branchH p (1/4) 4+branchH p 4 4)-
      4*(2*branchH p (1/4) (1/4)+branchH p 4 (1/4)))=
      -WPFiniteField.R p (-2)/2-11*(WPFiniteNC122.q p)^2/5+
        9*WPFiniteNC122.q p*(WPFiniteInversion.integerFermatQuotient p 3 : K)/5-
          27*(WPFiniteInversion.integerFermatQuotient p 3 : K)^2/40+
            originalG p (1/5)/4 := by
  have hn (n : ℕ) (hpos : 0<n) (hlt : n<p) : (n : K)≠0 :=
    WPFiniteField.denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hpos,hlt⟩)
  have h2 : (2 : K) ≠ 0 := hn 2 (by omega) (by omega)
  have h3 : (3 : K) ≠ 0 := hn 3 (by omega) (by omega)
  have h4 : (4 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 2 0 0 using 1; norm_num
  have h5 : (5 : K) ≠ 0 := hn 5 (by omega) (by omega)
  have h6 : (6 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 1 1 0 using 1; norm_num
  have h12 : (12 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 2 1 0 using 1; norm_num
  have h15 : (15 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 0 1 1 using 1; norm_num
  have h40 : (40 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 3 0 1 using 1; norm_num
  have haa := divide_two _ _ h2 (movingH_aa p u hu h4 h5)
  have hbb := divide_two _ _ h2 (movingH_bb p u hu h2 h5)
  have hba := divide_two _ _ h2 (movingH_ba p u hu h4 h5)
  have hab := divide_two _ _ h2 (movingH_ab p u hu h4 h5)
  have hG : originalG p (1/5 : K)=WPFiniteLoop.B p u+2*WPFiniteLoop.A p u := by
    rw [←hu]
    exact originalG_square p u
  simp only [branchH_movingH p hp,haa,hbb,hba,hab,native_S_one_one p hp,
    native_S_half_half p hp,native_S_two_two p hp,native_S_two_one p hp,
    native_S_one_half p hp,native_S_one_two p hp,native_S_half_one p hp,hG]
  unfold ActualRationalSignRows.q2 ActualRationalSignRows.q3 WPFiniteNC122.q
  field_simp [h2,h3,h4,h5,h6,h12,h15,h40]
  ring

theorem actual_AK_Dstar_inverse_zero_closed (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    fullStrictTail p 0 ((actualAK p : K[X]).toLaurent*invert (Dstar p).toLaurent)=
      WPFiniteField.R p (-2)/2-originalG p (1/5)/4+
        77*(WPFiniteNC122.q p)^2/50+
          54*WPFiniteNC122.q p*(WPFiniteInversion.integerFermatQuotient p 3 : K)/25-
            63*(WPFiniteInversion.integerFermatQuotient p 3 : K)^2/200-
              3*WPFiniteNC122.q p*(WPFiniteInversion.integerFermatQuotient p 5 : K)/2-
                11*(WPFifthEntropy.C p u)^2/10 := by
  rw [actual_AK_Dstar_inverse_zero_NC126d p hp u hu,
    branchH_rational_triangle_NC126 p hp u hu]
  obtain ⟨ha,hb⟩ := Dstar_endpoints (K:=K) p hp
  rw [ha,hb]
  unfold WPFiniteNC122.h
  have hn (n : ℕ) (hpos : 0<n) (hlt : n<p) : (n : K)≠0 :=
    WPFiniteField.denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hpos,hlt⟩)
  have h2 : (2 : K) ≠ 0 := hn 2 (by omega) (by omega)
  have h3 : (3 : K) ≠ 0 := hn 3 (by omega) (by omega)
  have h5 : (5 : K) ≠ 0 := hn 5 (by omega) (by omega)
  have h4 : (4 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 2 0 0 using 1; norm_num
  have h6 : (6 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 1 1 0 using 1; norm_num
  have h10 : (10 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 1 0 1 using 1; norm_num
  have h25 : (25 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 0 0 2 using 1; norm_num
  have h40 : (40 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 3 0 1 using 1; norm_num
  have h50 : (50 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 1 0 2 using 1; norm_num
  have h200 : (200 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 3 0 2 using 1; norm_num
  field_simp [h2,h3,h4,h5,h6,h10,h25,h40,h50,h200]
  ring

theorem actual_AK_Dstar_one_retained (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    fullStrictTail p 1 ((actualAK p : K[X])*Dstar p).toLaurent=
      8*(WPFiniteNC122.q p)^2/5-
        3*WPFiniteNC122.q p*(WPFiniteInversion.integerFermatQuotient p 3 : K)+
          27*(WPFiniteInversion.integerFermatQuotient p 3 : K)^2/20-
            4*WPFifthEntropy.C p u*(WPFifthEntropy.C p u+WPFiniteNC122.q p)/5+
              fullStrictTail p 1 ((finiteMixedLog p)*Dstar p).toLaurent := by
  rw [actual_AK_Dstar_strict_one_weight p hp,nativeB_origin_fifth p hp u hu,
    Dstar_origin_fifth p hp u hu]
  obtain ⟨hba,hbb⟩ := nativeB_endpoints (K:=K) p hp
  obtain ⟨ha,hb⟩ := Dstar_endpoints (K:=K) p hp
  rw [hba,hbb,ha,hb]
  unfold nativeTau WPFiniteNC122.h
  have hn (n : ℕ) (hpos : 0<n) (hlt : n<p) : (n : K)≠0 :=
    WPFiniteField.denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hpos,hlt⟩)
  have h2 : (2 : K) ≠ 0 := hn 2 (by omega) (by omega)
  have h3 : (3 : K) ≠ 0 := hn 3 (by omega) (by omega)
  have h5 : (5 : K) ≠ 0 := hn 5 (by omega) (by omega)
  have h4 : (4 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 2 0 0 using 1; norm_num
  have h6 : (6 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 1 1 0 using 1; norm_num
  have h20 : (20 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 2 0 1 using 1; norm_num
  field_simp [h2,h3,h4,h5,h6,h20]
  ring

/-- This full-tail scalar is the original five-term NC124 expression with its entire metric. -/
noncomputable def actualNativeG2Tail (p : ℕ) [Fact p.Prime] [CharP K p] : K :=
  -(5/3 : K)*fullStrictTail p 0
      ((actualAK p : K[X]).toLaurent*invert (Dstar p).toLaurent)-
    fullStrictTail p 0 ((actualAK p : K[X])*Dstar p).toLaurent+
      (11/4 : K)*(fullStrictTail p 1
        ((actualAK p : K[X]).toLaurent*invert (Dstar p).toLaurent)+
          fullStrictTail p 1 ((actualAK p : K[X])*Dstar p).toLaurent)+
        (5/24 : K)*fullStrictTail p 1 ((actualAK p : K[X])^2).toLaurent+
          actualNativeMetric p

/-- The literal original quadratic residue before the complete strict-tail transport. -/
noncomputable def actualNativeG2Residue (p : ℕ) [Fact p.Prime] [CharP K p] : K :=
  let v := invert (actualAK p : K[X]).toLaurent
  let d := (Dstar p : K[X]).toLaurent
  originPole ((LaurentPolynomial.C (33 : K)-LaurentPolynomial.C (12 : K)*T 1)*
    ((LaurentPolynomial.C (5/3 : K)-LaurentPolynomial.C (11/4 : K)*T (p : ℤ))*v*d+
      (1-LaurentPolynomial.C (11/4 : K)*T (p : ℤ))*v*invert d-
        LaurentPolynomial.C (5/24 : K)*T (p : ℤ)*v^2))+actualNativeMetric p

/-- All five original residues become their full strict tails, without a top-degree cutoff. -/
theorem actualNativeG2Residue_full_tails (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) : actualNativeG2Residue (K:=K) p=actualNativeG2Tail p := by
  let U := (actualAK p : K[X]).toLaurent
  let d := (Dstar p : K[X]).toLaurent
  let v := invert U
  let den := LaurentPolynomial.C (33 : K)-LaurentPolynomial.C (12 : K)*T 1
  have h0dv := original_dlogV_inverse_phase p 0 hp (U*invert d)
  have h1dv := original_dlogV_inverse_phase p 1 hp (U*invert d)
  have h0d := original_dlogV_inverse_phase p 0 hp (U*d)
  have h1d := original_dlogV_inverse_phase p 1 hp (U*d)
  have h1s := original_dlogV_inverse_phase p 1 hp (U^2)
  simp only [Nat.zero_mul,Nat.cast_zero,T_zero,one_mul,map_mul,
    involutive_invert d] at h0dv h1dv h0d h1d
  simp only [Nat.one_mul,map_pow] at h1s
  change originPole (den*(v*d))=-fullStrictTail p 0 (U*invert d) at h0dv
  have h1dv : originPole (den*(T (p : ℤ)*v*d))=-fullStrictTail p 1 (U*invert d) := by
    simpa only [den,v,mul_assoc] using h1dv
  change originPole (den*(v*invert d))=-fullStrictTail p 0 (U*d) at h0d
  have h1d : originPole (den*(T (p : ℤ)*v*invert d))=-fullStrictTail p 1 (U*d) := by
    simpa only [den,v,mul_assoc] using h1d
  change originPole (den*(T (p : ℤ)*v^2))=-fullStrictTail p 1 (U^2) at h1s
  have he : den*((LaurentPolynomial.C (5/3 : K)-LaurentPolynomial.C (11/4 : K)*T (p : ℤ))*v*d+
      (1-LaurentPolynomial.C (11/4 : K)*T (p : ℤ))*v*invert d-
        LaurentPolynomial.C (5/24 : K)*T (p : ℤ)*v^2)=
      LaurentPolynomial.C (5/3 : K)*(den*(v*d))-
        LaurentPolynomial.C (11/4 : K)*(den*(T (p : ℤ)*v*d))+
          den*(v*invert d)-LaurentPolynomial.C (11/4 : K)*(den*(T (p : ℤ)*v*invert d))-
            LaurentPolynomial.C (5/24 : K)*(den*(T (p : ℤ)*v^2)) := by ring
  change originPole (den*((LaurentPolynomial.C (5/3 : K)-LaurentPolynomial.C (11/4 : K)*T (p : ℤ))*v*d+
      (1-LaurentPolynomial.C (11/4 : K)*T (p : ℤ))*v*invert d-
        LaurentPolynomial.C (5/24 : K)*T (p : ℤ)*v^2))+actualNativeMetric p=_
  rw [he]
  simp only [originPole_add,originPole_sub,originPole_C_mul,h0dv,h1dv,h0d,h1d,h1s,
    actualNativeG2Tail,map_mul,map_pow]
  dsimp only [U,d]
  ring

/-- The mixed high tail cancels algebraically only after all five full native tails are present. -/
theorem actualNativeG2Tail_NC126 (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    actualNativeG2Tail (K:=K) p=
      5*originalG p (1/5)/12-5*WPFiniteField.R p (-2)/6-WPFiniteField.R p 16/20-
        193*(WPFiniteNC122.q p)^2/50-
          9*WPFiniteNC122.q p*(WPFiniteInversion.integerFermatQuotient p 3 : K)/100-
            177*(WPFiniteInversion.integerFermatQuotient p 3 : K)^2/800+
              4*WPFiniteNC122.q p*(WPFiniteInversion.integerFermatQuotient p 5 : K)+
                11*(WPFifthEntropy.C p u)^2/15-
                  10*WPFiniteNC122.q p*WPFifthEntropy.C p u/3-
                    5*(WPFiniteInversion.integerFermatQuotient p 3 : K)*WPFifthEntropy.C p u/2 := by
  rw [actualNativeG2Tail,actual_AK_Dstar_inverse_zero_closed p hp u hu,
    actual_AK_Dstar_NC126d p hp u hu,actual_AK_Dstar_inverse_NC126d p hp u hu,
    actual_AK_Dstar_one_retained p hp u hu,actual_AK_square_NC126 p hp u hu,
    actualNativeMetric_NC126 p hp u hu]
  unfold nativeTau WPFiniteNC122.h
  have hn (n : ℕ) (hpos : 0<n) (hlt : n<p) : (n : K)≠0 :=
    WPFiniteField.denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hpos,hlt⟩)
  have h2 : (2 : K) ≠ 0 := hn 2 (by omega) (by omega)
  have h3 : (3 : K) ≠ 0 := hn 3 (by omega) (by omega)
  have h5 : (5 : K) ≠ 0 := hn 5 (by omega) (by omega)
  have h4 : (4 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 2 0 0 using 1; norm_num
  have h6 : (6 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 1 1 0 using 1; norm_num
  have h12 : (12 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 2 1 0 using 1; norm_num
  have h15 : (15 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 0 1 1 using 1; norm_num
  have h20 : (20 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 2 0 1 using 1; norm_num
  have h25 : (25 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 0 0 2 using 1; norm_num
  have h50 : (50 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 1 0 2 using 1; norm_num
  have h100 : (100 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 2 0 2 using 1; norm_num
  have h200 : (200 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 3 0 2 using 1; norm_num
  have h800 : (800 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 5 0 2 using 1; norm_num
  have h24 : (24 : K)≠0 := by
    rw [show (24 : K)=2^3*3 by ring]
    exact mul_ne_zero (pow_ne_zero 3 h2) h3
  have h10 : (10 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 1 0 1 using 1; norm_num
  have h75 : (75 : K) ≠ 0 := by
    convert green_smooth_ne_zero (K:=K) p hp 0 1 2 using 1; norm_num
  have ha0 : WPFiniteNC122.a0 p u=
      11*WPFifthEntropy.C p u/5-WPFiniteNC122.q p/5+
        3*((WPFiniteInversion.integerFermatQuotient p 3 : K)+
          (WPFiniteInversion.integerFermatQuotient p 5 : K))/2 := by
    have he := actual_AK_origin_retained (K:=K) p hp
    rw [coeff_zero_eq_eval_zero,actual_AK_origin p hp u hu] at he
    rw [Dstar_origin_fifth p hp u hu] at he
    unfold nativeConstant WPFiniteNC122.h at he
    linear_combination (norm := (field_simp [h2,h3,h5]; ring)) he
  rw [ha0]
  field_simp [h2,h3,h4,h5,h6,h10,h12,h15,h20,h24,h25,h50,h75,h100,h200,h800]
  ring

end WPFieldAssembly.ActualBpairContraction
