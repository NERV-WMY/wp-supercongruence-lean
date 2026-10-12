import WPFieldAssembly.SourceClosureVbalArithmetic
import WPFieldAssembly.SourceClosureVbalDigits

namespace WPFieldAssembly.ActualVbalFieldClosure

open WPPIntegralReduction ActualEntropyFifth
  ActualKwWeightedTrace ActualKwFiniteHBridge ActualKwOrderedEndpoints
  ActualKwRationalRowAttachment WPFiniteField

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/- These are the original field terms of V_bal/p. The rational source
identification is supplied separately by ActualVbalCarry. The fifth C is
E(2u)-E(u), while the conic digit retains E(2w)-E(w). All finite D_N
diagonals and both G carriers survive until the original T5 consumer. -/

noncomputable def vbalProduct (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K :=
  let q : K := WPFiniteInversion.integerFermatQuotient p 2
  let r : K := WPFiniteInversion.integerFermatQuotient p 3
  let k : K := WPFiniteInversion.integerFermatQuotient p 5
  let C := WPFifthEntropy.C p u
  (456/25 : K)*q^2-(21/2 : K)*q*r-(9/40 : K)*r^2-
    18*q*k+(9/4 : K)*r*k+(45/8 : K)*k^2-
    (1309/25 : K)*q*C-(33/5 : K)*r*C+(66/5 : K)*k*C+(111/50 : K)*C^2

noncomputable def conicPacket (p : ℕ) [Fact p.Prime] [CharP K p] (u w : K) : K :=
  let q : K := WPFiniteInversion.integerFermatQuotient p 2
  let r : K := WPFiniteInversion.integerFermatQuotient p 3
  let j : K := WPFiniteInversion.integerFermatQuotient p 11
  let C := WPFifthEntropy.C p u
  let h := -2*q-3*r/2
  originalG p (3/11)+4*h*(E p (2*w)-E p w)+6*(q-C)*j

noncomputable def vbalAlphabet (p : ℕ) [Fact p.Prime] [CharP K p] (u w : K) : K :=
  vbalProduct p u+(23/10 : K)*R p (-2 : K)+
    (33/5 : K)*(WPFiniteNC122.Aeven p (2*u)-WPFiniteNC122.Aeven p u)+
    (2/5 : K)*originalG p (1/5)-3*originalT5 p u/2-
    3*WPFiniteNC122.Aeven p (-(11/5 : K)*u)-(11/10 : K)*conicPacket p u w

noncomputable def vbalMomentConsumer (p : ℕ) [Fact p.Prime] [CharP K p]
    (u w : K) : K :=
  (2/3 : K)*vbalProduct p u+(23/15 : K)*R p (-2 : K)+
    (22/5 : K)*(WPFiniteNC122.Aeven p (2*u)-WPFiniteNC122.Aeven p u)+
    (4/15 : K)*originalG p (1/5)-2*WPFiniteNC122.Aeven p (-(11/5 : K)*u)-
    (11/15 : K)*conicPacket p u w

/-- The retained ordinary product is the exact closed entropy substitution. -/
theorem vbalProduct_closed_product (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    vbalProduct p u=SourceClosureVbalArithmetic.closedProduct
      (WPFiniteInversion.integerFermatQuotient p 2 : K)
      (WPFiniteInversion.integerFermatQuotient p 3 : K)
      (WPFiniteInversion.integerFermatQuotient p 5 : K) (WPFifthEntropy.C p u) := rfl

/-- This is the original C first digit, after its actual integral reduction. -/
theorem actual_conic_first_digit (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u w : K) (hu : u^2=(1/5 : K)) (hw : w^2=(3/11 : K)) :
    (ZMod.castHom (dvd_refl p) K) (ActualLogCCarry.logCFirstDigit p)=
      (3/5 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)+
      (11/5 : K)*(E p (2*w)-E p w-WPFifthEntropy.C p u) := by
  rw [←ActualLogCCarry.logCDigitIntegral_field p hp]
  exact ActualVbalCarry.logCDigitIntegral_field_fifth p hp u w hu hw

/-- The fifth first entropy letter is eliminated with both Frobenius classes retained. -/
theorem fifth_first_entropy (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=(1/5 : K)) :
    E p u=WPFifthEntropy.C p u/5-
      6*(WPFiniteInversion.integerFermatQuotient p 2 : K)/5+
      (WPFiniteInversion.integerFermatQuotient p 5 : K)/2 := by
  rw [WPFifthEntropy.E_at_fifth p hp u hu]
  ring

/-- The closed product is evaluated at the actual fifth entropy, for either branch. -/
theorem vbalProduct_actual_entropy (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=(1/5 : K)) :
    SourceClosureVbalArithmetic.entropyProduct
      (WPFiniteInversion.integerFermatQuotient p 2 : K)
      (WPFiniteInversion.integerFermatQuotient p 3 : K)
      (WPFiniteInversion.integerFermatQuotient p 5 : K) (WPFifthEntropy.C p u)
      (E p u)=vbalProduct p u := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  rw [fifth_first_entropy p hp u hu,vbalProduct_closed_product]
  exact SourceClosureVbalArithmetic.entropy_product_identity h2 h5 _ _ _ _

/-- The entire Q11 coefficient comes from the original Aend and Dend. -/
theorem original_Q11_collection (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    -(9/4 : K)*(WPFiniteInversion.integerFermatQuotient p 3 : K)-
      3*WPFifthEntropy.C p u+
      3*((WPFiniteInversion.integerFermatQuotient p 2 : K)+
        (3/4 : K)*(WPFiniteInversion.integerFermatQuotient p 3 : K))=
      3*((WPFiniteInversion.integerFermatQuotient p 2 : K)-WPFifthEntropy.C p u) := by
  ring

/-- Both original G endpoints retain the complete signed H2 traces. -/
theorem actual_G_full_sign_ends (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u w : K) (hu : u^2=(1/5 : K)) (hw : w^2=(3/11 : K)) :
    originalG p (1/5)=
      WPFiniteSignTrace.fullTraceS p (2*u) 2-WPFiniteSignTrace.fullTraceS p u 1+
        2*WPFiniteSignTrace.fullTraceS p (2*u) 1-
          2*WPFiniteSignTrace.fullTraceS p u (1/2) ∧
    originalG p (3/11)=
      WPFiniteSignTrace.fullTraceS p (2*w) 2-WPFiniteSignTrace.fullTraceS p w 1+
        2*WPFiniteSignTrace.fullTraceS p (2*w) 1-
          2*WPFiniteSignTrace.fullTraceS p w (1/2) := by
  refine ⟨?_,originalG_c_full_trace p hp w hw⟩
  rw [←hu]
  exact originalG_full_trace p hp u

/-- Exact evaluation of the original field terms, with the actual phase and
conic integral digits and the entire finite triangular comparison trace. -/
theorem original_field_terms_closed (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u w : K) (hu : u^2=(1/5 : K)) (hw : w^2=(3/11 : K)) :
    (69/10 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)^2-
      (63/10 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)*
        (WPFiniteInversion.integerFermatQuotient p 3 : K)+
      (9/8 : K)*(WPFiniteInversion.integerFermatQuotient p 3 : K)^2-
      (11/10 : K)*WPFiniteField.R p (-2 : K)-3*actualFifthCarryField p u-
      (ZMod.castHom (dvd_refl p) K) (residueHom p
        (ActualWeightedF0Carry.phaseCarryI p hp))-movingTw p+
      (4*(WPFiniteInversion.integerFermatQuotient p 2 : K)+
        3*(WPFiniteInversion.integerFermatQuotient p 3 : K))*
          (ZMod.castHom (dvd_refl p) K) (ActualLogCCarry.logCFirstDigit p)=
      vbalAlphabet p u w := by
  have hn (n : ℕ) (hpos : 0<n) (hlt : n<p) : (n : K)≠0 :=
    WPFiniteField.denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hpos,hlt⟩)
  have h2 : (2 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 2 (by omega) (by omega)
  have h3 : (3 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 3 (by omega) (by omega)
  have h4 : (4 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 4 (by omega) (by omega)
  have h5 : (5 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 5 (by omega) (by omega)
  have h8 : (8 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 8 (by omega) (by omega)
  have h10 : (10 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 10 (by omega) (by omega)
  have h15 : (15 : K)≠0 := by convert mul_ne_zero h3 h5 using 1; norm_num
  have h25 : (25 : K)≠0 := by convert mul_ne_zero h5 h5 using 1; norm_num
  have h40 : (40 : K)≠0 := by convert mul_ne_zero h8 h5 using 1; norm_num
  have h50 : (50 : K)≠0 := by convert mul_ne_zero h10 h5 using 1; norm_num
  have ht := movingTw_actual_rational_rows (K:=K) p hp u hu
  rw [movingDend_fermat p hp,(finiteLog_c_ordered (K:=K) p hp).2] at ht
  have ht' := congrArg (fun z : K => -z) ht
  simp only [neg_neg] at ht'
  rw [actual_conic_first_digit p hp u w hu hw,
    ActualVbalCarry.phaseCarryI_field_fifth p hp u hu,ht']
  rw [SourceClosureVbalArithmetic.actual_fifth_carry_product p hp u hu]
  unfold vbalAlphabet vbalProduct conicPacket SourceClosureVbalArithmetic.fifthProduct
  dsimp only
  unfold ActualRationalSignRows.q2 ActualRationalSignRows.q3
  field_simp [h2,h3,h4,h5,h8,h10,h15,h25,h40,h50]
  ring

/-- The whole original T5 cancels in this same weighted consumer. -/
theorem vbalAlphabet_T5_consumer (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u w : K) :
    (2/3 : K)*vbalAlphabet p u w+originalT5 p u=vbalMomentConsumer p u w := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K)≠0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := by convert mul_ne_zero h3 h5 using 1; norm_num
  unfold vbalAlphabet vbalMomentConsumer
  field_simp [h2,h3,h5,h10,h15]
  ring

/-- The remaining endpoint packets cancel under their original consumer weights. -/
theorem vbalAlphabet_fifth_consumer (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u w : K) :
    (2/3 : K)*vbalAlphabet p u w+originalT5 p u+
      2*WPFiniteNC122.Aeven p (-(11/5 : K)*u)+(11/15 : K)*conicPacket p u w=
      (2/3 : K)*vbalProduct p u+(23/15 : K)*R p (-2 : K)+
      (22/5 : K)*(WPFiniteNC122.Aeven p (2*u)-WPFiniteNC122.Aeven p u)+
      (4/15 : K)*originalG p (1/5) := by
  rw [vbalAlphabet_T5_consumer p hp u w]
  unfold vbalMomentConsumer
  ring

end WPFieldAssembly.ActualVbalFieldClosure
