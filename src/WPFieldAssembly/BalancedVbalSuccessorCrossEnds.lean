import WPFieldAssembly.BalancedVbalSuccessorCrossSupport
import WPFieldAssembly.BalancedVbalSuccessorCBParity
import WPFieldAssembly.SourceClosureVbalHasseSign

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualRankTwoProper WPActualGaussBottom
  WPFieldAssembly.BalancedVbalSuccessorCrossSupport
  WPFieldAssembly.BalancedVbalSuccessorCBParity
  WPFieldAssembly.SourceClosureVbalIR61FourEnds
  WPFieldAssembly.SourceClosureVbalHasseSign

namespace WPFieldAssembly.BalancedVbalSuccessorCrossEnds

set_option maxHeartbeats 1800000

variable (p : ℕ) [Fact p.Prime]

/- STATEMENT_FIDELITY: eval₂ evaluates the SAME full Laurent Dx from
   CrossSupport at the two original native units. Its actual N0 is the
   identical proper parity factor from CBParity. Only numerical powers
   of 2 and 4 are inverted; no branch factor or harmonic value is divided
   out. Both prime classes and all four lifted pole rows are retained. -/

noncomputable def actualCrossFourUnit (hp : 19≤p) : (ZMod p)ˣ :=
  Units.mk0 4 (WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega))

noncomputable def actualCrossQuarterUnit (hp : 19≤p) : (ZMod p)ˣ :=
  (actualCrossFourUnit p hp)⁻¹

theorem actual_cross_unit_values (hp : 19≤p) :
    (actualCrossQuarterUnit p hp : ZMod p)=1/4 ∧
      (actualCrossFourUnit p hp : ZMod p)=4 := by
  simp only [actualCrossQuarterUnit,actualCrossFourUnit,
    Units.val_inv_eq_inv_val,Units.val_mk0,one_div,and_self]

/-- The signed Laurent shift is the exact original e in both prime classes. -/
theorem actual_cross_Dx_exponent_parity (hp : 19≤p) :
    2*actualCrossE p=(p-1)/2+1+3*((p/6+1)%2) ∧
      2*(((p-1)/2-(p/6)%2)/2)+(p/6)%2=(p-1)/2 ∧
      actualCrossE p=(((p-1)/2-(p/6)%2)/2)+1+(p/6+1)%2 := by
  have hrem := actual_CB_parity_remainders p
  have hy := Nat.mod_lt (p/6) (by norm_num : 0<2)
  have hn := Nat.mod_lt (p/6+1) (by norm_num : 0<2)
  have hclass := WPActualNativeParameter.prime_six_classes p (by omega)
  dsimp only [actualCrossE]
  rcases hclass with h1 | h5 <;> omega

/-- These are the SAME N0 endpoints proved from the actual proper parity source. -/
theorem actual_cross_n0_native_ends (hp : 19≤p) :
    (actualCrossN0 p).eval (1/4)= -fieldHarmonic p (p/6) ∧
      (actualCrossN0 p).eval 4= -fieldHarmonic p (p/6) := by
  obtain ⟨_,_,ha,hb⟩ := actual_CB_parity_factor_ends p hp
  exact ⟨ha,hb⟩

/-- The actual eta normalization supplies both numerical factors, without an n0 unit. -/
theorem actual_cross_Dx_numeric_scales (hp : 19≤p) :
    actualCrossHasseSign p*(4 : ZMod p)^actualCrossE p*
        (-(1/8 : ZMod p))^((p/6+1)%2)= -2 ∧
      actualCrossHasseSign p*((4 : ZMod p)^actualCrossE p)⁻¹*
        (-8)^((p/6+1)%2)= -(1/2) := by
  let M := ((p-1)/2-(p/6)%2)/2
  have hexp := actual_cross_Dx_exponent_parity p hp
  have hM : 2*M+(p/6)%2=(p-1)/2 := hexp.2.1
  have hE : actualCrossE p=M+1+(p/6+1)%2 := hexp.2.2
  have hu := actual_cross_hasse_unit_scale p hp M hM
  have hrem := actual_CB_parity_remainders p
  have hy := Nat.mod_lt (p/6) (by norm_num : 0<2)
  have hr : (p/6)%2=0 ∨ (p/6)%2=1 := by omega
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h8 : (8 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 8 (by omega) (by omega)
  have ha : actualCrossHasseSign p*(4 : ZMod p)^actualCrossE p*
      (-(1/8 : ZMod p))^((p/6+1)%2)= -2 := by
    rcases hr with h0 | h1
    · have hn : (p/6+1)%2=1 := by omega
      have hunit : actualCrossHasseSign p*(4 : ZMod p)^M=1 := by
        simpa only [h0,pow_zero,mul_one] using hu
      have he : actualCrossE p=M+2 := by omega
      calc
        _ = actualCrossHasseSign p*((4 : ZMod p)^M*16)*(-(1/8 : ZMod p)) := by
          rw [he,hn,pow_one,pow_add]
          norm_num
        _ = (actualCrossHasseSign p*(4 : ZMod p)^M)*(-2) := by
          field_simp [h8]; ring
        _ = _ := by rw [hunit]; ring
    · have hn : (p/6+1)%2=0 := by omega
      have hunit : actualCrossHasseSign p*(4 : ZMod p)^M*(-2)=1 := by
        simpa only [h1,pow_one] using hu
      have he : actualCrossE p=M+1 := by omega
      calc
        _ = actualCrossHasseSign p*((4 : ZMod p)^M*4) := by
          simp only [he,hn,pow_zero,pow_add,pow_one,mul_one]
        _ = _ := by linear_combination (-2)*hunit
  have hnumerical : (-(1/8 : ZMod p))*(-8)=1 := by
    field_simp [h8]
  have hpowers : (-(1/8 : ZMod p))^((p/6+1)%2)*(-8)^((p/6+1)%2)=1 := by
    rw [←mul_pow,hnumerical,one_pow]
  have hprod :
      (actualCrossHasseSign p*(4 : ZMod p)^actualCrossE p*
        (-(1/8 : ZMod p))^((p/6+1)%2))*
      (actualCrossHasseSign p*((4 : ZMod p)^actualCrossE p)⁻¹*
        (-8)^((p/6+1)%2))=1 := by
    calc
      _ = actualCrossHasseSign p^2*
          ((4 : ZMod p)^actualCrossE p*((4 : ZMod p)^actualCrossE p)⁻¹)*
          ((-(1/8 : ZMod p))^((p/6+1)%2)*(-8)^((p/6+1)%2)) := by ring
      _ = _ := by
        rw [actual_cross_hasse_sign_square p hp,
          mul_inv_cancel₀ (pow_ne_zero (actualCrossE p) h4),hpowers]; ring
  rw [ha] at hprod
  refine ⟨ha,?_⟩
  apply mul_left_cancel₀ h2
  calc
    _ = -1 := by linear_combination -hprod
    _ = (2 : ZMod p)*(-(1/2 : ZMod p)) := by field_simp [h2]

private theorem inversion_eval {K : Type*} [Field K]
    (u : Kˣ) (L : K[T;T⁻¹]) :
    LaurentPolynomial.eval₂ (RingHom.id K) u (invert L)=
      LaurentPolynomial.eval₂ (RingHom.id K) u⁻¹ L := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM => simp only [map_add,hL,hM]
  | C_mul_T n a =>
    simp only [map_mul,invert_C,invert_T,LaurentPolynomial.eval₂_C,
      LaurentPolynomial.eval₂_T,RingHom.id_apply,zpow_neg,inv_zpow]

private theorem actual_cross_Dx_eval (u : (ZMod p)ˣ) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) u (actualCrossDx p)=
      6*actualCrossHasseSign p*((u : ZMod p)^actualCrossE p)⁻¹*(4-11*(u : ZMod p))*
        (((1/5 : ZMod p)*((u : ZMod p)+1))*
          ((1/25 : ZMod p)*((4*(u : ZMod p)-11)*(4-11*(u : ZMod p)))))^((p/6+1)%2)*
        (actualCrossN0 p).eval (u : ZMod p)*(actualCrossN0 p).eval ((u : ZMod p)⁻¹) := by
  simp only [actualCrossDx,map_mul,LaurentPolynomial.eval₂_C,RingHom.id_apply,
    LaurentPolynomial.eval₂_T,inversion_eval,LaurentPolynomial.eval₂_toLaurent,
    Polynomial.eval₂_id,Units.val_inv_eq_inv_val,zpow_neg,zpow_natCast,
    Units.val_pow_eq_pow_val,actualCrossPositiveNumerator,
    eval_mul,eval_sub,eval_add,eval_C,eval_ofNat,eval_X,eval_one,eval_pow,mul_pow]
  ring

/-- The original full Dx has its actual native endpoints, including possible h=0. -/
theorem actual_cross_Dx_native_ends (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (actualCrossQuarterUnit p hp)
        (actualCrossDx p)= -15*fieldHarmonic p (p/6)^2 ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (actualCrossFourUnit p hp)
        (actualCrossDx p)=120*fieldHarmonic p (p/6)^2 := by
  obtain ⟨hqa,hqb⟩ := actual_cross_unit_values p hp
  obtain ⟨hna,hnb⟩ := actual_cross_n0_native_ends p hp
  obtain ⟨hsa,hsb⟩ := actual_cross_Dx_numeric_scales p hp
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h8 : (8 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 8 (by omega) (by omega)
  have h25 : (25 : ZMod p)≠0 := by
    rw [show (25 : ZMod p)=5^2 by ring]
    exact pow_ne_zero _ h5
  have hqinv : (1/4 : ZMod p)⁻¹=4 := by rw [one_div,inv_inv]
  have hfinv : (4 : ZMod p)⁻¹=1/4 := (one_div (4 : ZMod p)).symm
  have hqpower : ((1/4 : ZMod p)^actualCrossE p)⁻¹=(4 : ZMod p)^actualCrossE p := by
    rw [←inv_pow,hqinv]
  have hca : (4-11*(1/4 : ZMod p))=5/4 := by
    field_simp [h4]; ring
  have hcba : ((1/5 : ZMod p)*((1/4 : ZMod p)+1))*
      ((1/25 : ZMod p)*((4*(1/4 : ZMod p)-11)*(4-11*(1/4 : ZMod p))))=
      -(1/8 : ZMod p) := by
    field_simp [h4,h5,h8,h25]; ring
  have hcb : (4-11*(4 : ZMod p))= -40 := by ring
  have hcbb : ((1/5 : ZMod p)*((4 : ZMod p)+1))*
      ((1/25 : ZMod p)*((4*(4 : ZMod p)-11)*(4-11*(4 : ZMod p))))= -8 := by
    field_simp [h5,h25]; ring
  constructor
  · rw [actual_cross_Dx_eval,hqa,hqpower,hqinv,hcba,hca,hna,hnb]
    calc
      _ = (15/2 : ZMod p)*
          (actualCrossHasseSign p*(4 : ZMod p)^actualCrossE p*
            (-(1/8 : ZMod p))^((p/6+1)%2))*fieldHarmonic p (p/6)^2 := by
        field_simp [h2,h4]; ring
      _ = _ := by rw [hsa]; field_simp [h2]
  · rw [actual_cross_Dx_eval,hqb,hfinv,hcbb,hcb,hnb,hna]
    calc
      _ = -240*(actualCrossHasseSign p*((4 : ZMod p)^actualCrossE p)⁻¹*
          (-8)^((p/6+1)%2))*fieldHarmonic p (p/6)^2 := by ring
      _ = _ := by rw [hsb]; field_simp [h2]; ring

/-- Squaring identifies the two native ends with all four original conic numerators. -/
theorem actual_cross_Dx_conic_four_ends (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (actualCrossQuarterUnit p hp)
        (actualCrossDx p)=actualCrossConicValue p (1/2) (1/2) ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (actualCrossQuarterUnit p hp)
        (actualCrossDx p)=actualCrossConicValue p (-1/2) (1/2) ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (actualCrossFourUnit p hp)
        (actualCrossDx p)=actualCrossConicValue p 2 1 ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (actualCrossFourUnit p hp)
        (actualCrossDx p)=actualCrossConicValue p (-2) 1 := by
  obtain ⟨ha,hb⟩ := actual_cross_Dx_native_ends p hp
  obtain ⟨hpa,hpan,hpb,hpbn⟩ := actual_cross_conic_four_end_values p hp
  exact ⟨ha.trans hpa.symm,ha.trans hpan.symm,hb.trans hpb.symm,hb.trans hpbn.symm⟩

/-- The same Dx retains the four signed simple-pole rows before the tame factor two. -/
theorem actual_cross_Dx_four_tame_rows (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (actualCrossQuarterUnit p hp)
        (actualCrossDx p)/(actualCrossPolePolynomial p).derivative.eval (1/2)=
        -fieldHarmonic p (p/6)^2 ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (actualCrossQuarterUnit p hp)
        (actualCrossDx p)/(actualCrossPolePolynomial p).derivative.eval (-1/2)=
        fieldHarmonic p (p/6)^2 ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (actualCrossFourUnit p hp)
        (actualCrossDx p)/(actualCrossPolePolynomial p).derivative.eval 2=
        -2*fieldHarmonic p (p/6)^2 ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (actualCrossFourUnit p hp)
        (actualCrossDx p)/(actualCrossPolePolynomial p).derivative.eval (-2)=
        2*fieldHarmonic p (p/6)^2 := by
  obtain ⟨ha,han,hb,hbn⟩ := actual_cross_Dx_conic_four_ends p hp
  obtain ⟨hra,hran,hrb,hrbn⟩ := actual_cross_conic_four_end_residue_rows p hp
  refine ⟨?_,?_,?_,?_⟩
  · rw [ha]; exact hra
  · rw [han]; exact hran
  · rw [hb]; exact hrb
  · rw [hbn]; exact hrbn

end WPFieldAssembly.BalancedVbalSuccessorCrossEnds
