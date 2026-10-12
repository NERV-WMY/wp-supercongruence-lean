import WPFieldAssembly.ActualBpairKernel
import WPFiniteProductTail

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteProductTail
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1400000

/-- The literal full logarithm in the original x coordinate. -/
noncomputable def kernelLog (p : ℕ) (c : K) : K[T;T⁻¹] :=
  ((WPFiniteAffineLog.LP p : K[X]).comp (Polynomial.C c*X)).toLaurent

/-- This coefficient retains both the lower and upper finite cutoff. -/
noncomputable def kernelLogCoeff (p : ℕ) (c : K) (j : ℤ) : K :=
  if 1≤j ∧ j<(p : ℤ) then c^j.toNat/(j.toNat : K) else 0

theorem kernelLog_coeff (p : ℕ) (c : K) (j : ℤ) :
    (kernelLog p c).coeff j=kernelLogCoeff p c j := by
  unfold kernelLog kernelLogCoeff
  by_cases hj : 0≤j
  · have he : (j.toNat : ℤ)=j := Int.toNat_of_nonneg hj
    rw [←he,WPFiniteJCarrier.toLaurent_coeff_nat,LP_scaled_coeff]
    congr 1
    exact propext (by omega)
  · rw [WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega)),
      if_neg (by omega : ¬(1≤j ∧ j<(p : ℤ)))]

/-- The whole original IR71 K_B, including its second negative Frobenius band. -/
noncomputable def literalKB (p : ℕ) : K[T;T⁻¹] :=
  LaurentPolynomial.C (1/6 : K)*
    (LaurentPolynomial.C (35 : K)*kernelLog p (1/4)+
      LaurentPolynomial.C (23*4 : K)*T (-(p : ℤ))*kernelLog p (1/4)+
      LaurentPolynomial.C (23*4^2 : K)*T (-2*(p : ℤ))*kernelLog p (1/4)-
      LaurentPolynomial.C (5 : K)*kernelLog p 4-
      LaurentPolynomial.C (29*(1/4) : K)*T (-(p : ℤ))*kernelLog p 4-
      LaurentPolynomial.C (29*(1/4)^2 : K)*T (-2*(p : ℤ))*kernelLog p 4)

/-- Every coefficient of the whole source is reduced to its three original log bands. -/
theorem literalKB_coeff (p : ℕ) (j : ℤ) :
    (literalKB (K:=K) p).coeff j=(1/6 : K)*
      (35*kernelLogCoeff p (1/4) j+
        (23*4)*kernelLogCoeff p (1/4) (j+p)+
        (23*4^2)*kernelLogCoeff p (1/4) (j+2*p)-
        5*kernelLogCoeff p 4 j-
        (29*(1/4))*kernelLogCoeff p 4 (j+p)-
        (29*(1/4)^2)*kernelLogCoeff p 4 (j+2*p)) := by
  simp only [literalKB,C_mul_coeff,AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_sub,Finsupp.add_apply,Finsupp.sub_apply,shift_coeff,
    kernelLog_coeff,show j-(-(p : ℤ))=j+p by omega,
    show j-(-2*(p : ℤ))=j+2*p by omega]

/-- A supported Frobenius band keeps its original integer denominator. -/
theorem kernelLogCoeff_band (p : ℕ) [Fact p.Prime] (c : ZMod p)
    (hc : c ≠ 0) (j : ℤ) (t : ℕ)
    (hj : 1 ≤ j+(t : ℤ)*(p : ℤ) ∧ j+(t : ℤ)*(p : ℤ)<p) :
    kernelLogCoeff p c (j+(t : ℤ)*(p : ℤ))=
      c^j*c^t/(j : ZMod p) := by
  have hn : 0 ≤ j+(t : ℤ)*(p : ℤ) := by omega
  have he : (((j+(t : ℤ)*(p : ℤ)).toNat : ℕ) : ℤ)=
      j+(t : ℤ)*(p : ℤ) := Int.toNat_of_nonneg hn
  have hpow : c^((j+(t : ℤ)*(p : ℤ)).toNat)=c^j*c^t := by
    rw [←zpow_natCast,he,zpow_add₀ hc,mul_comm (t : ℤ) (p : ℤ),zpow_mul]
    simp only [zpow_natCast,ZMod.pow_card]
  have hd : (((j+(t : ℤ)*(p : ℤ)).toNat : ℕ) : ZMod p)=(j : ZMod p) := by
    rw [←Int.cast_natCast,he,Int.cast_add,Int.cast_mul]
    simp only [Int.cast_natCast,ZMod.natCast_self,mul_zero,add_zero]
  rw [kernelLogCoeff,if_pos hj,hpow,hd]

private theorem kernelLogCoeff_outside (p : ℕ) (c : K) (j : ℤ)
    (hj : ¬(1≤j ∧ j<(p : ℤ))) : kernelLogCoeff p c j=0 := by
  rw [kernelLogCoeff,if_neg hj]

/-- Scalar extension preserves the whole finite coefficient window. -/
theorem kernelLogCoeff_map {L : Type*} [Field L] (f : K →+* L)
    (p : ℕ) (c : K) (j : ℤ) :
    f (kernelLogCoeff p c j)=kernelLogCoeff p (f c) j := by
  unfold kernelLogCoeff
  split_ifs <;> simp only [map_div₀,map_pow,map_natCast,map_zero]

/-- The literal Laurent kernel is natural under every field homomorphism. -/
theorem coefficientMap_literalKB {L : Type*} [Field L] (f : K →+* L) (p : ℕ) :
    WPActualChiSource.coefficientMap f (literalKB (K:=K) p)=
      literalKB (K:=L) p := by
  ext j
  rw [WPActualChiSource.coefficientMap_coeff,literalKB_coeff,literalKB_coeff]
  simp only [map_mul,map_add,map_sub,map_div₀,map_one,map_ofNat,map_pow,
    kernelLogCoeff_map]

/-- The complete original finite windows leave the origin coefficient zero. -/
theorem literalKB_zero (p : ℕ) : (literalKB (K:=K) p).coeff 0=0 := by
  rw [literalKB_coeff]
  simp only [zero_add]
  rw [kernelLogCoeff_outside p _ 0 (by omega),
    kernelLogCoeff_outside p _ (p : ℤ) (by omega),
    kernelLogCoeff_outside p _ (2*(p : ℤ)) (by omega),
    kernelLogCoeff_outside p _ 0 (by omega),
    kernelLogCoeff_outside p _ (p : ℤ) (by omega),
    kernelLogCoeff_outside p _ (2*(p : ℤ)) (by omega)]
  ring

/-- The original simple-pole source is annihilated without setting its scalar to zero. -/
theorem literalKB_simple_pole_zero (p : ℕ) (c : K) :
    (literalKB (K:=K) p*(LaurentPolynomial.C c*T (-1))).coeff (-1)=0 := by
  rw [show literalKB (K:=K) p*(LaurentPolynomial.C c*T (-1))=
      LaurentPolynomial.C c*T (-1)*literalKB (K:=K) p by ring,
    shift_coeff,show (-1 : ℤ)- -1=0 by norm_num,literalKB_zero,mul_zero]

/-- Equality of the entire original K_B and the supported native coefficient kernel. -/
theorem literalKB_eq_bKernel (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    literalKB (K:=ZMod p) p=bKernel p := by
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 6
    (Finset.mem_Ico.mpr (by omega))
  have ha : (1/4 : ZMod p)≠0 := one_div_ne_zero h4
  ext j
  have hb := bKernel_coeff_neg p (-j)
  rw [neg_neg] at hb
  rw [literalKB_coeff,hb]
  have hrecA : (1/4 : ZMod p)^(-j)=(4 : ZMod p)^j := by
    simp only [one_div,zpow_neg,inv_zpow,inv_inv]
  have hrecB : (4 : ZMod p)^(-j)=(1/4 : ZMod p)^j := by
    simp only [one_div,zpow_neg,inv_zpow]
  by_cases hjpos : 0<j
  · by_cases hjp : j<(p : ℤ)
    · have ha0 := kernelLogCoeff_band p (1/4) ha j 0 (by norm_num only [Nat.cast_zero,zero_mul,add_zero]; constructor <;> omega)
      have hb0 := kernelLogCoeff_band p 4 h4 j 0 (by norm_num only [Nat.cast_zero,zero_mul,add_zero]; constructor <;> omega)
      simp only [Nat.cast_zero,zero_mul,add_zero,pow_zero,mul_one] at ha0 hb0
      rw [ha0,hb0,kernelLogCoeff_outside p _ (j+p) (by omega),
        kernelLogCoeff_outside p _ (j+2*p) (by omega),
        kernelLogCoeff_outside p _ (j+p) (by omega),
        kernelLogCoeff_outside p _ (j+2*p) (by omega),
        if_pos (Finset.mem_Icc.mpr (by omega)),bWeight,
        if_pos (by omega : -j<0),hrecA,hrecB,Int.cast_neg]
      by_cases hz : (j : ZMod p)=0
      · simp only [hz,neg_zero,div_zero,mul_zero,add_zero,sub_zero]
      · field_simp [h6,hz]
        ring
    · by_cases he : j=(p : ℤ)
      · subst j
        rw [kernelLogCoeff_outside p _ _ (by omega),
          kernelLogCoeff_outside p _ _ (by omega),
          kernelLogCoeff_outside p _ _ (by omega),
          kernelLogCoeff_outside p _ _ (by omega),
          kernelLogCoeff_outside p _ _ (by omega),
          kernelLogCoeff_outside p _ _ (by omega)]
        simp only [Int.cast_neg,Int.cast_natCast,ZMod.natCast_self,
          neg_zero,div_zero,ite_self,mul_zero,add_zero,sub_zero]
      · rw [kernelLogCoeff_outside p _ _ (by omega),
          kernelLogCoeff_outside p _ _ (by omega),
          kernelLogCoeff_outside p _ _ (by omega),
          kernelLogCoeff_outside p _ _ (by omega),
          kernelLogCoeff_outside p _ _ (by omega),
          kernelLogCoeff_outside p _ _ (by omega),
          if_neg (by simp only [Finset.mem_Icc]; omega)]
        ring
  · by_cases hjzero : j=0
    · subst j
      rw [kernelLogCoeff_outside p _ _ (by omega),
        kernelLogCoeff_outside p _ _ (by omega),
        kernelLogCoeff_outside p _ _ (by omega),
        kernelLogCoeff_outside p _ _ (by omega),
        kernelLogCoeff_outside p _ _ (by omega),
        kernelLogCoeff_outside p _ _ (by omega)]
      simp only [neg_zero,Int.cast_zero,div_zero,ite_self,
        mul_zero,add_zero,sub_zero]
    · by_cases hjfirst : -(p : ℤ)<j
      · have ha1 := kernelLogCoeff_band p (1/4) ha j 1 (by norm_num only [Nat.cast_one,one_mul]; constructor <;> omega)
        have hb1 := kernelLogCoeff_band p 4 h4 j 1 (by norm_num only [Nat.cast_one,one_mul]; constructor <;> omega)
        simp only [Nat.cast_one,one_mul,pow_one] at ha1 hb1
        rw [kernelLogCoeff_outside p _ j (by omega),
          kernelLogCoeff_outside p _ j (by omega),ha1,hb1,
          kernelLogCoeff_outside p _ (j+2*p) (by omega),
          kernelLogCoeff_outside p _ (j+2*p) (by omega),
          if_pos (Finset.mem_Icc.mpr (by omega)),bWeight,
          if_neg (by omega : ¬(-j<0)),hrecA,hrecB,Int.cast_neg]
        by_cases hz : (j : ZMod p)=0
        · simp only [hz,neg_zero,div_zero,mul_zero,add_zero,sub_zero]
        · field_simp [h4,h6,hz]
          ring
      · by_cases he : j=-(p : ℤ)
        · subst j
          rw [kernelLogCoeff_outside p _ _ (by omega),
            kernelLogCoeff_outside p _ _ (by omega),
            kernelLogCoeff_outside p _ _ (by omega),
            kernelLogCoeff_outside p _ _ (by omega),
            kernelLogCoeff_outside p _ _ (by omega),
            kernelLogCoeff_outside p _ _ (by omega)]
          simp only [Int.cast_neg,Int.cast_natCast,ZMod.natCast_self,
            neg_zero,div_zero,ite_self,mul_zero,add_zero,sub_zero]
        · by_cases hjsecond : -2*(p : ℤ)<j
          · have ha2 := kernelLogCoeff_band p (1/4) ha j 2 (by norm_num only [Nat.cast_ofNat]; constructor <;> omega)
            have hb2 := kernelLogCoeff_band p 4 h4 j 2 (by norm_num only [Nat.cast_ofNat]; constructor <;> omega)
            simp only [Nat.cast_ofNat] at ha2 hb2
            rw [kernelLogCoeff_outside p _ j (by omega),
              kernelLogCoeff_outside p _ j (by omega),
              kernelLogCoeff_outside p _ (j+p) (by omega),
              kernelLogCoeff_outside p _ (j+p) (by omega),ha2,hb2,
              if_pos (Finset.mem_Icc.mpr (by omega)),bWeight,
              if_neg (by omega : ¬(-j<0)),hrecA,hrecB,Int.cast_neg]
            by_cases hz : (j : ZMod p)=0
            · simp only [hz,neg_zero,div_zero,mul_zero,add_zero,sub_zero]
            · field_simp [h4,h6,hz]
              ring
          · rw [kernelLogCoeff_outside p _ _ (by omega),
              kernelLogCoeff_outside p _ _ (by omega),
              kernelLogCoeff_outside p _ _ (by omega),
              kernelLogCoeff_outside p _ _ (by omega),
              kernelLogCoeff_outside p _ _ (by omega),
              kernelLogCoeff_outside p _ _ (by omega),
              if_neg (by simp only [Finset.mem_Icc]; omega)]
            ring

/-- The original literal kernel contracts the full actual native remainder. -/
theorem actual_bpair_literal_KB (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    NativeScalarRows.nativeBpair p hp=
      (literalKB (K:=ZMod p) p *
        WPFiniteLaurentDifferential.D
          (WPActualNativeCanonicalPart.nativeRemainder p hp)).coeff (-1) := by
  rw [literalKB_eq_bKernel p hp]
  exact actual_bpair_IR53 p hp

end WPFieldAssembly.ActualBpairContraction
