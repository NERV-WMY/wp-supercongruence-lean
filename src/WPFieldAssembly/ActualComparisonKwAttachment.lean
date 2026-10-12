import WPFieldAssembly.ActualBalancedTrace
import WPFieldAssembly.ActualKwSeriesAttachment
import WPFiniteJCarrier

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPPIntegralReduction WPActualChiSource
  WPActualRankTwoHatLift WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.ActualJointGreen

namespace WPFieldAssembly.ActualComparisonKwAttachment

set_option maxHeartbeats 1400000

/- The input is the original comparisonIntegral, including its branch constant,
both polynomial directions and both p-shifts. The cutoff comes from its actual
degree; no coefficient in its signed support is replaced by a field surrogate. -/

noncomputable def comparisonCoordinateQ : ℚ[X] := Polynomial.C (1/5 : ℚ)*(X+1)

noncomputable def movingComparisonQ (p : ℕ) [Fact p.Prime] : ℚ[X] :=
  (finiteEvenSquaredQ p).comp (4*comparisonCoordinateQ)-
    (finiteEvenSquaredQ p).comp comparisonCoordinateQ

noncomputable def comparisonBranchQ (p : ℕ) [Fact p.Prime] : ℚ :=
  (smallIntegralInverse p 15 *
    (17-4*((smallIntegralInverse p 4)^p+4^p))*comparisonEndIntegral p).val

theorem finiteEvenSquaredQ_degree (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (finiteEvenSquaredQ p).natDegree≤(p-1)/2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [finiteEvenSquaredQ,coeff_contract (by norm_num : (2 : ℕ)≠0),
    finiteEvenLogQ_eq_actual p hp]
  apply coeff_eq_zero_of_natDegree_lt
  have hd := rationalEvenLog_degree p
  omega

theorem movingComparisonQ_degree (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (movingComparisonQ p).natDegree≤(p-1)/2 := by
  have hc : comparisonCoordinateQ.natDegree≤1 := by
    unfold comparisonCoordinateQ
    exact (natDegree_C_mul_le _ _).trans (by compute_degree)
  have hc4 : (4*comparisonCoordinateQ : ℚ[X]).natDegree≤1 := by
    change (Polynomial.C (4 : ℚ)*comparisonCoordinateQ).natDegree≤1
    exact (natDegree_C_mul_le _ _).trans hc
  have hE := finiteEvenSquaredQ_degree p hp
  have h1 := (natDegree_comp_le (p := finiteEvenSquaredQ p)
    (q := 4*comparisonCoordinateQ)).trans (Nat.mul_le_mul hE hc4)
  have h2 := (natDegree_comp_le (p := finiteEvenSquaredQ p)
    (q := comparisonCoordinateQ)).trans (Nat.mul_le_mul hE hc)
  unfold movingComparisonQ
  exact (natDegree_sub_le_of_le (by simpa using h1) (by simpa using h2)).trans (by omega)

theorem comparisonCoordinateI_value (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (comparisonCoordinateI p).map (integralRationals p).subtype=comparisonCoordinateQ := by
  simp only [comparisonCoordinateI,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.map_add,Polynomial.map_X,Polynomial.map_one,comparisonCoordinateQ]
  simp only [Subring.subtype_apply]
  rw [smallIntegralInverse_value p 5 (by omega) (by omega)]
  norm_num

theorem movingEvenIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (ActualBalancedTrace.movingEvenIntegral p).map (integralRationals p).subtype=
      movingComparisonQ p := by
  simp only [ActualBalancedTrace.movingEvenIntegral,Polynomial.map_sub,
    Polynomial.map_comp,Polynomial.map_mul,Polynomial.map_ofNat,
    finiteEvenSquaredIntegral_value p hp,comparisonCoordinateI_value p hp,
    movingComparisonQ]

theorem comparisonRational_full_form (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    comparisonRational p hp=
      LaurentPolynomial.C (17/15 : ℚ)*T 0*
        ((movingComparisonQ p).toLaurent+invert (movingComparisonQ p).toLaurent)-
      LaurentPolynomial.C (4/15 : ℚ)*T (p : ℤ)*
        ((movingComparisonQ p).toLaurent+invert (movingComparisonQ p).toLaurent)-
      LaurentPolynomial.C (4/15 : ℚ)*T (-(p : ℤ))*
        ((movingComparisonQ p).toLaurent+invert (movingComparisonQ p).toLaurent)+
      LaurentPolynomial.C (comparisonBranchQ p) := by
  have hb : comparisonBranchQ p = (1/15 : ℚ)*
      (17-4*((smallIntegralInverse p 4^p).val+
        (4^p : integralRationals p).val))*(comparisonEndIntegral p).val := by
    change (integralRationals p).subtype
      (smallIntegralInverse p 15*
        (17-4*(smallIntegralInverse p 4^p+4^p))*comparisonEndIntegral p)=_
    simp only [map_mul,map_sub,map_ofNat,map_add]
    simp only [Subring.subtype_apply]
    rw [smallIntegralInverse_value p 15 (by omega) (by omega)]
    norm_num
  simp only [comparisonRational,comparisonIntegral,comparisonPhaseIntegral,
    map_add,map_mul,map_sub,map_ofNat,coefficientMap_C,coefficientMap_T,
    coefficientMap_toLaurent,coefficientMap_invert,movingEvenIntegral_value p hp,
    Subring.subtype_apply]
  rw [smallIntegralInverse_value p 15 (by omega) (by omega)]
  simp only [T_zero,mul_one]
  have h17 : (LaurentPolynomial.C (17/15 : ℚ) : ℚ[T;T⁻¹])=
      LaurentPolynomial.C (1/15 : ℚ)*17 := by
    change LaurentPolynomial.C (17/15 : ℚ)=LaurentPolynomial.C (1/15 : ℚ)*
      LaurentPolynomial.C 17
    rw [←map_mul]
    congr 1
    ring
  have h4 : (LaurentPolynomial.C (4/15 : ℚ) : ℚ[T;T⁻¹])=
      LaurentPolynomial.C (1/15 : ℚ)*4 := by
    change LaurentPolynomial.C (4/15 : ℚ)=LaurentPolynomial.C (1/15 : ℚ)*
      LaurentPolynomial.C 4
    rw [←map_mul]
    congr 1
    ring
  rw [h17,h4]
  rw [hb]
  simp only [map_mul,map_sub,map_ofNat,map_add]
  ring

theorem comparisonRational_upper_coeff_zero (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (n : ℤ) (hn : ((p+(p-1)/2 : ℕ) : ℤ)<n) :
    (comparisonRational p hp).coeff n=0 := by
  have hd := movingComparisonQ_degree p hp
  have h1 : (movingComparisonQ p).toLaurent.coeff n=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inr (by omega))
  have h2 : (movingComparisonQ p).toLaurent.coeff (-n)=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))
  have h3 : (movingComparisonQ p).toLaurent.coeff (n-p)=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inr (by omega))
  have h4 : (movingComparisonQ p).toLaurent.coeff (-(n-p))=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))
  have h5 : (movingComparisonQ p).toLaurent.coeff (n+p)=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inr (by omega))
  have h6 : (movingComparisonQ p).toLaurent.coeff (-(n+p))=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))
  rw [comparisonRational_full_form p hp]
  simp only [AddMonoidAlgebra.coeff_add,AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply,Finsupp.sub_apply,WPFiniteJCarrier.shifted_coeff,
    LaurentPolynomial.invert_apply,sub_zero,sub_neg_eq_add,h1,h2,h3,h4,h5,h6,
    add_zero,mul_zero,sub_zero,zero_add]
  simp [LaurentPolynomial.C_apply,show n≠0 by omega]

theorem laurent_full_signed_expansion {R : Type*} [CommRing R] (L : R[T;T⁻¹]) :
    L=∑ n∈L.coeff.support, LaurentPolynomial.C (L.coeff n)*T n := by
  simp only [←single_eq_C_mul_T]
  change L=L.coeff.sum AddMonoidAlgebra.single
  exact (AddMonoidAlgebra.sum_coeff_single L).symm

theorem comparisonRational_support_upper (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (n : ℤ) (hn : n∈(comparisonRational p hp).coeff.support) :
    n≤((p+(p-1)/2 : ℕ) : ℤ) := by
  by_contra hb
  exact (Finsupp.mem_support_iff.mp hn)
    (comparisonRational_upper_coeff_zero p hp n (by omega))

theorem comparisonField_upper_coeff_zero (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (n : ℤ) (hn : ((p+(p-1)/2 : ℕ) : ℤ)<n) :
    (comparisonField p : (ZMod p)[T;T⁻¹]).coeff n=0 := by
  have h := comparisonRational_upper_coeff_zero p hp n hn
  rw [comparisonRational,coefficientMap_coeff] at h
  have hI : (comparisonIntegral p).coeff n=0 := by
    apply Subtype.ext
    exact h
  rw [←comparisonIntegral_field p hp,coefficientMap_coeff,hI,map_zero]

theorem comparisonField_support_upper (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (n : ℤ) (hn : n∈(comparisonField p : (ZMod p)[T;T⁻¹]).coeff.support) :
    n≤((p+(p-1)/2 : ℕ) : ℤ) := by
  by_contra hb
  exact (Finsupp.mem_support_iff.mp hn)
    (comparisonField_upper_coeff_zero p hp n (by omega))

noncomputable def comparisonKwCarryI (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    integralRationals p :=
  ActualKwSeriesAttachment.actualFiniteCarryIntegral p (p+(p-1)/2) hp
    (comparisonIntegral p)

/-- The whole original comparison trace is divided before its field carry is taken. -/
theorem comparisonKwCarryI_value (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (comparisonKwCarryI p hp).val=
      (1/(p : ℚ))*(ActualKwSeriesAttachment.actualWeightedTrace p
        (comparisonRational p hp)-(-3*5^(p-1) : ℚ)*
          ActualKwSeriesAttachment.seriesWeightedTrace
            (ActualKwFirstCarry.frobeniusUnit p (1/4 : ℚ) 4 (11/4))
              (comparisonRational p hp)) := by
  symm
  exact ActualKwSeriesAttachment.actualWeightedTrace_divided_full_source p
    (p+(p-1)/2) hp (comparisonIntegral p)
    (comparisonRational p hp).coeff.support (comparisonRational p hp).coeff
    (laurent_full_signed_expansion _) (comparisonRational_support_upper p hp)

/-- All F1 coefficients below p+N, including the p-phase and top N band, survive. -/
theorem comparisonKwCarryI_field (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (comparisonKwCarryI p hp)=(-3 : ZMod p)*
      (∑ r∈Finset.range (p+(p-1)/2),
        PowerSeries.coeff r (ActualKwFirstCarry.literalFirstTwoPhases p)*
          ActualKwWeightedTrace.fieldDlogQ p
            (T (-(r : ℤ))*(comparisonField p : (ZMod p)[T;T⁻¹]))) := by
  rw [comparisonKwCarryI,ActualKwSeriesAttachment.actualFiniteCarryIntegral_field
    p (p+(p-1)/2) hp (by omega) (comparisonIntegral p),
    comparisonIntegral_field p hp]

end WPFieldAssembly.ActualComparisonKwAttachment
