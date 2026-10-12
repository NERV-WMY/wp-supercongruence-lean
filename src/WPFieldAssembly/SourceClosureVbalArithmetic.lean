import WPFieldAssembly.ActualEntropyFifth
import WPFieldAssembly.ActualKwRationalRowAttachment

namespace WPFieldAssembly.SourceClosureVbalArithmetic

open WPPIntegralReduction ActualEntropyFifth WPFiniteField

variable {K : Type*} [Field K]

/-- The ordinary product of the original fifth first carry; its weight-two
endpoints are kept separately in the actual integral attachment below. -/
def fifthProduct (q k C : K) : K :=
  -(169/50 : K)*q^2+(24/5 : K)*q*k-(15/8 : K)*k^2+
    (103/25 : K)*q*C-(11/5 : K)*k*C-(37/50 : K)*C^2

/-- The SB103 product before substituting the fifth entropy endpoint. -/
def entropyProduct (q r k C E : K) : K :=
  (321/10 : K)*q^2-(21/2 : K)*q*r-(9/40 : K)*r^2-
    (156/5 : K)*q*k+(9/4 : K)*r*k+(279/32 : K)*k^2-
    (308/5 : K)*q*C-(33/5 : K)*r*C+(693/40 : K)*k*C+(27/8 : K)*C^2+
    (132/5 : K)*q*E-(99/8 : K)*k*E-(33/4 : K)*E*C+(99/8 : K)*E^2

/-- The whole ordinary product in SB103g, retaining Q3 and the fifth C. -/
def closedProduct (q r k C : K) : K :=
  (456/25 : K)*q^2-(21/2 : K)*q*r-(9/40 : K)*r^2-
    18*q*k+(9/4 : K)*r*k+(45/8 : K)*k^2-
    (1309/25 : K)*q*C-(33/5 : K)*r*C+(66/5 : K)*k*C+(111/50 : K)*C^2

/-- The fifth norm and endpoint substitution determines every ordinary product
coefficient; Aeven(T0) and its endpoint difference are outside this identity. -/
theorem fifth_product_identity (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (q k C : K) :
    let E := C/5-6*q/5+k/2
    let H := k/2-(4/5 : K)*q;
    -(22/5 : K)*q^2+(47/10 : K)*q*k-(3/2 : K)*k^2+
      (q+4*k)*C/5-(11/5 : K)*q*E-
      (33/8 : K)*E^2+(33/4 : K)*E*H+(11/4 : K)*E*C-
      (45/8 : K)*H^2-(35/4 : K)*H*C-(9/8 : K)*C^2=fifthProduct q k C := by
  dsimp only
  unfold fifthProduct
  have h4 : (4 : K) ≠ 0 := by
    convert mul_ne_zero h2 h2 using 1
    norm_num
  have h8 : (8 : K) ≠ 0 := by
    convert mul_ne_zero h2 h4 using 1
    norm_num
  have h10 : (10 : K) ≠ 0 := by
    convert mul_ne_zero h2 h5 using 1
    norm_num
  have h25 : (25 : K) ≠ 0 := by
    convert mul_ne_zero h5 h5 using 1
    norm_num
  have h50 : (50 : K) ≠ 0 := by
    convert mul_ne_zero h2 h25 using 1
    norm_num
  field_simp [h2,h4,h5,h8,h10,h25,h50]
  ring

/-- SB103a changes the product alphabet after the original p-division. -/
theorem entropy_product_identity (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (q r k C : K) :
    entropyProduct q r k C (C/5-6*q/5+k/2)=closedProduct q r k C := by
  have h4 : (4 : K) ≠ 0 := by
    convert mul_ne_zero h2 h2 using 1
    norm_num
  have h8 : (8 : K) ≠ 0 := by
    convert mul_ne_zero h2 h4 using 1
    norm_num
  have h10 : (10 : K) ≠ 0 := by
    convert mul_ne_zero h2 h5 using 1
    norm_num
  have h25 : (25 : K) ≠ 0 := by
    convert mul_ne_zero h5 h5 using 1
    norm_num
  have h32 : (32 : K) ≠ 0 := by
    convert mul_ne_zero h4 h8 using 1
    norm_num
  have h40 : (40 : K) ≠ 0 := by
    convert mul_ne_zero h5 h8 using 1
    norm_num
  have h50 : (50 : K) ≠ 0 := by
    convert mul_ne_zero h2 h25 using 1
    norm_num
  unfold entropyProduct closedProduct
  field_simp [h2,h4,h5,h8,h10,h25,h32,h40,h50]
  ring

/-- The Q3 Q11 terms cancel, while the entire original Q11 coefficient remains. -/
theorem Q11_product_identity (q r C j : K) :
    -(11/5 : K)*j*(-(9/4 : K)*r-3*C+3*(q+(3/4 : K)*r))=
      -(33/5 : K)*(q-C)*j := by
  ring

/-- The actual reduced fifth carry has this product and both original Aeven ends. -/
theorem actual_fifth_carry_product (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u^2=(1/5 : K)) :
    actualFifthCarryField p u=
      fifthProduct (WPFiniteInversion.integerFermatQuotient p 2 : K)
        (WPFiniteInversion.integerFermatQuotient p 5 : K) (WPFifthEntropy.C p u)+
      WPFiniteNC122.Aeven p (-(11/5 : K)*u)-
      (11/5 : K)*(WPFiniteNC122.Aeven p (2*u)-WPFiniteNC122.Aeven p u) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have he : E p u=WPFifthEntropy.C p u/5-
      6*(WPFiniteInversion.integerFermatQuotient p 2 : K)/5+
      (WPFiniteInversion.integerFermatQuotient p 5 : K)/2 := by
    rw [WPFifthEntropy.E_at_fifth p hp u hu]
    ring
  unfold actualFifthCarryField
  dsimp only
  change _ + WPFiniteNC122.Aeven p (-(11/5 : K)*u)-
    (11/5 : K)*(WPFiniteNC122.Aeven p (2*u)-WPFiniteNC122.Aeven p u)=_
  rw [show E p (2*u)-E p u=WPFifthEntropy.C p u from rfl,he]
  rw [fifth_product_identity h2 h5]

/-- The product evaluation is attached to the canonical original rational carry. -/
theorem actual_fifth_integral_product (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u^2=(1/5 : K)) :
    (ZMod.castHom (dvd_refl p) K) (residueHom p (actualFifthCarryIntegral p))=
      fifthProduct (WPFiniteInversion.integerFermatQuotient p 2 : K)
        (WPFiniteInversion.integerFermatQuotient p 5 : K) (WPFifthEntropy.C p u)+
      WPFiniteNC122.Aeven p (-(11/5 : K)*u)-
      (11/5 : K)*(WPFiniteNC122.Aeven p (2*u)-WPFiniteNC122.Aeven p u) := by
  rw [actualFifthCarryIntegral_field p hp u hu,actual_fifth_carry_product p hp u hu]

end WPFieldAssembly.SourceClosureVbalArithmetic
