import WPBivariateDifferential
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Derivative

open scoped LaurentSeries BigOperators
open HahnSeries Polynomial

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 1500000

local instance residueCoefficientIntAlgebra {L : Type*} [Field L] : Algebra ℤ (RatFunc L) :=
  Ring.toIntAlgebra (RatFunc L)

noncomputable instance rationalLaurentAlgebra {L : Type*} [Field L] :
    Algebra (RatFunc L) (LaurentSeries L) := RatFunc.liftAlgebra L (LaurentSeries L)

section Laurent

variable {K : Type*} [Field K]

local instance residueIntAlgebra : Algebra ℤ (LaurentSeries K) :=
  Ring.toIntAlgebra (LaurentSeries K)

noncomputable def laurentS (f : LaurentSeries K) : LaurentSeries K :=
  LaurentSeries.derivative K f

@[simp] theorem laurentS_coeff (f : LaurentSeries K) (n : ℤ) :
    (laurentS f).coeff n = ((n + 1 : ℤ) : K) * f.coeff (n + 1) := by
  simp [laurentS, LaurentSeries.derivative, LaurentSeries.hasseDeriv_coeff,
    zsmul_eq_mul]

theorem laurentS_single_mul (k : ℤ) (a : K) (f : LaurentSeries K) :
    laurentS (single k a * f) = single (k - 1) ((k : K) * a) * f +
      single k a * laurentS f := by
  ext n
  simp only [laurentS_coeff, HahnSeries.coeff_add, coeff_single_mul]
  rw [show n - (k - 1) = n + 1 - k by omega,
    show n - k + 1 = n + 1 - k by omega]
  push_cast
  ring

theorem laurentS_powerSeries (P : PowerSeries K) :
    laurentS (P : LaurentSeries K) = ((PowerSeries.derivative K P : PowerSeries K) :
      LaurentSeries K) := by
  ext n
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, laurentS_coeff,
      show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega,
      LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_derivative]
    push_cast
    ring
  | negSucc n =>
    cases n with
    | zero => simp [laurentS_coeff, PowerSeries.coeff_coe]
    | succ n =>
      have h : Int.negSucc (n + 1) + 1 < 0 := by omega
      simp [laurentS_coeff, PowerSeries.coeff_coe, h]

theorem laurentS_mul (f g : LaurentSeries K) :
    laurentS (f * g) = laurentS f * g + f * laurentS g := by
  let a : ℤ := f.order
  let b : ℤ := g.order
  let P : PowerSeries K := f.powerSeriesPart
  let Q : PowerSeries K := g.powerSeriesPart
  have hf : single a (1 : K) * (P : LaurentSeries K) = f :=
    LaurentSeries.single_order_mul_powerSeriesPart f
  have hg : single b (1 : K) * (Q : LaurentSeries K) = g :=
    LaurentSeries.single_order_mul_powerSeriesPart g
  have hpq : (single a (1 : K) * (P : LaurentSeries K)) *
      (single b 1 * (Q : LaurentSeries K)) =
      single (a + b) 1 * ((P * Q : PowerSeries K) : LaurentSeries K) := by
    rw [PowerSeries.coe_mul]
    calc
      _ = (single a 1 * single b 1) * ((P : LaurentSeries K) * (Q : LaurentSeries K)) := by
        ring
      _ = _ := by rw [single_mul_single, one_mul]
  have hab : single (a + b - 1) ((a + b : ℤ) : K) =
      single (a - 1) (a : K) * single b 1 + single a 1 * single (b - 1) (b : K) := by
    rw [single_mul_single, single_mul_single, mul_one, one_mul,
      show a - 1 + b = a + b - 1 by omega,
      show a + (b - 1) = a + b - 1 by omega, ← single_add]
    congr 1
    push_cast
    rfl
  rw [← hf, ← hg, hpq, laurentS_single_mul, laurentS_powerSeries,
    Derivation.leibniz, smul_eq_mul, PowerSeries.coe_add, PowerSeries.coe_mul,
    PowerSeries.coe_mul, mul_one, hab]
  rw [laurentS_single_mul, laurentS_single_mul,
    laurentS_powerSeries, laurentS_powerSeries, mul_one, mul_one]
  have hs : (single (a+b) (1 : K) : LaurentSeries K) = single a 1*single b 1 := by
    rw [single_mul_single, one_mul]
  simp only [smul_eq_mul, PowerSeries.coe_mul, hs]
  ring

noncomputable def laurentSAddHom : LaurentSeries K →+ LaurentSeries K where
  toFun := laurentS
  map_zero' := (LaurentSeries.derivative K).map_zero
  map_add' := (LaurentSeries.derivative K).map_add

noncomputable def laurentSDerivation : Derivation ℤ (LaurentSeries K) (LaurentSeries K) :=
  Derivation.mk' laurentSAddHom.toIntLinearMap (by
    intro f g
    change laurentS (f * g) = f * laurentS g + g * laurentS f
    rw [laurentS_mul]
    ring)

theorem laurentS_polynomial (P : K[X]) :
    laurentSDerivation (algebraMap K[X] (LaurentSeries K) P) =
      algebraMap K[X] (LaurentSeries K) (derivative P) := by
  change laurentS ((P : PowerSeries K) : LaurentSeries K) = _
  rw [laurentS_powerSeries, PowerSeries.derivative_coe]
  rfl

/-- Exact formal residue at s=0. -/
noncomputable def laurentResidue (f : LaurentSeries K) : K := f.coeff (-1)

@[simp] theorem laurentResidue_s_derivative (f : LaurentSeries K) :
    laurentResidue (laurentS f) = 0 := by
  simp [laurentResidue]

@[simp] theorem laurentResidue_add (f g : LaurentSeries K) :
    laurentResidue (f + g) = laurentResidue f + laurentResidue g := rfl

@[simp] theorem laurentResidue_sub (f g : LaurentSeries K) :
    laurentResidue (f - g) = laurentResidue f - laurentResidue g := rfl

noncomputable def coefficientDerivativeZero
    (D : Derivation ℤ K K) : ZeroHom K K := ⟨D, map_zero D⟩

noncomputable def laurentCoefficientDerivative
    (D : Derivation ℤ K K) (f : LaurentSeries K) : LaurentSeries K :=
  f.map (coefficientDerivativeZero D)

@[simp] theorem laurentCoefficientDerivative_coeff
    (D : Derivation ℤ K K) (f : LaurentSeries K) (n : ℤ) :
    (laurentCoefficientDerivative D f).coeff n = D (f.coeff n) := rfl

theorem laurentCoefficientDerivative_mul
    (D : Derivation ℤ K K) (f g : LaurentSeries K) :
    laurentCoefficientDerivative D (f * g) =
      laurentCoefficientDerivative D f * g + f * laurentCoefficientDerivative D g := by
  ext n
  rw [laurentCoefficientDerivative_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_add]
  dsimp only [laurentCoefficientDerivative]
  rw [
    coeff_mul_left' f.isPWO_support
      (HahnSeries.support_map_subset f (coefficientDerivativeZero D)),
    coeff_mul_right' g.isPWO_support
      (HahnSeries.support_map_subset g (coefficientDerivativeZero D))]
  have hm (h : LaurentSeries K) (n : ℤ) :
      (h.map (coefficientDerivativeZero D)).coeff n = D (h.coeff n) := rfl
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, hm, Finset.sum_add_distrib]
  simp only [mul_comm, add_comm]

noncomputable def laurentCoefficientDerivativeAddHom
    (D : Derivation ℤ K K) : LaurentSeries K →+ LaurentSeries K where
  toFun := laurentCoefficientDerivative D
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp

noncomputable def laurentXDerivation (D : Derivation ℤ K K) :
    Derivation ℤ (LaurentSeries K) (LaurentSeries K) :=
  Derivation.mk' (laurentCoefficientDerivativeAddHom D).toIntLinearMap (by
    intro f g
    change laurentCoefficientDerivative D (f * g) =
      f * laurentCoefficientDerivative D g + g * laurentCoefficientDerivative D f
    rw [laurentCoefficientDerivative_mul]
    ring)

@[simp] theorem laurentResidue_coefficient_derivative
    (D : Derivation ℤ K K) (f : LaurentSeries K) :
    laurentResidue (laurentCoefficientDerivative D f) = D (laurentResidue f) := rfl

theorem rationalLift_laurent_embedding
    (D : Derivation ℤ K[X] K[X])
    (E : Derivation ℤ (LaurentSeries K) (LaurentSeries K))
    (hE : ∀ P : K[X], E (algebraMap K[X] (LaurentSeries K) P) =
      algebraMap K[X] (LaurentSeries K) (D P)) (f : RatFunc K) :
    algebraMap (RatFunc K) (LaurentSeries K) (rationalLift D f) =
      E (algebraMap (RatFunc K) (LaurentSeries K) f) := by
  conv_rhs => rw [← RatFunc.num_div_denom f]
  simp only [rationalLift, map_div₀, map_sub, map_mul, map_pow,
    ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) (LaurentSeries K),
    Derivation.leibniz_div, hE, smul_eq_mul]
  ring

theorem partialS_laurent_embedding (f : RatFunc (RatFunc ℚ)) :
    algebraMap (RatFunc (RatFunc ℚ)) (LaurentSeries (RatFunc ℚ)) (partialS f) =
      laurentS (algebraMap (RatFunc (RatFunc ℚ)) (LaurentSeries (RatFunc ℚ)) f) := by
  change algebraMap (RatFunc (RatFunc ℚ)) (LaurentSeries (RatFunc ℚ))
      (rationalLift (Polynomial.derivative'.restrictScalars ℤ) f) =
    laurentSDerivation (algebraMap (RatFunc (RatFunc ℚ)) (LaurentSeries (RatFunc ℚ)) f)
  exact rationalLift_laurent_embedding (Polynomial.derivative'.restrictScalars ℤ)
    laurentSDerivation laurentS_polynomial f

theorem partialX_laurent_polynomial (P : Polynomial (RatFunc ℚ)) :
    laurentXDerivation xDerivation
      (algebraMap (Polynomial (RatFunc ℚ)) (LaurentSeries (RatFunc ℚ)) P) =
    algebraMap (Polynomial (RatFunc ℚ)) (LaurentSeries (RatFunc ℚ))
      (coefficientXDerivation P) := by
  ext n
  cases n with
  | ofNat n =>
    change xDerivation
      ((((P : PowerSeries (RatFunc ℚ)) : LaurentSeries (RatFunc ℚ))).coeff (n : ℤ)) =
        (((((coefficientXDerivation P) : PowerSeries (RatFunc ℚ)) :
          LaurentSeries (RatFunc ℚ))).coeff (n : ℤ))
    rw [LaurentSeries.coeff_coe_powerSeries, LaurentSeries.coeff_coe_powerSeries,
      Polynomial.coeff_coe, Polynomial.coeff_coe, coefficientXDerivation_coeff]
    rfl
  | negSucc n =>
    change xDerivation
      ((((P : PowerSeries (RatFunc ℚ)) : LaurentSeries (RatFunc ℚ))).coeff (Int.negSucc n)) =
        (((((coefficientXDerivation P) : PowerSeries (RatFunc ℚ)) :
          LaurentSeries (RatFunc ℚ))).coeff (Int.negSucc n))
    simp [PowerSeries.coeff_coe]

theorem partialX_laurent_embedding (f : RatFunc (RatFunc ℚ)) :
    algebraMap (RatFunc (RatFunc ℚ)) (LaurentSeries (RatFunc ℚ)) (partialX f) =
      laurentCoefficientDerivative xDerivation
        (algebraMap (RatFunc (RatFunc ℚ)) (LaurentSeries (RatFunc ℚ)) f) := by
  exact rationalLift_laurent_embedding _ (laurentXDerivation xDerivation)
    partialX_laurent_polynomial f

@[simp] theorem rational_laurent_coefficient (a : K) :
    algebraMap (RatFunc K) (LaurentSeries K) (RatFunc.C a) = HahnSeries.C a := by
  rw [← RatFunc.algebraMap_C,
    ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) (LaurentSeries K)]
  change ((Polynomial.C a : PowerSeries K) : LaurentSeries K) = _
  rw [Polynomial.coe_C, PowerSeries.coe_C]

noncomputable def rationalResidue (f : RatFunc (RatFunc ℚ)) : RatFunc ℚ :=
  laurentResidue (algebraMap (RatFunc (RatFunc ℚ)) (LaurentSeries (RatFunc ℚ)) f)

@[simp] theorem rationalResidue_add (f g : RatFunc (RatFunc ℚ)) :
    rationalResidue (f+g) = rationalResidue f+rationalResidue g := by
  simp only [rationalResidue, map_add, laurentResidue_add]

@[simp] theorem rationalResidue_sub (f g : RatFunc (RatFunc ℚ)) :
    rationalResidue (f-g) = rationalResidue f-rationalResidue g := by
  simp only [rationalResidue, map_sub, laurentResidue_sub]

@[simp] theorem rationalResidue_neg (f : RatFunc (RatFunc ℚ)) :
    rationalResidue (-f) = -rationalResidue f := by
  simp only [rationalResidue, map_neg, laurentResidue, HahnSeries.coeff_neg]

theorem rationalResidue_coefficient_mul (a : RatFunc ℚ) (f : RatFunc (RatFunc ℚ)) :
    rationalResidue (RatFunc.C a*f) = a*rationalResidue f := by
  simp only [rationalResidue, laurentResidue, map_mul, rational_laurent_coefficient,
    HahnSeries.C_apply, coeff_single_mul, sub_zero]

theorem rationalResidue_sum {ι : Type*} (s : Finset ι)
    (f : ι → RatFunc (RatFunc ℚ)) :
    rationalResidue (∑ i ∈ s, f i) = ∑ i ∈ s, rationalResidue (f i) := by
  simp only [rationalResidue, laurentResidue, map_sum, HahnSeries.coeff_sum]

@[simp] theorem rationalResidue_partialS (f : RatFunc (RatFunc ℚ)) :
    rationalResidue (partialS f) = 0 := by
  rw [rationalResidue, partialS_laurent_embedding, laurentResidue_s_derivative]

theorem rationalResidue_partialX (f : RatFunc (RatFunc ℚ)) :
    rationalResidue (partialX f) = rationalDerivative (rationalResidue f) := by
  rw [rationalResidue, partialX_laurent_embedding, laurentResidue_coefficient_derivative]
  rfl

end Laurent

end

end WPForcedSourceStokes
