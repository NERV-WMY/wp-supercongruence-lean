import WPReview.ResidueConnection
import WPGammaURegular.StepBlocks
import Mathlib.NumberTheory.Padics.RingHoms

noncomputable section

namespace WPGammaIntegralLift

open Polynomial
open WPResidueQuotient

variable (p : ℕ) [Fact p.Prime]

abbrev S := Parameter.ParameterRing ℤ_[p]

/-- The genuine residue map of p-adic integers. -/
def coefficientReduce : ℤ_[p] →+* ZMod p := PadicInt.toZMod

theorem coefficientReduce_surjective : Function.Surjective (coefficientReduce p) :=
  ZMod.ringHom_surjective (coefficientReduce p)

theorem coefficientReduce_kernel (a : ℤ_[p]) :
    coefficientReduce p a = 0 ↔ ∃ b, a = (p : ℤ_[p]) * b := by
  change a ∈ RingHom.ker PadicInt.toZMod ↔ _
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]
  rfl

def regularU : WPGammaURegular.R p := ⟨WPGammaU.u p, WPGammaURegular.u_mem p⟩
def regularUInverse : WPGammaURegular.R p :=
  ⟨(WPGammaU.u p)⁻¹, WPGammaURegular.u_inv_mem p⟩
def regularDelta : WPGammaURegular.R p := 1 - (6 * regularU p)^6

theorem regularU_mul_inverse : regularU p * regularUInverse p = 1 := by
  apply Subtype.ext
  apply mul_inv_cancel₀
  simpa only [regularU, WPGammaU.u, WPPsi.polyMap, map_zero] using
    (IsFractionRing.injective (Polynomial (ZMod p)) (WPPsi.K p)).ne
      (Polynomial.X_ne_zero : (X : Polynomial (ZMod p)) ≠ 0)

theorem regularDelta_mul_inverse : regularDelta p * WPGammaURegular.deltaInverse p = 1 := by
  apply Subtype.ext
  apply mul_inv_cancel₀
  change WPGammaU.delta p ≠ 0
  have hd : (Parameter.discriminantPolynomial (ZMod p)) ≠ 0 := by
    intro h
    have he := congrArg (Polynomial.eval 0) h
    simp [Parameter.discriminantPolynomial] at he
  have he := (IsFractionRing.injective (Polynomial (ZMod p)) (WPPsi.K p)).ne hd
  simpa [Parameter.discriminantPolynomial, WPGammaU.delta, WPGammaU.z,
    WPGammaU.u, WPPsi.polyMap, map_ofNat] using he

def baseReduce : Polynomial ℤ_[p] →+* WPGammaURegular.R p :=
  Polynomial.eval₂RingHom
    ((algebraMap (ZMod p) (WPGammaURegular.R p)).comp (coefficientReduce p))
    (regularU p)

@[simp] theorem baseReduce_X : baseReduce p X = regularU p := by
  simp [baseReduce, Polynomial.eval₂RingHom, Polynomial.eval₂AddMonoidHom]

@[simp] theorem baseReduce_C (a : ℤ_[p]) :
    baseReduce p (C a) = algebraMap (ZMod p) (WPGammaURegular.R p) (coefficientReduce p a) := by
  simp [baseReduce, Polynomial.eval₂RingHom, Polynomial.eval₂AddMonoidHom]

theorem baseReduce_denominator : IsUnit (baseReduce p (Parameter.denominatorPolynomial ℤ_[p])) := by
  have hu : IsUnit (regularU p) :=
    isUnit_iff_exists_inv.mpr ⟨_, regularU_mul_inverse p⟩
  have hd : IsUnit (regularDelta p) :=
    isUnit_iff_exists_inv.mpr ⟨_, regularDelta_mul_inverse p⟩
  simpa [Parameter.denominatorPolynomial, Parameter.discriminantPolynomial,
    regularDelta, map_ofNat] using hu.mul hd

/-- Reduction on the actual localization Zp[u,1/(u*(1-(6u)^6))]. -/
def reduce : S p →+* WPGammaURegular.R p :=
  IsLocalization.Away.lift (Parameter.denominatorPolynomial ℤ_[p]) (baseReduce_denominator p)

@[simp] theorem reduce_polynomial (f : Polynomial ℤ_[p]) :
    reduce p (algebraMap (Polynomial ℤ_[p]) (S p) f) = baseReduce p f :=
  IsLocalization.Away.lift_eq _ _ _

@[simp] theorem reduce_u : reduce p Parameter.u = regularU p := by
  simp [Parameter.u]

@[simp] theorem reduce_discriminant : reduce p Parameter.discriminant = regularDelta p := by
  simp [Parameter.discriminant, regularDelta, map_ofNat]

@[simp] theorem reduce_coefficient (a : ℤ_[p]) :
    reduce p (algebraMap ℤ_[p] (S p) a) =
      algebraMap (ZMod p) (WPGammaURegular.R p) (coefficientReduce p a) := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] (Polynomial ℤ_[p]) (S p)]
  simp

theorem baseReduce_val (f : Polynomial ℤ_[p]) :
    (baseReduce p f : WPPsi.K p) = WPPsi.polyMap p (f.map (coefficientReduce p)) := by
  have he : (WPGammaURegular.coefficientRing p).val.toRingHom.comp (baseReduce p) =
      (WPPsi.polyMap p).comp (Polynomial.mapRingHom (coefficientReduce p)) := by
    apply Polynomial.ringHom_ext
    · intro a
      change (baseReduce p (C a) : WPPsi.K p) = _
      rw [baseReduce_C]
      change algebraMap (ZMod p) (WPPsi.K p) (coefficientReduce p a) =
        WPPsi.polyMap p ((C a).map (coefficientReduce p))
      rw [Polynomial.map_C]
      exact IsScalarTower.algebraMap_apply (ZMod p) (Polynomial (ZMod p))
        (WPPsi.K p) (coefficientReduce p a)
    · simp [regularU, WPGammaU.u]
  exact RingHom.congr_fun he f

theorem baseReduce_zero_iff (f : Polynomial ℤ_[p]) :
    baseReduce p f = 0 ↔ f.map (coefficientReduce p) = 0 := by
  constructor
  · intro h
    apply IsFractionRing.injective (Polynomial (ZMod p)) (WPPsi.K p)
    change WPPsi.polyMap p (f.map (coefficientReduce p)) = WPPsi.polyMap p 0
    rw [← baseReduce_val, h, map_zero]
    rfl
  · intro h
    apply Subtype.ext
    simp only [baseReduce_val, h, map_zero, Subalgebra.coe_zero]

theorem polynomialReduce_kernel (f : Polynomial ℤ_[p]) :
    f.map (coefficientReduce p) = 0 ↔ ∃ g, f = (p : Polynomial ℤ_[p]) * g := by
  constructor
  · intro h
    have hn (n : ℕ) : coefficientReduce p (f.coeff n) = 0 := by
      have he := congrArg (fun f : Polynomial (ZMod p) => f.coeff n) h
      simpa using he
    choose b hb using fun n => (coefficientReduce_kernel p (f.coeff n)).mp (hn n)
    refine ⟨∑ n ∈ f.support, monomial n (b n), ?_⟩
    rw [Finset.mul_sum]
    conv_lhs => rw [← Polynomial.sum_monomial_eq f]
    apply Finset.sum_congr rfl
    intro n _
    change monomial n (f.coeff n) = _
    rw [hb n, ← Polynomial.C_mul_monomial]
    simp
  · rintro ⟨g, rfl⟩
    simp

theorem reduce_kernel (a : S p) : reduce p a = 0 ↔ ∃ b, a = (p : S p) * b := by
  obtain ⟨f, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (Submonoid.powers (Parameter.denominatorPolynomial ℤ_[p])) a
  constructor
  · intro h
    have hf : baseReduce p f = 0 := by
      have he := (IsLocalization.lift_mk'_spec (S := S p) (g := baseReduce p)
        (fun s : Submonoid.powers (Parameter.denominatorPolynomial ℤ_[p]) => by
          obtain ⟨n, hn⟩ := s.property
          rw [← hn, map_pow]
          exact (baseReduce_denominator p).pow n) f 0 s).mp h
      simpa using he
    obtain ⟨g, hg⟩ := (polynomialReduce_kernel p f).mp ((baseReduce_zero_iff p f).mp hf)
    refine ⟨IsLocalization.mk' (S p) g s, ?_⟩
    rw [hg, IsLocalization.mk'_eq_iff_eq_mul, map_mul]
    simp only [map_natCast]
    rw [mul_assoc, IsLocalization.mk'_spec]
  · rintro ⟨b, hb⟩
    rw [hb, map_mul, map_natCast]
    rw [← map_natCast (algebraMap (ZMod p) (WPGammaURegular.R p)) p,
      ZMod.natCast_self, map_zero, zero_mul]

@[simp] theorem reduce_uInverse : reduce p Parameter.uInverse = regularUInverse p := by
  have hu : IsUnit (regularU p) :=
    isUnit_iff_exists_inv.mpr ⟨_, regularU_mul_inverse p⟩
  apply hu.mul_left_inj.mp
  rw [← reduce_u p, ← map_mul, mul_comm Parameter.uInverse,
    Parameter.u_mul_uInverse, map_one, reduce_u, mul_comm,
    regularU_mul_inverse]

@[simp] theorem reduce_discriminantInverse :
    reduce p Parameter.discriminantInverse = WPGammaURegular.deltaInverse p := by
  have hu : IsUnit (regularDelta p) :=
    isUnit_iff_exists_inv.mpr ⟨_, regularDelta_mul_inverse p⟩
  apply hu.mul_left_inj.mp
  rw [← reduce_discriminant p, ← map_mul, mul_comm Parameter.discriminantInverse,
    Parameter.discriminant_mul_inverse, map_one, reduce_discriminant, mul_comm,
    regularDelta_mul_inverse]

theorem reduce_surjective : Function.Surjective (reduce p) := by
  intro a
  have ha : ∃ b : S p, (reduce p b : WPPsi.K p) = (a : WPPsi.K p) := by
    refine Algebra.adjoin_induction (p := fun x _ => ∃ b : S p,
      (reduce p b : WPPsi.K p) = x) ?_ ?_ ?_ ?_ a.property
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨Parameter.u, by rw [reduce_u]; rfl⟩
      · exact ⟨Parameter.uInverse, by rw [reduce_uInverse]; rfl⟩
      · exact ⟨Parameter.discriminantInverse, by rw [reduce_discriminantInverse]; rfl⟩
    · intro x
      obtain ⟨b, hb⟩ := coefficientReduce_surjective p x
      exact ⟨algebraMap ℤ_[p] (S p) b, by rw [reduce_coefficient, hb]; rfl⟩
    · intro x y _ _ hx hy
      obtain ⟨b, hb⟩ := hx
      obtain ⟨d, hd⟩ := hy
      refine ⟨b+d, ?_⟩
      rw [map_add]
      exact congrArg₂ (· + ·) hb hd
    · intro x y _ _ hx hy
      obtain ⟨b, hb⟩ := hx
      obtain ⟨d, hd⟩ := hy
      refine ⟨b*d, ?_⟩
      rw [map_mul]
      exact congrArg₂ (· * ·) hb hd
  obtain ⟨b, hb⟩ := ha
  exact ⟨b, Subtype.ext hb⟩

theorem reduceKernel_eq : RingHom.ker (reduce p) = Ideal.span {(p : S p)} := by
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact reduce_kernel p a

def residueEquiv : S p ⧸ Ideal.span {(p : S p)} ≃+* WPGammaURegular.R p :=
  (Ideal.quotEquivOfEq (reduceKernel_eq p).symm).trans
    (RingHom.quotientKerEquivOfSurjective (reduce_surjective p))

end WPGammaIntegralLift
