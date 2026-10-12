import WPReview.ResidueClosedCanonicalBounds
import WPResidueQuotient.ActualCompletion
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.CharP.Lemmas

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators
open WPResidueQuotient

def exponentPower (p : ℕ) : Exponents →+ Exponents where
  toFun x := p • x
  map_zero' := nsmul_zero p
  map_add' x y := nsmul_add x y p

def laurentPhi (R : Type*) [CommRing R] (p : ℕ) :
    WPResidueQuotient.LaurentPolynomial R →+* WPResidueQuotient.LaurentPolynomial R :=
  AddMonoidAlgebra.mapDomainRingHom R (exponentPower p)

theorem laurentPhi_single (R : Type*) [CommRing R] (p : ℕ) (x : Exponents) (r : R) :
    laurentPhi R p (AddMonoidAlgebra.single x r) = AddMonoidAlgebra.single (p • x) r := by
  simp [laurentPhi, exponentPower]

theorem laurentPhi_scalar (R : Type*) [CommRing R] (p : ℕ) (r : R) :
    laurentPhi R p (algebraMap R (WPResidueQuotient.LaurentPolynomial R) r) =
      algebraMap R (WPResidueQuotient.LaurentPolynomial R) r := by
  change laurentPhi R p (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 r
  rw [laurentPhi_single, nsmul_zero]

theorem laurentPhi_smul (R : Type*) [CommRing R] (p : ℕ) (r : R)
    (P : WPResidueQuotient.LaurentPolynomial R) : laurentPhi R p (r • P) = r • laurentPhi R p P := by
  simp only [Algebra.smul_def, map_mul, laurentPhi_scalar]

theorem laurentPhi_vertex (R : Type*) [CommRing R] (p : ℕ) (i : Fin 6) :
    laurentPhi R p (laurentVertex (R := R) i) = laurentVertex (R := R) i ^ p := by
  rw [laurentVertex, laurentPhi_single]
  simp

theorem laurentPhi_logarithmic (R : Type*) [CommRing R] (p : ℕ)
    (w : Exponents →+ ℤ) (P : WPResidueQuotient.LaurentPolynomial R) :
    logarithmicDerivation w (laurentPhi R p P) =
      (p : R) • laurentPhi R p (logarithmicDerivation w P) := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ, smul_add]
  | single x r =>
    rw [laurentPhi_single, logarithmicDerivation_single,
      logarithmicDerivation_single, laurentPhi_single]
    rw [map_nsmul]
    simp [nsmul_eq_mul, AddMonoidAlgebra.smul_single, mul_assoc]

theorem degree_nsmul_le (p : ℕ) (x : Exponents) :
    canonicalDegreeNat (p • x) ≤ p * canonicalDegreeNat x := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [succ_nsmul, Nat.succ_mul]
    exact (canonicalDegreeNat_add_le _ _).trans (Nat.add_le_add_right ih _)

theorem laurentPhi_supported (R : Type*) [CommRing R] (p m : ℕ)
    (P : WPResidueQuotient.LaurentPolynomial R) (hP : P ∈ numeratorFiltration R m) :
    laurentPhi R p P ∈ numeratorFiltration R (p*m) := by
  classical
  have he : P = ∑ x ∈ P.coeff.support, AddMonoidAlgebra.single x (P.coeff x) := by
    simpa only [Finsupp.sum] using (AddMonoidAlgebra.sum_coeff_single P).symm
  rw [he, map_sum]
  apply (numeratorFiltration R (p*m)).sum_mem
  intro x hx
  rw [laurentPhi_single]
  exact single_mem_numeratorFiltration (p • x) _ _
    ((degree_nsmul_le p x).trans (Nat.mul_le_mul_left p ((mem_numeratorFiltration m P).mp hP x hx)))

variable (p : ℕ) [Fact p.Prime]

def coefficientReduction : WPResidueQuotient.LaurentPolynomial ℤ_[p] →+* WPResidueQuotient.LaurentPolynomial (ZMod p) :=
  Specialization.laurentMap (WPGammaIntegralLift.coefficientReduce p)

theorem coefficientReduction_kernel (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) :
    coefficientReduction p P = 0 ↔ ∃ Q, P = (p : ℤ_[p]) • Q := by
  classical
  constructor
  · intro h
    have hc (x : Exponents) : WPGammaIntegralLift.coefficientReduce p (P.coeff x) = 0 := by
      have he := congrArg (fun T : WPResidueQuotient.LaurentPolynomial (ZMod p) => T.coeff x) h
      simpa only [coefficientReduction, Specialization.laurentMap_coefficient,
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using he
    choose b hb using fun x => (WPGammaIntegralLift.coefficientReduce_kernel p (P.coeff x)).mp (hc x)
    refine ⟨∑ x ∈ P.coeff.support, AddMonoidAlgebra.single x (b x), ?_⟩
    rw [Finset.smul_sum]
    calc
      P = ∑ x ∈ P.coeff.support, AddMonoidAlgebra.single x (P.coeff x) := by
        simpa only [Finsupp.sum] using (AddMonoidAlgebra.sum_coeff_single P).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        rw [AddMonoidAlgebra.smul_single, hb]
        rfl
  · rintro ⟨Q, rfl⟩
    rw [coefficientReduction, Specialization.laurentMap_smul]
    simp [WPGammaIntegralLift.coefficientReduce]

theorem reduction_laurentPhi (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) :
    coefficientReduction p (laurentPhi ℤ_[p] p P) = coefficientReduction p P ^ p := by
  let : CharP (WPResidueQuotient.LaurentPolynomial (ZMod p)) p :=
    CharP.of_ringHom_of_ne_zero (algebraMap (ZMod p)
      (WPResidueQuotient.LaurentPolynomial (ZMod p))) p (Fact.out : p.Prime).ne_zero
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp [(Fact.out : p.Prime).ne_zero]
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, map_add, add_pow_char]
  | single x r =>
    rw [laurentPhi_single]
    simp only [coefficientReduction, Specialization.laurentMap_single]
    simp

def frobeniusDifference (hp : 7 ≤ p) : WPResidueQuotient.LaurentPolynomial ℤ_[p] :=
  laurentPhi ℤ_[p] p (torusPolynomial (Parameter.integralTenth p hp)) -
    torusPolynomial (Parameter.integralTenth p hp) ^ p

theorem frobeniusDifference_reduction (hp : 7 ≤ p) :
    coefficientReduction p (frobeniusDifference p hp) = 0 := by
  rw [frobeniusDifference, map_sub, reduction_laurentPhi, map_pow, sub_self]

def G (hp : 7 ≤ p) : WPResidueQuotient.LaurentPolynomial ℤ_[p] :=
  Classical.choose ((coefficientReduction_kernel p _).mp (frobeniusDifference_reduction p hp))

theorem G_integral_identity (hp : 7 ≤ p) :
    frobeniusDifference p hp = (p : ℤ_[p]) • G p hp :=
  Classical.choose_spec ((coefficientReduction_kernel p _).mp (frobeniusDifference_reduction p hp))

theorem frobeniusDifference_supported (hp : 7 ≤ p) :
    frobeniusDifference p hp ∈ numeratorFiltration ℤ_[p] p := by
  apply (numeratorFiltration ℤ_[p] p).sub_mem
  · simpa only [Nat.mul_one] using laurentPhi_supported ℤ_[p] p 1
      (torusPolynomial (Parameter.integralTenth p hp))
      (torusPolynomial_mem_numeratorFiltration _)
  · exact torusPolynomial_pow_mem_numeratorFiltration _ p

theorem G_supported (hp : 7 ≤ p) : G p hp ∈ numeratorFiltration ℤ_[p] p := by
  classical
  rw [mem_numeratorFiltration]
  intro x hx
  have hn : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hg := congrArg (fun P : WPResidueQuotient.LaurentPolynomial ℤ_[p] => P.coeff x)
    (G_integral_identity p hp)
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] at hg
  have hd : x ∈ (frobeniusDifference p hp).coeff.support := by
    rw [Finsupp.mem_support_iff, hg]
    exact mul_ne_zero hn (Finsupp.mem_support_iff.mp hx)
  exact (mem_numeratorFiltration p _).mp (frobeniusDifference_supported p hp) x hd

theorem G_logarithmic (hp : 7 ≤ p) (w : Exponents →+ ℤ) :
    logarithmicDerivation w (G p hp) =
      laurentPhi ℤ_[p] p (logarithmicDerivation w (torusPolynomial (Parameter.integralTenth p hp))) -
      torusPolynomial (Parameter.integralTenth p hp) ^ (p-1) *
        logarithmicDerivation w (torusPolynomial (Parameter.integralTenth p hp)) := by
  have hn : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hd := congrArg (logarithmicDerivation (R := ℤ_[p]) w) (G_integral_identity p hp)
  rw [frobeniusDifference, map_sub, laurentPhi_logarithmic,
    Derivation.leibniz_pow, Derivation.map_smul] at hd
  have he : (p : ℤ_[p]) • logarithmicDerivation w (G p hp) =
      (p : ℤ_[p]) • (laurentPhi ℤ_[p] p
        (logarithmicDerivation w (torusPolynomial (Parameter.integralTenth p hp))) -
      torusPolynomial (Parameter.integralTenth p hp) ^ (p-1) *
        logarithmicDerivation w (torusPolynomial (Parameter.integralTenth p hp))) := by
    rw [smul_sub, ← hd]
    simp [Algebra.smul_def]
  ext x
  have hc := congrArg (fun P : WPResidueQuotient.LaurentPolynomial ℤ_[p] => P.coeff x) he
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] at hc
  exact mul_left_cancel₀ hn hc

theorem laurentPhi_f (hp : 7 ≤ p) :
    laurentPhi ℤ_[p] p (torusPolynomial (Parameter.integralTenth p hp)) =
      torusPolynomial (Parameter.integralTenth p hp)^p + (p : ℤ_[p]) • G p hp := by
  simpa only [frobeniusDifference, add_comm] using
    (sub_eq_iff_eq_add.mp (G_integral_identity p hp))

end WPResidueFrobenius
