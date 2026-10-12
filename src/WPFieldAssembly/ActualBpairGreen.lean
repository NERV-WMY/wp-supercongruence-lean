import WPFieldAssembly.ActualBpairFiniteKernel
import WPFieldAssembly.ActualEtaTransport
import WPFieldAssembly.ActualSimplePoleResidue

set_option maxHeartbeats 1600000

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource
  WPFieldAssembly.GreenLaurentOperators WPFiniteLaurentDifferential
  WPActualNativeCanonicalPart WPActualCanonicalFinitePart WPCartierPoleProjection
namespace WPFieldAssembly.ActualBpairContraction
open WPFieldAssembly.ActualGreenResidue WPFieldAssembly.ActualThreePhase
open WPFieldAssembly.ActualSimplePoleResidue

theorem phi_self (p : ℕ) [Fact p.Prime] :
    ActualThreePhase.φ (K := ZMod p) p = RingHom.id (ZMod p) := by
  exact Subsingleton.elim _ _

theorem coefficientMap_self (p : ℕ) (U : (ZMod p)[T;T⁻¹]) :
    WPActualChiSource.coefficientMap (RingHom.id (ZMod p)) U = U := by
  ext j
  rw [WPActualChiSource.coefficientMap_coeff]
  rfl

theorem actual_remainder_green_source (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (u : ZMod p) (hu : u ^ 2 = 1 / 5) :
    D (nativeRemainder p hp) =
      D (ActualGreenResidue.greenPrimitive (K := ZMod p) p u) +
      weightedDD (WPFiniteZSource.P p u) +
      LaurentPolynomial.C (ActualGreenResidue.hK (K := ZMod p) p -
        (WPActualEtaPrimitive.actualResidue p ((p-1)/2) (p-1-p/6) 0 : ZMod p)) * T (-1) -
      LaurentPolynomial.C (1 / 6 : ZMod p) *
        D (pullbackPolynomial p (nativeHJet p)).toLaurent := by
  have hχ := ActualGreenResidue.actual_chi_finite_P (K := ZMod p) p hp u hu
  rw [ActualThreePhase.χK, phi_self, coefficientMap_self] at hχ
  have hχ' : NativeChiFieldSource.halfChiField p hp =
      ActualGreenResidue.candidateChi (K := ZMod p) p hp u := by
    simpa only [ActualGreenResidue.candidateChi] using hχ
  have hH : ActualGreenResidue.HpullK (K := ZMod p) p =
      ActualGreenResidue.Hpull p := by
    rw [ActualGreenResidue.HpullK, phi_self, Polynomial.map_id]
  have hPeta : WPActualFieldPrimitive.literalFieldPeta p hp =
      D (ActualGreenResidue.greenPrimitive (K := ZMod p) p u) +
      weightedDD (WPFiniteZSource.P p u) +
      LaurentPolynomial.C (ActualGreenResidue.hK (K := ZMod p) p) * T (-1) := by
    rw [ActualGreenResidue.literal_Peta_transport p hp, hχ', ← hH,
      ActualGreenResidue.actual_candidate_eta_formula p hp u]
  have hR := actual_native_remainder_source p hp
  change D (nativeRemainder p hp) =
    WPActualFieldPrimitive.literalFieldPeta p hp -
      LaurentPolynomial.C (WPActualEtaPrimitive.actualResidue p
        ((p-1)/2) (p-1-p/6) 0 : ZMod p) * T (-1) -
      LaurentPolynomial.C (1 / 6 : ZMod p) *
        D (pullbackPolynomial p (nativeHJet p)).toLaurent at hR
  rw [hR, hPeta, map_sub]
  ring

theorem actual_bpair_green_source (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (u : ZMod p) (hu : u ^ 2 = 1 / 5) :
    NativeScalarRows.nativeBpair p hp =
      (bKernel p * D (ActualGreenResidue.greenPrimitive (K := ZMod p) p u)).coeff (-1) +
      (bKernel p * weightedDD (WPFiniteZSource.P p u)).coeff (-1) -
      (1 / 6 : ZMod p) *
        (bKernel p * D (pullbackPolynomial p (nativeHJet p)).toLaurent).coeff (-1) := by
  let c : ZMod p := ActualGreenResidue.hK (K := ZMod p) p -
    (WPActualEtaPrimitive.actualResidue p ((p-1)/2) (p-1-p/6) 0 : ZMod p)
  have hz : (bKernel p * (LaurentPolynomial.C c * T (-1))).coeff (-1) = 0 := by
    have he : bKernel p * (LaurentPolynomial.C c * T (-1)) =
        LaurentPolynomial.C c * T (-1) * bKernel p := by ring
    rw [he, shift_coeff, show (-1 : ℤ) - -1 = 0 by norm_num,
      bKernel_zero, mul_zero]
  rw [actual_bpair_IR53 p hp, actual_remainder_green_source p hp u hu]
  change (bKernel p *
    (D (ActualGreenResidue.greenPrimitive (K := ZMod p) p u) +
      weightedDD (WPFiniteZSource.P p u) + LaurentPolynomial.C c * T (-1) -
      LaurentPolynomial.C (1 / 6 : ZMod p) *
        D (pullbackPolynomial p (nativeHJet p)).toLaurent)).coeff (-1) = _
  have hc : bKernel p * (LaurentPolynomial.C (1 / 6 : ZMod p) *
      D (pullbackPolynomial p (nativeHJet p)).toLaurent) =
    LaurentPolynomial.C (1 / 6 : ZMod p) *
      (bKernel p * D (pullbackPolynomial p (nativeHJet p)).toLaurent) := by ring
  rw [mul_sub, mul_add, mul_add, hc, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hz, C_mul_coeff, add_zero]
end WPFieldAssembly.ActualBpairContraction



namespace WPFieldAssembly.ActualBpairContraction
variable {K : Type*} [Field K]
noncomputable def nativeRK (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) : K[T;T⁻¹] :=
  coefficientMap (ActualThreePhase.φ (K := K) p) (nativeRemainder p hp)
noncomputable def bKernelK (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  coefficientMap (ActualThreePhase.φ (K := K) p) (bKernel p)
noncomputable def HJetPullK (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  coefficientMap (ActualThreePhase.φ (K := K) p)
    (pullbackPolynomial p (nativeHJet p)).toLaurent

/-- Both characteristic-p branches use the same whole original finite kernel. -/
theorem bKernelK_eq_literalKB (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    bKernelK (K:=K) p=literalKB (K:=K) p := by
  rw [bKernelK,←literalKB_eq_bKernel p hp,coefficientMap_literalKB]

theorem D_coefficientMap {L : Type*} [Field L] (f : K →+* L) (U : K[T;T⁻¹]) :
    coefficientMap f (D U) = D (coefficientMap f U) := by
  ext j
  rw [coefficientMap_coeff, D_coeff, D_coeff, coefficientMap_coeff, map_mul, map_intCast]

theorem actual_bpair_IR53_K (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    ActualThreePhase.φ (K := K) p (NativeScalarRows.nativeBpair p hp) =
      (bKernelK (K := K) p * D (nativeRK (K := K) p hp)).coeff (-1) := by
  have h := congrArg (ActualThreePhase.φ (K := K) p) (actual_bpair_IR53 p hp)
  rw [← coefficientMap_coeff, map_mul, D_coefficientMap] at h
  exact h

theorem actual_literal_Peta_K (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    coefficientMap (ActualThreePhase.φ (K := K) p)
        (WPActualFieldPrimitive.literalFieldPeta p hp) =
      GreenLaurentOperators.eta (ActualThreePhase.χK (K := K) p hp)
        (ActualGreenResidue.HpullK (K := K) p).toLaurent := by
  have h := congrArg (coefficientMap (ActualThreePhase.φ (K := K) p))
    (ActualGreenResidue.literal_Peta_transport p hp)
  simp only [GreenLaurentOperators.eta, weightedDD, map_sub, map_add, map_mul,
    coefficientMap_C, coefficientMap_T, DD_map, map_div₀, map_one, map_ofNat,
    coefficientMap_toLaurent] at h
  simpa only [GreenLaurentOperators.eta, weightedDD, ActualThreePhase.χK,
    ActualGreenResidue.HpullK, map_add, map_ofNat] using h

theorem actual_remainder_green_source_K (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    D (nativeRK (K := K) p hp) =
      D (ActualGreenResidue.greenPrimitive (K := K) p u) +
      weightedDD (WPFiniteZSource.P p u) +
      LaurentPolynomial.C (ActualGreenResidue.hK (K := K) p -
        ActualThreePhase.φ (K := K) p
          (WPActualEtaPrimitive.actualResidue p ((p-1)/2) (p-1-p/6) 0 : ZMod p)) * T (-1) -
      LaurentPolynomial.C (1 / 6 : K) * D (HJetPullK (K := K) p) := by
  have hχ : ActualThreePhase.χK (K := K) p hp =
      ActualGreenResidue.candidateChi (K := K) p hp u := by
    simpa only [ActualGreenResidue.candidateChi] using
      (ActualGreenResidue.actual_chi_finite_P (K := K) p hp u hu)
  have hP := actual_literal_Peta_K (K := K) p hp
  rw [hχ, ActualGreenResidue.actual_candidate_eta_formula p hp u] at hP
  have hR := congrArg (coefficientMap (ActualThreePhase.φ (K := K) p))
    (actual_native_remainder_source p hp)
  change coefficientMap (ActualThreePhase.φ (K := K) p) (D (nativeRemainder p hp)) =
    coefficientMap (ActualThreePhase.φ (K := K) p)
      (WPActualFieldPrimitive.literalFieldPeta p hp -
        LaurentPolynomial.C (WPActualEtaPrimitive.actualResidue p
          ((p-1)/2) (p-1-p/6) 0 : ZMod p) * T (-1) -
        LaurentPolynomial.C (1 / 6 : ZMod p) *
          D (pullbackPolynomial p (nativeHJet p)).toLaurent) at hR
  simp only [map_sub, map_mul, coefficientMap_C, coefficientMap_T,
    D_coefficientMap, map_div₀, map_one, map_ofNat] at hR
  rw [hP] at hR
  change D (nativeRK (K := K) p hp) = _ at hR
  rw [hR, map_sub]
  dsimp only [HJetPullK]
  ring

end WPFieldAssembly.ActualBpairContraction

namespace WPFieldAssembly.ActualBpairContraction
variable {K : Type*} [Field K]

open WPFieldAssembly.ActualSimplePoleResidue

theorem actual_bpair_green_source_K (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    ActualThreePhase.φ (K := K) p (NativeScalarRows.nativeBpair p hp) =
      (bKernelK (K := K) p *
        D (ActualGreenResidue.greenPrimitive (K := K) p u)).coeff (-1) +
      (bKernelK (K := K) p * weightedDD (WPFiniteZSource.P p u)).coeff (-1) -
      (1 / 6 : K) * (bKernelK (K := K) p * D (HJetPullK (K := K) p)).coeff (-1) := by
  let c : K := ActualGreenResidue.hK (K := K) p -
    ActualThreePhase.φ (K := K) p
      (WPActualEtaPrimitive.actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0 : ZMod p)
  have hk0 : (bKernelK (K := K) p).coeff 0 = 0 := by
    rw [bKernelK, coefficientMap_coeff, bKernel_zero, map_zero]
  have hz : (bKernelK (K := K) p * (LaurentPolynomial.C c * T (-1))).coeff (-1) = 0 := by
    rw [show bKernelK (K := K) p * (LaurentPolynomial.C c * T (-1)) =
      LaurentPolynomial.C c * T (-1) * bKernelK (K := K) p by ring,
      shift_coeff, show (-1 : ℤ) - -1 = 0 by norm_num, hk0, mul_zero]
  rw [actual_bpair_IR53_K p hp, actual_remainder_green_source_K p hp u hu]
  change (bKernelK (K := K) p *
    (D (ActualGreenResidue.greenPrimitive (K := K) p u) +
      weightedDD (WPFiniteZSource.P p u) + LaurentPolynomial.C c * T (-1) -
      LaurentPolynomial.C (1 / 6 : K) * D (HJetPullK (K := K) p))).coeff (-1) = _
  rw [mul_sub, mul_add, mul_add,
    show bKernelK (K := K) p * (LaurentPolynomial.C (1 / 6 : K) *
      D (HJetPullK (K := K) p)) = LaurentPolynomial.C (1 / 6 : K) *
        (bKernelK (K := K) p * D (HJetPullK (K := K) p)) by ring,
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hz, C_mul_coeff, add_zero]

/-- The whole original K_B carries the actual Green, period and low-H source together. -/
theorem actual_bpair_green_literal_source_K (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    ActualThreePhase.φ (K:=K) p (NativeScalarRows.nativeBpair p hp)=
      (literalKB (K:=K) p *
        D (ActualGreenResidue.greenPrimitive (K:=K) p u)).coeff (-1)+
      (literalKB (K:=K) p * weightedDD (WPFiniteZSource.P p u)).coeff (-1)-
      (1/6 : K)*(literalKB (K:=K) p * D (HJetPullK (K:=K) p)).coeff (-1) := by
  simpa only [bKernelK_eq_literalKB p hp] using
    actual_bpair_green_source_K (K:=K) p hp u hu

/-- Clearing the actual divided difference retains both endpoint correction terms. -/
theorem weightedDD_origin (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p)
    (h4 : (4 : K)≠0) (F P : K[T;T⁻¹]) :
    (F*weightedDD P).coeff (-1)=
      originPole (F*(P*(33-12*T 1)+
        8*(T 1-4)*LaurentPolynomial.C (ev (1/4) (one_div_ne_zero h4) P)+
        4*(T 1-LaurentPolynomial.C (1/4 : K))*
          LaurentPolynomial.C (ev 4 h4 P))) := by
  have hs := congrArg (fun U : K[T;T⁻¹] => F*U) (weightedDD_cleared h4 P)
  have he : (WPFiniteZSource.Abar : K[X]).toLaurent*(F*weightedDD P)=
      F*(P*(33-12*T 1)+
        8*(T 1-4)*LaurentPolynomial.C (ev (1/4) (one_div_ne_zero h4) P)+
        4*(T 1-LaurentPolynomial.C (1/4 : K))*
          LaurentPolynomial.C (ev 4 h4 P)) := by
    linear_combination hs
  rw [←he,originPole_cleared p hp]

/-- The actual Bpair has its original uncontracted Green identity at the origin. -/
theorem actual_bpair_green_origin_source_K (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) (h4 : (4 : K)≠0) :
    ActualThreePhase.φ (K:=K) p (NativeScalarRows.nativeBpair p hp)=
      -(ActualGreenResidue.greenPrimitive (K:=K) p u *
        D (literalKB (K:=K) p)).coeff (-1)+
      originPole (literalKB (K:=K) p *
        (WPFiniteZSource.P p u*(33-12*T 1)+
          8*(T 1-4)*LaurentPolynomial.C
            (ev (1/4) (one_div_ne_zero h4) (WPFiniteZSource.P p u))+
          4*(T 1-LaurentPolynomial.C (1/4 : K))*LaurentPolynomial.C
            (ev 4 h4 (WPFiniteZSource.P p u))))-
      (1/6 : K)*(literalKB (K:=K) p * D (HJetPullK (K:=K) p)).coeff (-1) := by
  have hz : (D (literalKB (K:=K) p *
      ActualGreenResidue.greenPrimitive (K:=K) p u)).coeff (-1)=0 := by
    rw [D_coeff]
    norm_num
  rw [D_mul,AddMonoidAlgebra.coeff_add,Finsupp.add_apply] at hz
  have hibp : (literalKB (K:=K) p *
      D (ActualGreenResidue.greenPrimitive (K:=K) p u)).coeff (-1)=
      -(ActualGreenResidue.greenPrimitive (K:=K) p u *
        D (literalKB (K:=K) p)).coeff (-1) := by
    have hz' : (ActualGreenResidue.greenPrimitive (K:=K) p u *
        D (literalKB (K:=K) p)).coeff (-1)+
        (literalKB (K:=K) p *
          D (ActualGreenResidue.greenPrimitive (K:=K) p u)).coeff (-1)=0 := by
      simpa only [mul_comm] using hz
    linear_combination hz'
  rw [actual_bpair_green_literal_source_K p hp u hu,hibp,
    weightedDD_origin p hp h4]

end WPFieldAssembly.ActualBpairContraction
