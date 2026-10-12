import WPToricRho.Connection
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Matrix.Basic

noncomputable section

namespace WPToricState

open Polynomial Module

def relation (p : ℕ) : Polynomial (ZMod p) := X ^ 3

abbrev TruncRing (p : ℕ) := AdjoinRoot (relation p)

def base (p : ℕ) : ZMod p →+* TruncRing p := AdjoinRoot.of (relation p)

def rho (p : ℕ) : TruncRing p := AdjoinRoot.root (relation p)

theorem relation_monic (p : ℕ) : (relation p).Monic := monic_X.pow 3

theorem rho_third_zero (p : ℕ) : rho p ^ 3 = 0 := by
  have he := AdjoinRoot.eval₂_root (relation p)
  change (X ^ 3 : Polynomial (ZMod p)).eval₂ (base p) (rho p) = 0 at he
  rw [eval₂_pow, eval₂_X] at he
  exact he

variable (p : ℕ) [Fact p.Prime]

theorem actual_denominator_unit (n : ℕ) (hn : n < p) :
    IsUnit (WPToricRho.denominator (rho p) n) :=
  WPToricRho.denominator_unit Fact.out (base p) (rho p) (rho_third_zero p) n hn

theorem actual_zero_endpoint :
    (WPToricRho.residual (base p) (rho p)).coeff 0 = 0 :=
  WPToricRho.residual_coeff_zero Fact.out (base p) (rho p) (rho_third_zero p)

theorem actual_terminal_endpoint :
    (WPToricRho.residual (base p) (rho p)).coeff p = 0 :=
  WPToricRho.residual_coeff_terminal Fact.out (base p) (rho p) (rho_third_zero p)

theorem actual_finite_rho_equation (hp7 : 7 ≤ p) :
    WPRho.rhoPower (rho p) 3 (WPToricRho.finiteH (base p) (rho p)) -
      X * WPToricRho.threeShift (base p) (rho p) (WPToricRho.finiteH (base p) (rho p)) = 0 :=
  WPToricRho.finite_rho_connection_equation Fact.out hp7 (base p) (rho p) (rho_third_zero p)

theorem relation_degree : (relation p).natDegree = 3 := by simp [relation]

def rhoBasis : Basis (Fin 3) (ZMod p) (TruncRing p) :=
  (AdjoinRoot.powerBasis' (relation_monic p)).basis.reindex (finCongr (relation_degree p))

theorem rhoBasis_pow (i : Fin 3) : rhoBasis p i = rho p ^ i.val := by
  unfold rhoBasis
  rw [Basis.reindex_apply]
  exact (AdjoinRoot.powerBasis' (relation_monic p)).basis_eq_pow _

def rhoCoord (j : Fin 3) : TruncRing p →ₗ[ZMod p] ZMod p := (rhoBasis p).coord j

theorem rhoCoord_power (i j : Fin 3) :
    rhoCoord p j (rho p ^ i.val) = if i = j then 1 else 0 := by
  rw [← rhoBasis_pow p i]
  exact (rhoBasis p).repr_self_apply i j

def jordan (i j : Fin 3) : ZMod p := if i.val + 1 = j.val then 1 else 0

theorem rhoCoord_next_power (i j : Fin 3) :
    rhoCoord p j (rho p ^ (i.val + 1)) = jordan p i j := by
  by_cases hi : i.val < 2
  · have hpow := rhoCoord_power p (⟨i.val + 1, by omega⟩ : Fin 3) j
    simpa [jordan, Fin.ext_iff] using hpow
  · have hi2 : i.val = 2 := by omega
    simp [hi2, rho_third_zero, jordan]
    omega

theorem rhoCoord_mul (a : TruncRing p) (j : Fin 3) :
    rhoCoord p j (rho p * a) =
      ∑ i : Fin 3, rhoCoord p i a * jordan p i j := by
  have he := (rhoBasis p).sum_repr a
  calc
    rhoCoord p j (rho p * a) =
      rhoCoord p j (rho p * ∑ i : Fin 3, (rhoBasis p).repr a i • rhoBasis p i) := by rw [he]
    _ = ∑ i : Fin 3, (rhoBasis p).repr a i * rhoCoord p j (rho p * rhoBasis p i) := by
      simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [rhoBasis_pow, ← pow_succ', rhoCoord_next_power]
      rfl

def coordPoly (j : Fin 3) (P : Polynomial (TruncRing p)) : Polynomial (ZMod p) :=
  P.sum (fun n a => monomial n (rhoCoord p j a))

theorem coeff_coordPoly (j : Fin 3) (P : Polynomial (TruncRing p)) (n : ℕ) :
    (coordPoly p j P).coeff n = rhoCoord p j (P.coeff n) := by
  classical
  simp only [coordPoly, Polynomial.sum_def, finsetSum_coeff, coeff_monomial]
  by_cases hn : n ∈ P.support
  · simp [Finset.sum_ite_eq', hn]
  · have hz : P.coeff n = 0 := by simpa only [mem_support_iff, not_not] using hn
    simp [Finset.sum_ite_eq', hn, hz]

theorem coordPoly_add (j : Fin 3) (P Q : Polynomial (TruncRing p)) :
    coordPoly p j (P + Q) = coordPoly p j P + coordPoly p j Q := by
  ext n
  simp [coeff_coordPoly, coeff_add]

theorem coordPoly_sub (j : Fin 3) (P Q : Polynomial (TruncRing p)) :
    coordPoly p j (P - Q) = coordPoly p j P - coordPoly p j Q := by
  ext n
  simp [coeff_coordPoly, coeff_sub]

theorem coordPoly_X_mul (j : Fin 3) (P : Polynomial (TruncRing p)) :
    coordPoly p j (X * P) = X * coordPoly p j P := by
  ext n
  cases n <;> simp [coeff_coordPoly, coeff_X_mul]

theorem rhoCoord_base_mul (j : Fin 3) (c : ZMod p) (a : TruncRing p) :
    rhoCoord p j (base p c * a) = c * rhoCoord p j a := by
  rw [show base p c = algebraMap (ZMod p) (TruncRing p) c by rfl,
    ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem coordPoly_base_C_mul (j : Fin 3) (c : ZMod p) (P : Polynomial (TruncRing p)) :
    coordPoly p j (C (base p c) * P) = C c * coordPoly p j P := by
  ext n
  simp [coeff_coordPoly, coeff_C_mul, rhoCoord_base_mul]

theorem coordPoly_theta (j : Fin 3) (P : Polynomial (TruncRing p)) :
    coordPoly p j (WPRho.theta P) = WPRho.theta (coordPoly p j P) := by
  ext n
  rw [coeff_coordPoly, WPRho.coeff_theta, WPRho.coeff_theta, coeff_coordPoly]
  have hc : (n : TruncRing p) = base p (n : ZMod p) := by simp
  rw [hc, rhoCoord_base_mul]

theorem coordPoly_rho_C_mul (j : Fin 3) (P : Polynomial (TruncRing p)) :
    coordPoly p j (C (rho p) * P) =
      ∑ i : Fin 3, C (jordan p i j) * coordPoly p i P := by
  ext n
  simp only [coeff_coordPoly, coeff_C_mul, rhoCoord_mul, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

end WPToricState

