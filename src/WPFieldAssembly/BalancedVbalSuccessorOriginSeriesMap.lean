import WPFieldAssembly.SourceClosureTraceOrigin
import WPFieldAssembly.ActualBpairLowHLocalPole
import Mathlib.RingTheory.PowerSeries.WellKnown

open scoped Polynomial PowerSeries LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries WPActualChiSource

namespace WPFieldAssembly.BalancedVbalSuccessorOriginSeriesTransport

open ActualBpairLowHLocalPole SourceClosureTraceOrigin

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

private theorem geometric_series_unit (a : K) :
    (PowerSeries.mk fun n => a^n)*(1-PowerSeries.C a*PowerSeries.X)=1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp only [mul_sub,mul_one,←mul_assoc,map_sub,
        PowerSeries.coeff_mk,pow_zero,PowerSeries.coeff_zero_mul_X,
        PowerSeries.coeff_zero_one,sub_zero]
  | succ n =>
      simp only [mul_sub,mul_one,←mul_assoc,map_sub,
        PowerSeries.coeff_succ_mul_X,PowerSeries.coeff_mul_C,
        PowerSeries.coeff_mk,pow_succ,PowerSeries.coeff_one,
        Nat.succ_ne_zero,if_false,sub_self]

/-- The literal reciprocal equals both complete geometric series before any slot is selected. -/
theorem actual_fieldReciprocal_geometric_product (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) :
    LaurentPoleField.fieldReciprocal p=
      (PowerSeries.mk fun n => (4 : ZMod p)^n)*
        (PowerSeries.mk fun n => (1/4 : ZMod p)^n) := by
  let G := (PowerSeries.mk fun n => (4 : ZMod p)^n)
  let J := (PowerSeries.mk fun n => (1/4 : ZMod p)^n)
  let B := (1-PowerSeries.C (4 : ZMod p)*PowerSeries.X)
  let C := (1-PowerSeries.C (1/4 : ZMod p)*PowerSeries.X)
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hG : G*B=1 := geometric_series_unit _
  have hJ : J*C=1 := geometric_series_unit _
  have hr : LaurentPoleField.fieldReciprocal p=
      PowerSeries.C (16/15 : ZMod p)*G-PowerSeries.C (1/15 : ZMod p)*J := by
    apply PowerSeries.ext
    intro n
    simp only [LaurentPoleField.fieldReciprocal,G,J,map_sub,
      PowerSeries.coeff_mk,PowerSeries.coeff_C_mul,pow_succ]
    field_simp [h4,h15]; ring
  have hc : (16/15 : ZMod p)-(1/15 : ZMod p)=1 := by
    field_simp [h15]; ring
  have hx : (16/15 : ZMod p)*(1/4 : ZMod p)-(1/15 : ZMod p)*4=0 := by
    field_simp [h4,h15]; ring
  have hc' := congrArg (PowerSeries.C : ZMod p → (ZMod p)⟦X⟧) hc
  have hx' := congrArg (PowerSeries.C : ZMod p → (ZMod p)⟦X⟧) hx
  simp only [map_sub,map_mul,map_one,map_zero,map_ofNat] at hc' hx'
  have hlin : PowerSeries.C (16/15 : ZMod p)*C-
      PowerSeries.C (1/15 : ZMod p)*B=1 := by
    dsimp only [B,C]
    simp only [map_ofNat]
    linear_combination hc'-PowerSeries.X*hx'
  have hR : LaurentPoleField.fieldReciprocal p*(B*C)=1 := by
    rw [hr]
    linear_combination PowerSeries.C (16/15 : ZMod p)*C*hG-
      PowerSeries.C (1/15 : ZMod p)*B*hJ+hlin
  have hprod : (G*J)*(B*C)=1 := by
    calc
      _=(G*B)*(J*C) := by ring
      _=1 := by rw [hG,hJ,mul_one]
  have hBC : B*C≠0 := by
    intro hz
    rw [hz,mul_zero] at hprod
    exact zero_ne_one hprod
  apply mul_right_cancel₀ hBC
  exact hR.trans hprod.symm

/-- The same literal reciprocal is the full inverse of the normalized Abar product. -/
theorem actual_fieldReciprocal_normalized_unit (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) :
    LaurentPoleField.fieldReciprocal p*
      (1-PowerSeries.C (4 : ZMod p)*PowerSeries.X)*
        (1-PowerSeries.C (1/4 : ZMod p)*PowerSeries.X)=1 := by
  rw [actual_fieldReciprocal_geometric_product p hp]
  have h4 := geometric_series_unit (4 : ZMod p)
  have hq := geometric_series_unit (1/4 : ZMod p)
  calc
    _=((PowerSeries.mk fun n => (4 : ZMod p)^n)*
        (1-PowerSeries.C (4 : ZMod p)*PowerSeries.X))*
      ((PowerSeries.mk fun n => (1/4 : ZMod p)^n)*
        (1-PowerSeries.C (1/4 : ZMod p)*PowerSeries.X)) := by ring
    _=1 := by rw [h4,hq,mul_one]

private theorem actual_Abar_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent≠0 := by
  intro hz
  apply WPFiniteZSource.Abar_nonzero (K:=K) p hp
  ext j
  exact congrArg (fun Q : LaurentSeries K => Q.coeff j)
    (hz.trans (map_zero localFiniteSeriesHom).symm)

/-- Every pole order retains the complete mapped reciprocal power, including p-multiple slots. -/
theorem actual_Abar_inverse_power_map (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (m : ℕ) (f : ZMod p →+* K) :
    (localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent^m)⁻¹=
      algebraMap K (LaurentSeries K) (f ((-1/4 : ZMod p)^m))*
        ((PowerSeries.map f (LaurentPoleField.fieldReciprocal p^m) : K⟦X⟧) : LaurentSeries K) := by
  let A := localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent
  let x := localFiniteSeriesHom (T 1 : K[T;T⁻¹])
  let R : LaurentSeries K := (PowerSeries.map f (LaurentPoleField.fieldReciprocal p) : K⟦X⟧)
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hq : (4 : LaurentSeries K)*HahnSeries.C (1/4 : K)=1 := by
    have he := congrArg (algebraMap K (LaurentSeries K)) (mul_one_div_cancel h4)
    simpa only [map_mul,map_one,map_ofNat,LaurentSeries.algebraMap_apply] using he
  have hA : A=HahnSeries.C (-4 : K)*
      (1-HahnSeries.C (4 : K)*x)*(1-HahnSeries.C (1/4 : K)*x) := by
    dsimp only [A,x]
    simp only [WPFiniteZSource.Abar,map_mul,map_sub,map_neg,map_ofNat,
      map_one,Polynomial.toLaurent_X,localFiniteSeries_T]
    linear_combination (4*(HahnSeries.single 1 (1 : K))^2-
      HahnSeries.single 1 (1 : K))*hq
  have hu := congrArg
    (fun Q : (ZMod p)⟦X⟧ => ((PowerSeries.map f Q : K⟦X⟧) : LaurentSeries K))
    (actual_fieldReciprocal_normalized_unit p hp)
  simp only [map_mul,map_sub,map_one,PowerSeries.map_C,PowerSeries.map_X] at hu
  simp only [PowerSeries.coe_C,PowerSeries.coe_X] at hu
  have hf4 : f (4 : ZMod p)=(4 : K) := by simp only [map_ofNat]
  have hfq : f (1/4 : ZMod p)=(1/4 : K) := by
    simp only [map_div₀,map_one,map_ofNat]
  rw [hf4,hfq] at hu
  change R*(1-HahnSeries.C (4 : K)*x)*
    (1-HahnSeries.C (1/4 : K)*x)=1 at hu
  have hc : HahnSeries.C (-1/4 : K)*HahnSeries.C (-4 : K)=
      (1 : LaurentSeries K) := by
    have he := congrArg (algebraMap K (LaurentSeries K))
      (show (-1/4 : K)*(-4 : K)=1 by field_simp [h4])
    simpa only [map_mul,map_one,LaurentSeries.algebraMap_apply] using he
  have hU : (HahnSeries.C (-1/4 : K)*R)*A=1 := by
    rw [hA]
    calc
      _=(HahnSeries.C (-1/4 : K)*HahnSeries.C (-4 : K))*
        (R*(1-HahnSeries.C (4 : K)*x)*(1-HahnSeries.C (1/4 : K)*x)) := by ring
      _=1 := by rw [hc,hu,mul_one]
  have ha : A≠0 := actual_Abar_series_ne_zero (K:=K) p hp
  have hi : A⁻¹=HahnSeries.C (-1/4 : K)*R := by
    apply mul_right_cancel₀ ha
    rw [inv_mul_cancel₀ ha,hU]
  have hscalar : (HahnSeries.C (-1/4 : K) : LaurentSeries K)^m=
      algebraMap K (LaurentSeries K) (f ((-1/4 : ZMod p)^m)) := by
    simp only [map_pow,map_div₀,map_neg,map_one,map_ofNat]
  have hR : R^m=
      ((PowerSeries.map f (LaurentPoleField.fieldReciprocal p^m) : K⟦X⟧) : LaurentSeries K) := by
    simp only [R,map_pow]
  change (A^m)⁻¹=_
  rw [←inv_pow,hi,mul_pow,hscalar,hR]

private theorem mapped_integer_powerSeries_coefficient (p : ℕ) [Fact p.Prime]
    (f : ZMod p →+* K) (Q : (ZMod p)⟦X⟧) (n : ℤ) :
    ((PowerSeries.map f Q : K⟦X⟧) : LaurentSeries K).coeff n=
      f (LaurentPoleField.fieldZcoeff p n Q) := by
  cases n with
  | ofNat n => simp [PowerSeries.coeff_coe,LaurentPoleField.fieldZcoeff]
  | negSucc n => simp [PowerSeries.coeff_coe,LaurentPoleField.fieldZcoeff]

/-- Every signed monomial is shifted by exactly -n-1 in the entire mapped reciprocal power. -/
theorem actual_originTrace_series_map_monomial (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (m : ℕ) (f : ZMod p →+* K) (c : ZMod p) (n : ℤ) :
    f (originTrace p m (LaurentPolynomial.C c*T n))=
      (localFiniteSeriesHom (coefficientMap f (LaurentPolynomial.C c*T n))/
        localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent^m).coeff (-1) := by
  rw [originTrace_monomial,originWeight,map_mul,map_mul]
  rw [coefficientMap_monomial,map_mul,localFiniteSeries_C,localFiniteSeries_T]
  simp only [div_eq_mul_inv]
  rw [actual_Abar_inverse_power_map p hp m f]
  simp only [LaurentSeries.algebraMap_apply,HahnSeries.C_apply,
    HahnSeries.single_mul_single,zero_add,mul_one,HahnSeries.coeff_single_mul,sub_zero]
  rw [show (-1 : ℤ)-n=-n-1 by ring,
    mapped_integer_powerSeries_coefficient p f (LaurentPoleField.fieldReciprocal p^m)]
  simp only [div_eq_mul_inv]

/-- The SAME original originTrace equals the complete local-series quotient at every pole order.
All finite Laurent sources and all signed exponents are included; no support restriction is imposed. -/
theorem actual_originTrace_series_map (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (m : ℕ) (f : ZMod p →+* K) (F : (ZMod p)[T;T⁻¹]) :
    f (originTrace p m F)=
      (localFiniteSeriesHom (coefficientMap f F)/
        localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent^m).coeff (-1) := by
  induction F using LaurentPolynomial.induction_on' with
  | add F G hF hG =>
      rw [map_add,map_add,map_add,map_add,add_div,HahnSeries.coeff_add,hF,hG]
  | C_mul_T n c => exact actual_originTrace_series_map_monomial p hp m f c n

end WPFieldAssembly.BalancedVbalSuccessorOriginSeriesTransport
