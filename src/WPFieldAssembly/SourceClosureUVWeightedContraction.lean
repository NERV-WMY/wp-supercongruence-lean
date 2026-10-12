import WPFieldAssembly.SourceClosureUVWeightedLog
import WPFieldAssembly.ActualUVSourceIdentification

open scoped LaurentPolynomial Polynomial
open LaurentPolynomial WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.SourceClosureUniversalLog
  WPFieldAssembly.SourceClosureUVPhaseTrace
  WPFieldAssembly.SourceClosureUVWeightedLog

namespace WPFieldAssembly.SourceClosureUVWeightedContraction

/- These contractions use the entire original logarithmic carriers.
   The log and dilog inversion signs are deliberately different. -/

theorem weighted_log_prefactor (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (c z : ZMod p) :
    originalWeightedFieldTrace p ((T (-(p : ℤ))-LaurentPolynomial.C z)*scaledLog p c)=
      -3*z*(2*WPFiniteField.ell p (4*c)+WPFiniteField.ell p (c/4)) := by
  rw [sub_mul, weighted_sub, weighted_shift_scaledLog p hp, weighted_C_mul,
    weighted_scaledLog p hp]
  ring

theorem weighted_dilog_prefactor (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (c z : ZMod p) :
    originalWeightedFieldTrace p ((T (-(p : ℤ))-LaurentPolynomial.C z)*scaledDilog p c)=
      -3*z*(2*WPFiniteField.R p (4*c)+WPFiniteField.R p (c/4)) := by
  rw [sub_mul, weighted_sub, weighted_shift_scaledDilog p hp, weighted_C_mul,
    weighted_scaledDilog p hp]
  ring

theorem original_real_log_ends (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    WPFiniteField.ell p (1 : ZMod p)=0 ∧
      WPFiniteField.ell p (1/16 : ZMod p)=
        -(WPFiniteField.ell p (16 : ZMod p))/16 := by
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h16 : (16 : ZMod p)≠0 := by
    rw [show (16 : ZMod p)=4*4 by ring]
    exact mul_ne_zero h4 h4
  constructor
  · exact WPFiniteInversion.ell_one_eq_zero p (by omega)
  · have h := WPFiniteField.ell_inversion p (16 : ZMod p) h16
    rw [ZMod.pow_card] at h
    rw [one_div, h]
    ring

theorem original_real_dilog_ends (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    WPFiniteField.R p (1 : ZMod p)=0 ∧
      WPFiniteField.R p (1/16 : ZMod p)=
        WPFiniteField.R p (16 : ZMod p)/16 := by
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h16 : (16 : ZMod p)≠0 := by
    rw [show (16 : ZMod p)=4*4 by ring]
    exact mul_ne_zero h4 h4
  constructor
  · exact WPFiniteInversion.R_one_eq_zero p (by omega)
  · have h := WPFiniteField.R_inversion p (16 : ZMod p) h16
    rw [ZMod.pow_card] at h
    rw [one_div, h]
    ring

/-- UW18b's whole Ja+Jb contribution, with both reflected cutoff bands retained. -/
theorem original_Jab_weight (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    originalWeightedFieldTrace p (originalJa p+originalJb p)=
      -3*WPFiniteField.ell p (16 : ZMod p)/(2*WPFiniteABSourceTail.epsilon p) := by
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h16 : (16 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 16
    (Finset.mem_Ico.mpr (by omega))
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p)≠0 :=
    pow_ne_zero _ (WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega)))
  have hl := original_real_log_ends p hp
  have hJa : originalJa p =
      LaurentPolynomial.C (2/WPFiniteABSourceTail.epsilon p : ZMod p)*
        ((T (-(p : ℤ))-LaurentPolynomial.C (1/4 : ZMod p))*scaledLog p 4) := by
    rw [originalJa, mul_assoc]
  have hJb : originalJb p =
      LaurentPolynomial.C (2/WPFiniteABSourceTail.epsilon p : ZMod p)*
        ((T (-(p : ℤ))-LaurentPolynomial.C (4 : ZMod p))*scaledLog p (1/4)) := by
    rw [originalJb, mul_assoc]
  rw [hJa, hJb, weighted_add, weighted_C_mul, weighted_C_mul,
    weighted_log_prefactor p hp, weighted_log_prefactor p hp,
    show (4 : ZMod p)*4=16 by ring,
    show (4 : ZMod p)/4=1 by field_simp [h4],
    show (4 : ZMod p)*(1/4)=1 by field_simp [h4],
    show (1/4 : ZMod p)/4=1/16 by rw [div_div]; congr 1; ring,
    hl.1, hl.2]
  field_simp [h2, h4, h16, heps]
  ring

/-- The same whole dilogarithm has the positive finite inversion sign. -/
theorem original_J2_weight (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    originalWeightedFieldTrace p (originalJ2log p)=
      -(WPFiniteField.R p (16 : ZMod p))/10 := by
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h16 : (16 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 16
    (Finset.mem_Ico.mpr (by omega))
  have hd := original_real_dilog_ends p hp
  rw [originalJ2log, weighted_C_mul, weighted_sub,
    weighted_dilog_prefactor p hp, weighted_dilog_prefactor p hp,
    show (4 : ZMod p)*4=16 by ring,
    show (4 : ZMod p)/4=1 by field_simp [h4],
    show (4 : ZMod p)*(1/4)=1 by field_simp [h4],
    show (1/4 : ZMod p)/4=1/16 by rw [div_div]; congr 1; ring,
    hd.1, hd.2]
  field_simp [h2, h3, h4, h5, h10, h15, h16]
  ring

end WPFieldAssembly.SourceClosureUVWeightedContraction
