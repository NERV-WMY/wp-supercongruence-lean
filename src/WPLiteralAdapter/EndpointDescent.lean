import WPLiteralAdapter.OriginGamma
import WPFullConductorPrecision
import WPLaurent.Nonresonance

open WPForcedSourceStokes WPFiniteConductorPolynomial Polynomial

namespace WPLiteralAdapter

noncomputable section

/-- Six exact nonresonant divisions recover the extended endpoint from its beta coefficients. -/
theorem six_step_polynomial_endpoint (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (P : ℚ[X]) (hdegree : P.natDegree ≤ 3*p+5)
    (hbeta : ∀ j : ℕ, j≤5 → precisionZero p 6
      ((((3*p+j : ℕ) : ℚ)+1)*P.coeff (3*p+j+1) -
        (((3*p+j : ℕ) : ℚ)+1/2)*P.coeff (3*p+j))) :
    precisionZero p 6 (P.coeff (3*p)) := by
  let R := integralSubring p
  have hstep (j : ℕ) (hj : j≤5)
      (hnext : precisionZero p 6 (P.coeff (3*p+(j+1)))) :
      precisionZero p 6 (P.coeff (3*p+j)) := by
    let n := 3*p+j
    have hu := WPLaurent.nonresonant_denominator_unit p
      (2*(n : ℤ)+1) 6 (2*(j : ℤ)+1) (by dsimp [n]; ring)
      (by omega) (by omega)
    have hd : (2*(n : ℚ)+1)⁻¹ ∈ R := by
      change 0≤padicValRat p ((2*(n : ℚ)+1)⁻¹)
      rw [padicValRat.inv]
      have huq : padicValRat p (2*(n : ℚ)+1)=0 := by
        simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one,
          Int.cast_natCast] using hu
      rw [huq]
      norm_num
    have hb : precisionZero p 6 (((n : ℚ)+1)*P.coeff (n+1)-
        ((n : ℚ)+1/2)*P.coeff n) := hbeta j hj
    have hn : precisionZero p 6 (P.coeff (n+1)) := by
      simpa only [n, Nat.add_assoc] using hnext
    have ha : precisionZero p 6 (P.coeff (n+1)*(2*((n : ℚ)+1))) :=
      precisionZero_mul_integral p 6 _ _ hn
        (R.mul_mem (natCast_mem R 2) (R.add_mem (natCast_mem R n) R.one_mem))
    have hb2 := precisionZero_mul_integral p 6 _ _ hb
      (R.neg_mem (natCast_mem R 2))
    have hs := precisionZero_add p 6 _ _ ha hb2
    have hf := precisionZero_mul_integral p 6 _ _ hs hd
    have hd0 : 2*(n : ℚ)+1≠0 := by positivity
    convert hf using 1
    field_simp [hd0]
    ring
  have h6 : precisionZero p 6 (P.coeff (3*p+6)) :=
    Or.inl (coeff_eq_zero_of_natDegree_lt (by omega))
  have h5 := hstep 5 (by omega) h6
  have h4 := hstep 4 (by omega) h5
  have h3 := hstep 3 (by omega) h4
  have h2 := hstep 2 (by omega) h3
  have h1 := hstep 1 (by omega) h2
  simpa only [Nat.add_zero] using hstep 0 (by omega) h1

end

end WPLiteralAdapter
