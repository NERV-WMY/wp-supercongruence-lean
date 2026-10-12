import WPMomentPrecision.BasePole.Baselines

open WPPIntegralReduction

namespace WPMomentPrecision.BasePole

theorem fermatQ_integral (p a : ℕ) [Fact p.Prime] :
    0 ≤ padicValRat p (fermatQ p a) := by
  unfold fermatQ
  rw [padicValRat.of_int]
  exact Int.natCast_nonneg _

theorem fermatUnit_inverse_integral (p a : ℕ) [Fact p.Prime]
    (ha : 0 < a) (hap : a < p) : 0 ≤ padicValRat p (fermatUnit p a)⁻¹ := by
  have hd : ¬p ∣ a := Nat.not_dvd_of_pos_of_lt ha hap
  unfold fermatUnit
  rw [padicValRat.inv, padicValRat.pow, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd hd]
  simp

theorem fermatUnit_ne_zero (p a : ℕ) (ha : 0 < a) : fermatUnit p a ≠ 0 := by
  unfold fermatUnit
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))

theorem naturalPower_eq_unit (p a : ℕ) (hp : 1 ≤ p) :
    (a : ℚ)^p = (a : ℚ)*fermatUnit p a := by
  unfold fermatUnit
  rw [← pow_succ', Nat.sub_add_cancel hp]

theorem power125_eq_unit (p : ℕ) (hp : 1 ≤ p) :
    (125 : ℚ)^p = 125*(fermatUnit p 5)^3 := by
  have hf : (125 : ℚ)^p = ((5 : ℚ)^p)^3 := by
    rw [show (125 : ℚ)=(5 : ℚ)^3 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    omega
  have hfive : (5 : ℚ)^p = 5*fermatUnit p 5 := by
    simpa only [Nat.cast_ofNat] using naturalPower_eq_unit p 5 hp
  rw [hf, hfive, mul_pow]
  norm_num

theorem baseTaylorRemainder_integral (p : ℕ) [Fact p.Prime] (t : ℚ)
    (ht : 0 ≤ padicValRat p t) : 0 ≤ padicValRat p (baseTaylorRemainder t) := by
  let tt : integralRationals p := ⟨t, ht⟩
  exact (79932 + 205760*tt + 254208*tt^2 + 214400*tt^3 +
    122880*tt^4 + 46080*tt^5 + 10240*tt^6 + 1024*tt^7).property

theorem endpointTaylorRemainder_integral (p : ℕ) [Fact p.Prime] (t : ℚ)
    (ht : 0 ≤ padicValRat p t) : 0 ≤ padicValRat p (endpointTaylorRemainder t) := by
  let tt : integralRationals p := ⟨t, ht⟩
  exact (33903 + 116800*tt + 210320*tt^2 + 256128*tt^3 +
    214720*tt^4 + 122880*tt^5 + 46080*tt^6 + 10240*tt^7 + 1024*tt^8).property

def baseUnitTarget (P q r : ℚ) : ℚ :=
  (24/625)*(1 + P*((32/3)*q-3*r) +
    P^2*((97/2)*q^2-32*q*r+6*r^2))

/-- The exact third-order remainder uses only integral unit inverses and denominators 3 and 5. -/
def baseUnitRemainder (P q r ui vi : ℚ) : ℚ :=
  (1/3)^2*(1/5)^3 *
    ((216*(1/5)*r^3 + 2304*(1/5)*P*q*r^3 + 10476*(1/5)*P^2*q^2*r^3) *
        (-(10+15*(P*r)+6*(P*r)^2)*vi^3) +
      6*2304*(1/5)*q*r^2 - 3*10476*(1/5)*q^2*r +
      6*10476*(1/5)*P*q^2*r^2 +
      q^3*(baseTaylorRemainder (P*q)*(1/3)*(1/5)*ui)*vi^3)

theorem normalized_base_exact_taylor (P q r : ℚ)
    (hu : 1+P*q ≠ 0) (hv : 1+P*r ≠ 0) :
    baseBaseline (2*(1+P*q)) / (1125*(1+P*r)^3) =
      baseUnitTarget P q r + P^3 *
        baseUnitRemainder P q r (1+P*q)⁻¹ (1+P*r)⁻¹ := by
  rw [show baseBaseline (2*(1+P*q)) / (1125*(1+P*r)^3) =
      (1/1125)*baseBaseline (2*(1+P*q))*((1+P*r)⁻¹)^3 by
        simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]; ring]
  rw [baseBaseline_exact_taylor (P*q) hu,
    inverse_cube_exact_taylor (P*r) hv]
  unfold baseUnitTarget baseUnitRemainder
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  field_simp [hu, hv]
  ring

theorem baseUnitRemainder_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P q r ui vi : ℚ) (hP : 0 ≤ padicValRat p P) (hq : 0 ≤ padicValRat p q)
    (hr : 0 ≤ padicValRat p r) (hui : 0 ≤ padicValRat p ui)
    (hvi : 0 ≤ padicValRat p vi) :
    0 ≤ padicValRat p (baseUnitRemainder P q r ui vi) := by
  let R := integralRationals p
  let PP : R := ⟨P, hP⟩
  let qq : R := ⟨q, hq⟩
  let rr : R := ⟨r, hr⟩
  let uu : R := ⟨ui, hui⟩
  let vv : R := ⟨vi, hvi⟩
  let c3 : R := ⟨1/3, WPFiniteConductorPolynomial.small_inverse_integral p 3
    (by omega) (by omega)⟩
  let c5 : R := ⟨1/5, WPFiniteConductorPolynomial.small_inverse_integral p 5
    (by omega) (by omega)⟩
  let A : R := ⟨baseTaylorRemainder (P*q),
    baseTaylorRemainder_integral p _ (R.mul_mem hP hq)⟩
  exact (c3^2*c5^3 *
    ((216*c5*rr^3 + 2304*c5*PP*qq*rr^3 + 10476*c5*PP^2*qq^2*rr^3) *
        (-(10+15*(PP*rr)+6*(PP*rr)^2)*vv^3) +
      6*2304*c5*qq*rr^2 - 3*10476*c5*qq^2*rr +
      6*10476*c5*PP*qq^2*rr^2 + qq^3*(A*c3*c5*uu)*vv^3)).property

def endpointUnitTarget (P q r : ℚ) : ℚ :=
  (1044+P*(10476*q-3132*r))/625

/-- The original endpoint baseline has an exact integral second-order remainder. -/
def endpointUnitRemainder (P q r ui vi : ℚ) : ℚ :=
  (1044*(1/5)^4*r^2+10476*(1/5)^4*P*q*r^2) *
      (6-(P*r)*(10+15*(P*r)+6*(P*r)^2)*vi^3) -
    3*10476*(1/5)^4*q*r +
    4*q^2*endpointTaylorRemainder (P*q)*(1/3)*(1/5)^4*ui*vi^3

theorem normalized_endpoint_exact_taylor (P q r : ℚ)
    (hu : 1+P*q ≠ 0) (hv : 1+P*r ≠ 0) :
    (16/125)*(1+P*q)^2*endpointBaseline (2*(1+P*q))*((1+P*r)⁻¹)^3 =
      endpointUnitTarget P q r + P^2 *
        endpointUnitRemainder P q r (1+P*q)⁻¹ (1+P*r)⁻¹ := by
  rw [endpointBaseline_exact_taylor (P*q) hu,
    inverse_cube_exact_taylor (P*r) hv]
  unfold endpointUnitTarget endpointUnitRemainder
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  field_simp [hu, hv]
  ring

theorem endpointUnitRemainder_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P q r ui vi : ℚ) (hP : 0 ≤ padicValRat p P) (hq : 0 ≤ padicValRat p q)
    (hr : 0 ≤ padicValRat p r) (hui : 0 ≤ padicValRat p ui)
    (hvi : 0 ≤ padicValRat p vi) :
    0 ≤ padicValRat p (endpointUnitRemainder P q r ui vi) := by
  let R := integralRationals p
  let PP : R := ⟨P, hP⟩
  let qq : R := ⟨q, hq⟩
  let rr : R := ⟨r, hr⟩
  let uu : R := ⟨ui, hui⟩
  let vv : R := ⟨vi, hvi⟩
  let c3 : R := ⟨1/3, WPFiniteConductorPolynomial.small_inverse_integral p 3
    (by omega) (by omega)⟩
  let c5 : R := ⟨1/5, WPFiniteConductorPolynomial.small_inverse_integral p 5
    (by omega) (by omega)⟩
  let A : R := ⟨endpointTaylorRemainder (P*q),
    endpointTaylorRemainder_integral p _ (R.mul_mem hP hq)⟩
  exact ((1044*c5^4*rr^2+10476*c5^4*PP*qq*rr^2) *
      (6-(PP*rr)*(10+15*(PP*rr)+6*(PP*rr)^2)*vv^3) -
    3*10476*c5^4*qq*rr + 4*qq^2*A*c3*c5^4*uu*vv^3).property

noncomputable def actualBaseUnitRemainder (p : ℕ) : ℚ :=
  baseUnitRemainder p (fermatQ p 2) (fermatQ p 5)
    (fermatUnit p 2)⁻¹ (fermatUnit p 5)⁻¹

noncomputable def actualEndpointUnitRemainder (p : ℕ) : ℚ :=
  endpointUnitRemainder p (fermatQ p 2) (fermatQ p 5)
    (fermatUnit p 2)⁻¹ (fermatUnit p 5)⁻¹

theorem actualBaseUnitRemainder_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualBaseUnitRemainder p) :=
  baseUnitRemainder_integral p hp _ _ _ _ _ (by
    change (p : ℚ) ∈ integralRationals p
    exact natCast_mem (integralRationals p) p)
    (fermatQ_integral p 2) (fermatQ_integral p 5)
    (fermatUnit_inverse_integral p 2 (by omega) (by omega))
    (fermatUnit_inverse_integral p 5 (by omega) (by omega))

theorem actualEndpointUnitRemainder_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualEndpointUnitRemainder p) :=
  endpointUnitRemainder_integral p hp _ _ _ _ _ (by
    change (p : ℚ) ∈ integralRationals p
    exact natCast_mem (integralRationals p) p)
    (fermatQ_integral p 2) (fermatQ_integral p 5)
    (fermatUnit_inverse_integral p 2 (by omega) (by omega))
    (fermatUnit_inverse_integral p 5 (by omega) (by omega))

theorem actual_baseBaseline_exact_taylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    baseBaseline ((2 : ℚ)^p)/(9*(125 : ℚ)^p) =
      baseUnitTarget p (fermatQ p 2) (fermatQ p 5) +
        (p : ℚ)^3*actualBaseUnitRemainder p := by
  have h2 := WPFiniteInversion.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h5 := WPFiniteInversion.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have hu2 := fermatUnit_eq p 2 (by simpa using h2)
  have hu5 := fermatUnit_eq p 5 (by simpa using h5)
  have h := normalized_base_exact_taylor (p : ℚ) (fermatQ p 2) (fermatQ p 5)
    (by rw [← hu2]; exact fermatUnit_ne_zero p 2 (by omega))
    (by rw [← hu5]; exact fermatUnit_ne_zero p 5 (by omega))
  rw [← hu2, ← hu5] at h
  have htwo : (2 : ℚ)^p = 2*fermatUnit p 2 := by
    simpa only [Nat.cast_ofNat] using naturalPower_eq_unit p 2 (by omega)
  rw [htwo, power125_eq_unit p (by omega)]
  change _ = baseUnitTarget p (fermatQ p 2) (fermatQ p 5) +
    (p : ℚ)^3*baseUnitRemainder p (fermatQ p 2) (fermatQ p 5)
      (fermatUnit p 2)⁻¹ (fermatUnit p 5)⁻¹
  convert h using 1
  congr 1
  ring

theorem actual_endpointBaseline_exact_taylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    16*(fermatUnit p 2)^2*endpointBaseline ((2 : ℚ)^p)/(125 : ℚ)^p =
      endpointUnitTarget p (fermatQ p 2) (fermatQ p 5) +
        (p : ℚ)^2*actualEndpointUnitRemainder p := by
  have h2 := WPFiniteInversion.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h5 := WPFiniteInversion.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have hu2 := fermatUnit_eq p 2 (by simpa using h2)
  have hu5 := fermatUnit_eq p 5 (by simpa using h5)
  have h := normalized_endpoint_exact_taylor (p : ℚ) (fermatQ p 2) (fermatQ p 5)
    (by rw [← hu2]; exact fermatUnit_ne_zero p 2 (by omega))
    (by rw [← hu5]; exact fermatUnit_ne_zero p 5 (by omega))
  rw [← hu2, ← hu5] at h
  have htwo : (2 : ℚ)^p = 2*fermatUnit p 2 := by
    simpa only [Nat.cast_ofNat] using naturalPower_eq_unit p 2 (by omega)
  rw [htwo, power125_eq_unit p (by omega)]
  change _ = endpointUnitTarget p (fermatQ p 2) (fermatQ p 5) +
    (p : ℚ)^2*endpointUnitRemainder p (fermatQ p 2) (fermatQ p 5)
      (fermatUnit p 2)⁻¹ (fermatUnit p 5)⁻¹
  convert h using 1
  have hu0 := fermatUnit_ne_zero p 5 (by omega)
  field_simp [hu0]

theorem actual_endpointUnit_exact_taylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    1+(fermatUnit p 2)⁻¹ = 2-(p : ℚ)*fermatQ p 2 +
      (p : ℚ)^2*((fermatQ p 2)^2*(fermatUnit p 2)⁻¹) := by
  have h2 := WPFiniteInversion.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hu2 := fermatUnit_eq p 2 (by simpa using h2)
  have h := inverse_first_exact_taylor ((p : ℚ)*fermatQ p 2)
    (by rw [← hu2]; exact fermatUnit_ne_zero p 2 (by omega))
  rw [← hu2] at h
  calc
    1+(fermatUnit p 2)⁻¹ =
        1+(1-(p : ℚ)*fermatQ p 2+((p : ℚ)*fermatQ p 2)^2/fermatUnit p 2) :=
      congrArg (fun x : ℚ => 1+x) h
    _ = 2-(p : ℚ)*fermatQ p 2+
        (p : ℚ)^2*((fermatQ p 2)^2*(fermatUnit p 2)⁻¹) := by
      simp only [div_eq_mul_inv]
      ring

theorem actual_endpointUnit_remainder_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p ((fermatQ p 2)^2*(fermatUnit p 2)⁻¹) :=
  (integralRationals p).mul_mem
    ((integralRationals p).pow_mem (fermatQ_integral p 2) 2)
    (fermatUnit_inverse_integral p 2 (by omega) (by omega))

def actualBeta (p : ℕ) : ℚ := 15*fermatQ p 3+15*fermatQ p 5-64*fermatQ p 2

theorem actualBeta_integral (p : ℕ) [Fact p.Prime] :
    0 ≤ padicValRat p (actualBeta p) := by
  let R := integralRationals p
  let q (a : ℕ) : R := ⟨fermatQ p a, fermatQ_integral p a⟩
  exact (15*q 3+15*q 5-64*q 2).property

theorem actualBeta_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualBeta p : ZMod p) = WPFiniteInversion.ell p 16 := by
  let R := integralRationals p
  let q (a : ℕ) : R := ⟨fermatQ p a, fermatQ_integral p a⟩
  change residueHom p (15*q 3+15*q 5-64*q 2)=WPFiniteInversion.ell p 16
  simp only [map_sub, map_add, map_mul, map_ofNat]
  have hq (a : ℕ) : residueHom p (q a) =
      (WPFiniteInversion.integerFermatQuotient p (a : ℤ) : ZMod p) := by
    change ((fermatQ p a : ℚ) : ZMod p)=_
    rw [fermatQ, Rat.cast_intCast]
  simp only [hq]
  exact (actual_beta_fermat p hp).symm

end WPMomentPrecision.BasePole
