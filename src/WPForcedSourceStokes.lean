import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

open Polynomial

namespace WPForcedSourceStokes

/-- Rational differentiation uses the actual reduced numerator and denominator. -/
noncomputable def rationalDerivative (f : RatFunc ℚ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ)
    (derivative f.num * f.denom - f.num * derivative f.denom) /
      (algebraMap ℚ[X] (RatFunc ℚ) f.denom) ^ 2

private theorem polynomial_fraction_derivative (P Q : ℚ[X]) (hQ : Q ≠ 0) :
    rationalDerivative (algebraMap ℚ[X] (RatFunc ℚ) P /
      algebraMap ℚ[X] (RatFunc ℚ) Q) =
      algebraMap ℚ[X] (RatFunc ℚ) (derivative P * Q - P * derivative Q) /
        (algebraMap ℚ[X] (RatFunc ℚ) Q) ^ 2 := by
  let f : RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ) P /
    algebraMap ℚ[X] (RatFunc ℚ) Q
  have hc : f.num * Q = P * f.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hQ).mpr rfl
  have hd := congrArg derivative hc
  simp only [derivative_mul] at hd
  have hc' := congrArg (algebraMap ℚ[X] (RatFunc ℚ)) hc
  have hd' := congrArg (algebraMap ℚ[X] (RatFunc ℚ)) hd
  simp only [map_mul] at hc'
  simp only [map_add, map_mul] at hd'
  change rationalDerivative f = _
  unfold rationalDerivative
  simp only [map_sub, map_mul]
  have hden : algebraMap ℚ[X] (RatFunc ℚ) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)
  have hq : algebraMap ℚ[X] (RatFunc ℚ) Q ≠ 0 := RatFunc.algebraMap_ne_zero hQ
  field_simp [hden, hq]
  linear_combination
    algebraMap ℚ[X] (RatFunc ℚ) f.denom * algebraMap ℚ[X] (RatFunc ℚ) Q * hd' -
      (algebraMap ℚ[X] (RatFunc ℚ) (derivative f.denom) * algebraMap ℚ[X] (RatFunc ℚ) Q +
        algebraMap ℚ[X] (RatFunc ℚ) f.denom *
          algebraMap ℚ[X] (RatFunc ℚ) (derivative Q)) * hc'


/-- Literal polynomial numerators of s14 primitive_row. -/
noncomputable def primitiveNumerator : Fin 6 → ℚ[X] :=
  ![-(221773650806250*X^8 - 1503132522131250*X^7 + 3723606976500000*X^6 - 2169455656771053*X^5 - 40956081646390479*X^4 + 103207329500259600*X^3 - 43747191704947500*X^2 + 10591244125000000*X - 2545812500000000),
    -(1856817188119125*X^8 - 12585094275029625*X^7 + 31176189825210000*X^6 - 77231074057061337*X^5 + 271088081060128209*X^4 - 662287068835761600*X^3 + 755580734652397500*X^2 - 213163861968750000*X - 10437831250000000),
    -2*(17428562927383950*X^11 - 118126926507824550*X^10 + 292627723225212000*X^9 - 772142970292880589*X^8 + 3319630016857857423*X^7 - 8112395820448285200*X^6 + 3295566944859026250*X^5 + 27903747231140625000*X^4 - 68640605627343750000*X^3 + 73688625527343750000*X^2 - 35895956250000000000*X + 6364531250000000000),
    -(1675028621928906*X^11 - 11352971770851474*X^10 + 28123937355843360*X^9 - 75389755821710031*X^8 + 330459542986715235*X^7 - 806217628510566000*X^6 + 415424800467337500*X^5 + 2194872802872525000*X^4 - 5480192337716250000*X^3 + 5892141846937500000*X^2 - 2871676500000000000*X + 509162500000000000),
    -(7906199343787782*X^11 - 53586462219006078*X^10 + 132746063056189920*X^9 - 349201112876671032*X^8 + 1517452083064009170*X^7 - 3703643019960507000*X^6 + 1740150277592146875*X^5 + 11315100845004496875*X^4 - 28161923474612812500*X^3 + 30197964014367187500*X^2 - 14717342062500000000*X + 2609457812500000000),
    -(12627573905140659*X^11 - 85586889801508911*X^10 + 212018524827053040*X^9 - 568012052156440284*X^8 + 2490691894429221540*X^7 - 6078803129564364000*X^6 + 2774200475601016875*X^5 + 18100041531561838125*X^4 - 44917249936655250000*X^3 + 49219104818657812500*X^2 - 24101474632812500000*X + 4264235937500000000)]

noncomputable def primitiveDenominator : Fin 6 → ℚ[X] :=
  ![(4422292875000*X*(99*X - 50)^2),
    (2211146437500*X*(99*X - 50)^2),
    (4975079484375*X^4*(99*X - 50)^2),
    (61420734375000*X*(99*X - 50)^2),
    (38387958984375*X*(99*X - 50)^2),
    (38387958984375*X*(99*X - 50)^2)]

/-- Literal polynomial numerators of s12 six_coordinate_source. -/
noncomputable def sourceNumerator : Fin 6 → ℚ[X] :=
  ![-(49911735537576000*X^10 - 358366114625568750*X^9 + 1024896781084880250*X^8 - 1504649505484526625*X^7 + 452996231267528739*X^6 - 967095462947044050*X^5 + 4568259094506607500*X^4 - 6390265799696625000*X^3 + 4776671745037500000*X^2 - 1620026581250000000*X + 203665000000000000),
    -(424991536633320525*X^10 - 3059269893497952675*X^9 + 8776295385209831250*X^8 - 17980716578328028350*X^7 + 40033847500084452231*X^6 - 72681314187914929575*X^5 + 72991314248116398750*X^4 - 42274489174403062500*X^3 + 20412363692634375000*X^2 - 6742838987500000000*X + 835026500000000000),
    -(16254637002555354315*X^13 - 117331289817565846140*X^12 + 337708827799074815355*X^11 - 712568763360020254725*X^10 + 1748175772637166704388*X^9 - 3284853027606881257275*X^8 + 3704502474256540713750*X^7 - 9155313050168474437500*X^6 + 35764645331938415625000*X^5 - 76328567295533437500000*X^4 + 86614239637406250000000*X^3 - 52943748309375000000000*X^2 + 16445948750000000000000*X - 2036650000000000000000),
    -(1985653292967065304*X^13 - 14368114735064950374*X^12 + 41475305233234945818*X^11 - 88343270723508495705*X^10 + 221167038990204750141*X^9 - 423533970403323140880*X^8 + 474160356450500328000*X^7 - 968138785177596900000*X^6 + 3581908522999976250000*X^5 - 7627707731215687500000*X^4 + 8660787001453125000000*X^3 - 5294374830937500000000*X^2 + 1644594875000000000000*X - 203665000000000000000),
    -(36543294297940253472*X^13 - 263435458016134499112*X^12 + 757044868395948363864*X^11 - 1569822791226846121485*X^10 + 3723903857070844049628*X^9 - 6706460023297782552765*X^8 + 7104436804434687747750*X^7 - 18032895993731205825000*X^6 + 72792768566568622500000*X^5 - 156236863530002062500000*X^4 + 177487785902109375000000*X^3 - 108534684034218750000000*X^2 + 33714194937500000000000*X - 4175132500000000000000),
    -(14697320943081344436*X^13 - 106064566372879052661*X^12 + 305192775314146313547*X^11 - 642442623371264688075*X^10 + 1566716945575890250404*X^9 - 2892773628120033493245*X^8 + 3118878132004496822625*X^7 - 7639960648920801665625*X^6 + 30095841001386345468750*X^5 - 64187382415999992187500*X^4 + 72733992740694140625000*X^3 - 44373556405664062500000*X^2 + 13773482078125000000000*X - 1705694375000000000000)]

noncomputable def sourceDenominator : Fin 6 → ℚ[X] :=
  ![(884458575000*X^2*(99*X - 50)^3),
    (442229287500*X^2*(99*X - 50)^3),
    (1990031793750*X^5*(99*X - 50)^3),
    (61420734375000*X^2*(99*X - 50)^3),
    (153551835937500*X^2*(99*X - 50)^3),
    (38387958984375*X^2*(99*X - 50)^3)]

noncomputable def symbol : RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ) X

noncomputable def lambda : RatFunc ℚ := (729 / 15625) * symbol ^ 3

noncomputable def primitiveEntry (i : Fin 6) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (primitiveNumerator i) /
    algebraMap ℚ[X] (RatFunc ℚ) (primitiveDenominator i)

noncomputable def sourceEntry (i : Fin 6) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (sourceNumerator i) /
    algebraMap ℚ[X] (RatFunc ℚ) (sourceDenominator i)

/-- The retained literal cyclic matrix, s10 cyclic_matrix. -/
noncomputable def cyclicMatrix : Fin 6 → Fin 6 → RatFunc ℚ :=
  ![![49456/125, 153648/125, 113472/125, 72/5, -3312/25, 113472/125],
    ![-1576/25, -4608/25, -3312/25, 0, 72/5, -3312/25],
    ![46/5, 108/5, 72/5, 0, 0, 72/5],
    ![-1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0]]

noncomputable def weightedRow (i : Fin 6) : RatFunc ℚ :=
  9 * cyclicMatrix 0 i + 126 * cyclicMatrix 1 i + 532 * cyclicMatrix 2 i

noncomputable def nextWeightedRow (i : Fin 6) : RatFunc ℚ :=
  9 * cyclicMatrix 1 i + 126 * cyclicMatrix 2 i + 532 * cyclicMatrix 3 i

/-- The literal six-coordinate connection, s10 six_coordinate_connection. -/
noncomputable def sixConnection : Fin 6 → Fin 6 → RatFunc ℚ :=
  ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0],
    ![-5*lambda/(72*(lambda-1)), -23*lambda/(36*(lambda-1)),
      -3*lambda/(2*(lambda-1)), 5*lambda/(72*(lambda-1)),
      23*lambda/(36*(lambda-1)), 3*lambda/(2*(lambda-1))],
    ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1],
    ![5/(72*(lambda-1)), 23/(36*(lambda-1)), 3/(2*(lambda-1)),
      -5*lambda/(72*(lambda-1)), -23*lambda/(36*(lambda-1)),
      -3*lambda/(2*(lambda-1))]]

private theorem escapePolynomial_ne_zero : (99 * X - 50 : ℚ[X]) ≠ 0 := by
  intro h
  have := congrArg (fun P : ℚ[X] => P.coeff 1) h
  norm_num at this

private theorem primitiveDenominator_ne_zero (i : Fin 6) :
    primitiveDenominator i ≠ 0 := by
  fin_cases i <;> simp [primitiveDenominator, escapePolynomial_ne_zero, X_ne_zero]

private theorem symbol_ne_zero : symbol ≠ 0 :=
  RatFunc.algebraMap_ne_zero X_ne_zero

@[simp] private theorem map_polynomial_numeral (n : ℕ) :
    algebraMap ℚ[X] (RatFunc ℚ) (n : ℚ[X]) = (n : RatFunc ℚ) :=
  map_natCast _ _

private theorem escape_ne_zero : (99 * symbol - 50 : RatFunc ℚ) ≠ 0 := by
  have h := RatFunc.algebraMap_ne_zero escapePolynomial_ne_zero
  simpa [symbol, _root_.map_ofNat] using h

private theorem lambda_sub_one_ne_zero : lambda - 1 ≠ 0 := by
  have hP : (C (729 / 15625) * X^3 - 1 : ℚ[X]) ≠ 0 := by
    intro h
    have := congrArg (fun P : ℚ[X] => P.coeff 0) h
    norm_num at this
  have h := RatFunc.algebraMap_ne_zero hP
  simpa [lambda, symbol, RatFunc.algebraMap_C] using h

set_option maxHeartbeats 2000000 in
/-- All six entries of the fixed outer primitive identity, with no source premise. -/
theorem outer_row_identity (i : Fin 6) :
    weightedRow i + 6 * nextWeightedRow i = 3375 * sourceEntry i +
      6750 * ((1-symbol) * rationalDerivative (primitiveEntry i) +
        (3*(1-symbol)/symbol) *
          (∑ j : Fin 6, primitiveEntry j * sixConnection j i) - primitiveEntry i / 2) := by
  have hscaled : (-15625 + (RatFunc.X : RatFunc ℚ)^3 * 729) ≠ 0 := by
    intro h
    apply lambda_sub_one_ne_zero
    dsimp [lambda, symbol]
    linear_combination h / 15625
  have hfactor : (-(RatFunc.X^2 * 125000) + RatFunc.X^3 * 742500 -
      RatFunc.X^4 * 1470150 + RatFunc.X^5 * 970299 : RatFunc ℚ) =
      symbol^2 * (99*symbol-50)^3 := by dsimp [symbol]; ring
  have hfactor5 : (-(RatFunc.X^5 * 125000) + RatFunc.X^6 * 742500 -
      RatFunc.X^7 * 1470150 + RatFunc.X^8 * 970299 : RatFunc ℚ) =
      symbol^5 * (99*symbol-50)^3 := by dsimp [symbol]; ring
  rw [primitiveEntry, polynomial_fraction_derivative _ _ (primitiveDenominator_ne_zero i)]
  fin_cases i <;> simp [weightedRow, nextWeightedRow, cyclicMatrix, sourceEntry, sourceNumerator,
    sourceDenominator, primitiveEntry, primitiveNumerator, primitiveDenominator,
    sixConnection, Fin.sum_univ_succ, derivative_mul, derivative_pow, symbol,
    lambda, _root_.map_ofNat]
  all_goals field_simp [show algebraMap ℚ[X] (RatFunc ℚ) X ≠ 0 from symbol_ne_zero,
    show 99 * algebraMap ℚ[X] (RatFunc ℚ) X - 50 ≠ 0 from escape_ne_zero,
    show 729 / 15625 * (algebraMap ℚ[X] (RatFunc ℚ) X)^3 - 1 ≠ 0 from
      lambda_sub_one_ne_zero]
  all_goals
    ring_nf
    simp only [hfactor, hfactor5, mul_inv_rev, ← inv_pow]
    field_simp [hscaled, symbol_ne_zero, escape_ne_zero]
    dsimp [symbol]
    ring

end WPForcedSourceStokes
