import WPActualConductorRows

open scoped BigOperators
open Polynomial

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def firstConductorMean : RatFunc ℚ :=
  (27/1000)*symbol*(80-99*symbol+27*symbol^2)

def firstConductorMeanDerivative : RatFunc ℚ :=
  (27/1000)*(80-198*symbol+81*symbol^2)

def firstConductorEll : RatFunc ℚ := (27/1000)*symbol*(9*symbol-16)

def firstConductorEllDerivative : RatFunc ℚ := (27/1000)*(18*symbol-16)

def firstConductorLP : RatFunc ℚ :=
  1953125*(9*symbol-25)*(81*symbol^2-198*symbol+80)*
    (243*symbol^3-1053*symbol^2+1266*symbol-400)/209952

def firstConductorRP : RatFunc ℚ :=
  1953125*(59049*symbol^6-511758*symbol^5+1724085*symbol^4-
    2860596*symbol^3+2441988*symbol^2-1011200*symbol+160000)/209952

def firstConductorK : RatFunc ℚ :=
  (firstConductorEll-2*(1-symbol)*firstConductorEllDerivative)*(25-9*symbol)+
    9*(1-symbol)*firstConductorEll

/-- Both coefficients of the complete unchanged ordinary BU[0,2] numerator. -/
def firstConductorNumeratorZero : RatFunc ℚ :=
  2*(1-symbol)*firstConductorLP*((2187/15625)*symbol^2)+
    4*(1-symbol)*firstConductorEll*(25-9*symbol)*firstConductorRP*
      firstConductorMeanDerivative+
    2*firstConductorRP*firstConductorMean*firstConductorK

def firstConductorNumeratorOne : RatFunc ℚ :=
  -4*(1-symbol)*firstConductorLP*firstConductorMeanDerivative-
    2*firstConductorRP*firstConductorK

theorem actual_first_conductor_zero_entries : bivBU 0 0=0 ∧ bivBU 0 1=0 := by
  norm_num [bivBU, bivLP, bivRP]

/-- The actual first row retains its full affine numerator and original quadratic divisor. -/
theorem actual_first_conductor_affine_numerator :
    bivBU 0 2 =
      (RatFunc.C firstConductorNumeratorZero+
        RatFunc.C firstConductorNumeratorOne*bivS)/(bivSourceDivisor*bivConductor) := by
  norm_num only [bivBU, bivLP, bivRP, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  congr 1
  norm_num [firstConductorNumeratorZero, firstConductorNumeratorOne,
    firstConductorLP, firstConductorRP, firstConductorMean,
    firstConductorMeanDerivative, firstConductorEll, firstConductorEllDerivative,
    firstConductorK, bivX, bivEll, bivEllX, bivMean, bivMeanX,
    bivConductorX, bivCollision, map_div₀, map_add, map_sub, map_mul, map_pow,
    map_neg, _root_.map_ofNat]
  ring

theorem actual_first_conductor_transformed_row (j : Fin 3) :
    bivConductorBU 2 j = (1-bivS)*bivBU 0 2*bivJCG bivB j 2 := by
  fin_cases j
  all_goals norm_num [bivConductorBU, Fin.sum_univ_succ, bivJCG,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    actual_first_conductor_zero_entries.1, actual_first_conductor_zero_entries.2]

end

end WPForcedSourceStokes
