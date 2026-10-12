import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace WPFieldAssembly.ScalarFinalSuccessorGreenCancellation

variable {K : Type*} [Field K]

/- The actual remaining collector is expanded before any pole is selected.
This certificate gives its exact cofactors against the seven full-source
identities in NativeJointSuccessorMixedGreenCore. It assigns no source value.
The symmetric and cubic factors Ds and Dt are independent. The only
denominator requiring cancellation in this identity is three. -/

/-- The complete mixed Green remainder is the sum of the seven source defects. -/
theorem whole_collector_cofactor_identity (h3 : (3 : K) ≠ 0)
    (A C Cd H S L h Ds Dt j jd e delta deltaD bracketD cbDeltaL sigma phiB
      completion correction proper joint Nj b b0 bD b0D primitiveD : K) :
    let remainder :=
      delta * L - A * H * deltaD - A * H * bracketD + cbDeltaL +
        H * sigma + H * S * phiB - A * completion -
        A * b0 * Cd - A * proper / 3 + (10 * h / 3) * S * e -
        (2 / 3) * Dt * e * L - Nj - joint
    let Hdefect :=
      H * ((3 / 2) * S * b - A * deltaD - A * bracketD + S * phiB) -
        A * completion + (2 / 5) * A * H * Ds * jd - correction
    let CBdefect := cbDeltaL - (3 / 2) * H * S * b - 3 * h * S * b + A * Cd * b
    let Mdefect :=
      A * C * (b0D + bD) - A * proper / 3 + H * sigma -
        (2 / 5) * A * H * Ds * jd - joint + correction
    let Pdefect := primitiveD - Cd * (b0 + b) - C * (b0D + bD)
    let deltaDefect := delta - (2 / 5) * Ds * j - (2 / 3) * Dt * e
    let Ndefect := Nj - (2 / 5) * L * Ds * j + 2 * h * S * j
    let Bdefect := b + (2 / 3) * j + (10 / 9) * e
    remainder + A * primitiveD =
      Hdefect + CBdefect + Mdefect + A * Pdefect + L * deltaDefect - Ndefect +
        3 * h * S * Bdefect := by
  dsimp only
  have h9 : (9 : K) ≠ 0 := by
    convert pow_ne_zero 2 h3 using 1
    norm_num
  field_simp [h3, h9]
  ring

end WPFieldAssembly.ScalarFinalSuccessorGreenCancellation
