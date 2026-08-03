import HardyTheorem.SelbergSqrtZetaCollectedArithmetic

open scoped ArithmeticFunction

namespace HardyTheorem

noncomputable example : ArithmeticFunction ℝ :=
  selbergSqrtZetaLogCoeff

noncomputable example : ArithmeticFunction ℝ :=
  selbergMoebiusLogCoeff

example :
    (2 : ArithmeticFunction ℝ) *
        (selbergSqrtZetaCoeff * selbergSqrtZetaLogCoeff) =
      selbergMoebiusLogCoeff :=
  two_mul_selbergSqrtZeta_mul_logCoeff

example :
    selbergMoebiusLogCoeff *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      -ArithmeticFunction.vonMangoldt :=
  selbergMoebiusLogCoeff_mul_zeta

example :
    (selbergSqrtZetaCoeff * selbergSqrtZetaCoeff) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = 1 :=
  selbergSqrtZetaCoeff_sq_mul_zeta

example :
    (4 : ArithmeticFunction ℝ) *
        ((selbergSqrtZetaLogCoeff * selbergSqrtZetaLogCoeff) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) =
      ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt :=
  four_mul_selbergSqrtZetaLogCoeff_sq_mul_zeta

noncomputable example (X : ℕ) : ArithmeticFunction ℝ :=
  selbergSqrtZetaFullTapered X

example (X n : ℕ) :
    selbergSqrtZetaFullTapered X n =
      selbergSqrtZetaCoeff n * (1 - Real.log n / Real.log X) :=
  selbergSqrtZetaFullTapered_apply X n

noncomputable example (X : ℕ) : ArithmeticFunction ℝ :=
  selbergSqrtZetaScaledTapered X

example (X n : ℕ) :
    selbergSqrtZetaScaledTapered X n =
      selbergSqrtZetaCoeff n * (Real.log X - Real.log n) :=
  selbergSqrtZetaScaledTapered_apply X n

example (X : ℕ) :
    (4 : ArithmeticFunction ℝ) *
        (((selbergSqrtZetaScaledTapered X * selbergSqrtZetaScaledTapered X) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ))) =
      (4 * Real.log X ^ 2) • (1 : ArithmeticFunction ℝ) +
        (4 * Real.log X) • ArithmeticFunction.vonMangoldt +
        ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt :=
  selbergSqrtZetaScaledTapered_collected X

example {X : ℕ} (hX : 1 < X) :
    selbergSqrtZetaScaledTapered X =
      Real.log X • selbergSqrtZetaFullTapered X :=
  selbergSqrtZetaScaledTapered_eq_log_smul hX

example {X : ℕ} (hX : 1 < X) :
    (4 * Real.log X ^ 2) •
        (((selbergSqrtZetaFullTapered X * selbergSqrtZetaFullTapered X) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ))) =
      (4 * Real.log X ^ 2) • (1 : ArithmeticFunction ℝ) +
        (4 * Real.log X) • ArithmeticFunction.vonMangoldt +
        ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt :=
  selbergSqrtZetaFullTapered_collected_denominator_free hX

example {X : ℕ} (hX : 1 < X) :
    ((selbergSqrtZetaFullTapered X * selbergSqrtZetaFullTapered X) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) =
      (1 : ArithmeticFunction ℝ) +
        (Real.log X)⁻¹ • ArithmeticFunction.vonMangoldt +
        (4 * Real.log X ^ 2)⁻¹ •
          (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) :=
  selbergSqrtZetaFullTapered_collected hX

example {X n : ℕ} (hn1 : 1 ≤ n) (hnX : n ≤ X) :
    selbergShortTaperedSqrtZeta X n = selbergSqrtZetaFullTapered X n :=
  selbergShortTaperedSqrtZeta_eq_full_of_le hn1 hnX

example {X n : ℕ} (hn1 : 1 ≤ n) (hnX : n ≤ X) :
    (selbergShortTaperedSqrtZeta X * selbergShortTaperedSqrtZeta X) n =
      (selbergSqrtZetaFullTapered X * selbergSqrtZetaFullTapered X) n :=
  selbergShortTaperedSqrtZeta_sq_eq_full_sq_of_le hn1 hnX

example {X n : ℕ} (hn1 : 1 ≤ n) (hnX : n ≤ X) :
    (((selbergShortTaperedSqrtZeta X * selbergShortTaperedSqrtZeta X) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n) =
      (((selbergSqrtZetaFullTapered X * selbergSqrtZetaFullTapered X) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n) :=
  selbergShortTaperedSqrtZeta_collected_eq_full_of_le hn1 hnX

example {X n : ℕ} (hX : 1 < X) (hn1 : 1 ≤ n) (hnX : n ≤ X) :
    (((selbergShortTaperedSqrtZeta X * selbergShortTaperedSqrtZeta X) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n) =
      (if n = 1 then 1 else 0) +
        ArithmeticFunction.vonMangoldt n / Real.log X +
        (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) n /
          (4 * Real.log X ^ 2) :=
  selbergShortTaperedSqrtZeta_collected_apply_of_le hX hn1 hnX

end HardyTheorem
