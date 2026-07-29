import PrimeNumberTheorem.ExplicitFormulaRealInterpolation

namespace PrimeNumberTheorem
namespace ExplicitFormulaAux

#check jumpVonMangoldt_nonneg_le_log
#check chebyshevPsi_eq_floor
#check chebyshevPsi0_sub_floor_eq
#check abs_chebyshevPsi0_sub_floor_le_log
#check norm_explicitFormulaApproxWithMultiplicity_sub_floor_le
#check norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_floor

example {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ PrimeNumberTheorem.jumpVonMangoldt x ∧
      PrimeNumberTheorem.jumpVonMangoldt x ≤ Real.log x :=
  jumpVonMangoldt_nonneg_le_log hx

example (x : ℝ) :
    chebyshevPsi x =
      chebyshevPsi (Nat.floor x : ℝ) :=
  chebyshevPsi_eq_floor x

example (x : ℝ) :
    chebyshevPsi0 x - chebyshevPsi0 (Nat.floor x : ℝ) =
      (PrimeNumberTheorem.jumpVonMangoldt (Nat.floor x : ℝ) -
        PrimeNumberTheorem.jumpVonMangoldt x) / 2 :=
  chebyshevPsi0_sub_floor_eq x

example {x : ℝ} (hx : 3 ≤ x) :
    |chebyshevPsi0 x - chebyshevPsi0 (Nat.floor x : ℝ)| ≤
      (Real.log (Nat.floor x : ℝ) + Real.log x) / 2 :=
  abs_chebyshevPsi0_sub_floor_le_log hx

example {x T : ℝ} (hx : 3 ≤ x) :
    ‖explicitFormulaApproxWithMultiplicity x T -
        explicitFormulaApproxWithMultiplicity (Nat.floor x : ℝ) T‖ ≤
      (1 + globalZeroMultiplicity T) *
          |x - (Nat.floor x : ℝ)| +
        2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound :=
  norm_explicitFormulaApproxWithMultiplicity_sub_floor_le hx

example {x T B : ℝ} (hx : 3 ≤ x)
    (hfloor :
      ‖explicitFormulaApproxWithMultiplicity (Nat.floor x : ℝ) T -
          (chebyshevPsi0 (Nat.floor x : ℝ) : ℂ)‖ ≤ B) :
    ‖explicitFormulaApproxWithMultiplicity x T -
        (chebyshevPsi0 x : ℂ)‖ ≤
      B +
        (1 + globalZeroMultiplicity T) *
          |x - (Nat.floor x : ℝ)| +
        2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound +
        (Real.log (Nat.floor x : ℝ) + Real.log x) / 2 :=
  norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_floor
    hx hfloor

end ExplicitFormulaAux
end PrimeNumberTheorem
