import PrimeNumberTheorem.ZeroDensityLayerBudgetAntiCancellation
import PrimeNumberTheorem.ZeroForcedOscillationExplicitFormula
import PrimeNumberTheorem.ZeroDensityLayerBudgetPsi0FloorPowerTransfer

open Filter Topology

namespace PrimeNumberTheorem

open ZeroForcedOscillation

/--
Diagonal-minus-off-diagonal energy coefficient of the actual equal-real-part
zeta-zero package on a logarithmic interval of length `L`.
-/
noncomputable def actualEqualRealPartZeroPackageEnergy
    (T beta L : ℝ) : ℝ :=
  (∑ rho ∈ equalRealPartZeroPackage T beta,
      ‖(analyticOrderNatAt riemannZeta rho : ℂ) * rho⁻¹‖ ^ 2) -
    offDiagonalBound (equalRealPartZeroPackage T beta)
      (fun rho => (analyticOrderNatAt riemannZeta rho : ℂ) * rho⁻¹)
      Complex.im / L

/--
The continuous mean-square theorem gives an actual zeta-zero package witness
with coefficient `sqrt actualEqualRealPartZeroPackageEnergy`.
-/
theorem exists_far_norm_actualEqualRealPartZeroPackageContribution_ge
    (T beta L : ℝ) (hL : 0 < L)
    (X : ℝ) :
    ∃ y ∈ Set.Ioo X (X + L),
      Real.exp (beta * y) *
          Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) ≤
        ‖equalRealPartZeroPackageContribution (Real.exp y) T beta‖ := by
  have hre :
      ∀ rho ∈ equalRealPartZeroPackage T beta, rho.re = beta := by
    intro rho hrho
    exact (mem_equalRealPartZeroPackage.mp hrho).2.2
  rcases exists_far_norm_equalRealPart_zeroPackage_ge
      (equalRealPartZeroPackage T beta)
      (analyticOrderNatAt riemannZeta) beta L hL hre X with
    ⟨y, hy, hmain⟩
  refine ⟨y, hy, ?_⟩
  rw [Real.sqrt_mul (sq_nonneg (Real.exp (beta * y))),
    Real.sqrt_sq (Real.exp_nonneg (beta * y))] at hmain
  simpa [actualEqualRealPartZeroPackageEnergy,
    equalRealPartZeroPackageContribution] using hmain

/--
Pointwise interval transfer from the actual equal-real-part package to a
natural `psi0` witness.

The hypotheses isolate the two honest losses: the full explicit-formula
remainder and floor rounding.  Both are measured at the same logarithmic
witness scale.
-/
theorem exists_far_natFloor_chebyshevPsi0Error_ge_of_actualZeroPackage
    (T beta L remainderCoeff loss X : ℝ)
    (hL : 0 < L)
    (hremainder :
      ∀ y ∈ Set.Ioo X (X + L),
        ‖zeroPackageExplicitFormulaRemainder y T beta‖ ≤
          remainderCoeff * Real.exp (beta * y))
    (hround :
      ∀ y ∈ Set.Ioo X (X + L),
        chebyshevPsi0FloorRoundingBudget (Real.exp y) ≤
          loss * Real.exp (beta * y)) :
    ∃ y ∈ Set.Ioo X (X + L),
      (Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) -
          remainderCoeff - loss) *
            Real.exp (beta * y) ≤
        |chebyshevPsi0Error (Nat.floor (Real.exp y) : ℝ)| := by
  rcases exists_far_norm_actualEqualRealPartZeroPackageContribution_ge
      T beta L hL X with
    ⟨y, hy, hmain⟩
  have hrem := hremainder y hy
  have hactual :
      ‖equalRealPartZeroPackageContribution (Real.exp y) T beta‖ -
          ‖zeroPackageExplicitFormulaRemainder y T beta‖ ≤
        |chebyshevPsi0Error (Real.exp y)| := by
    have hraw :=
      norm_zeroPackage_sub_norm_remainder_le_norm_chebyshevPsi0_sub_exp
        T beta y
    rw [Complex.norm_real, Real.norm_eq_abs] at hraw
    simpa [chebyshevPsi0Error] using hraw
  have hcontinuous :
      (Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) -
          remainderCoeff) * Real.exp (beta * y) ≤
        |chebyshevPsi0Error (Real.exp y)| := by
    calc
      (Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) -
          remainderCoeff) * Real.exp (beta * y) =
          Real.exp (beta * y) *
              Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) -
            remainderCoeff * Real.exp (beta * y) := by
        ring
      _ ≤
          ‖equalRealPartZeroPackageContribution (Real.exp y) T beta‖ -
            ‖zeroPackageExplicitFormulaRemainder y T beta‖ :=
        sub_le_sub hmain hrem
      _ ≤ |chebyshevPsi0Error (Real.exp y)| := hactual
  refine ⟨y, hy, ?_⟩
  exact
    continuousExpPowerPsi0Witness_to_natFloor_of_roundingSmall
      (hround y hy) hcontinuous

/--
Eventual form: an eventual power-scale bound for the full explicit-formula
remainder yields natural floor witnesses in every sufficiently far
logarithmic interval.
-/
theorem eventually_exists_far_natFloor_chebyshevPsi0Error_ge_of_actualZeroPackage
    (T beta L remainderCoeff loss : ℝ)
    (hL : 0 < L) (hbeta : 0 < beta) (hloss : 0 < loss)
    (hremainder :
      ∀ᶠ y : ℝ in atTop,
        ‖zeroPackageExplicitFormulaRemainder y T beta‖ ≤
          remainderCoeff * Real.exp (beta * y)) :
    ∀ᶠ X : ℝ in atTop,
      ∃ y ∈ Set.Ioo X (X + L),
        (Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) -
            remainderCoeff - loss) *
              Real.exp (beta * y) ≤
          |chebyshevPsi0Error (Nat.floor (Real.exp y) : ℝ)| := by
  have hround :=
    eventually_chebyshevPsi0FloorRoundingBudget_exp_le hbeta hloss
  rcases eventually_atTop.1 (hremainder.and hround) with
    ⟨Y, hY⟩
  filter_upwards [eventually_ge_atTop Y] with X hX
  apply
    exists_far_natFloor_chebyshevPsi0Error_ge_of_actualZeroPackage
      T beta L remainderCoeff loss X hL
  · intro y hy
    exact (hY y (hX.trans hy.1.le)).1
  · intro y hy
    exact (hY y (hX.trans hy.1.le)).2

end PrimeNumberTheorem
