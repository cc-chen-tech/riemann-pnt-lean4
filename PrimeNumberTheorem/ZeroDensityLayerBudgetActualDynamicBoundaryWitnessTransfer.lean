import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryExplicitFormulaTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetSharpConstantTransfer

/-!
# Dynamic-boundary witness transfer

The dynamic-boundary explicit-formula theorem proves that the genuine
relative Chebyshev error differs from the moving equal-real-part package by
`o(x^(beta - 1))` at natural points.  This module records the exact lower
transfer supported by that statement.

It deliberately does not prove an oscillation theorem for the moving package.
Such an anti-cancellation input can be supplied independently.  If its
coefficient is `c`, then the `o`-remainder permits every fixed positive loss
`loss`, rather than imposing a hard loss such as `1 / 2`.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

/--
A far natural-point witness for the moving boundary package transfers to the
genuine relative PNT error with any fixed positive coefficient loss.

The hypothesis `hresidual` is exactly the conclusion of
`actualDynamicBoundaryExplicitFormulaResidual_targetAmplitudeNegligible`.
-/
theorem actualDynamicBoundaryMainWitness_naturalTransfer
    {beta c loss : ℝ} {H : ℝ → ℝ}
    (hloss : 0 < loss)
    (hresidual :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H
              (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
              (m : ℝ)))
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * targetZeroPowerAmplitude beta (m : ℝ))) :
    HasFarNaturalPointTargetAmplitudeWitness
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      (fun m : ℕ =>
        (c - loss) * targetZeroPowerAmplitude beta (m : ℝ)) := by
  have hsmall :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H
              (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
              (m : ℝ)| <
          loss * targetZeroPowerAmplitude beta (m : ℝ) :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      hresidual hloss
  exact hmain.transfer_eventually_sub_lt hsmall

/--
Real-variable facade for the dynamic-boundary witness transfer.

The conclusion is nontrivial whenever `loss < c`.  In a concrete zero
application, the coefficient `c` may retain the analytic multiplicity and
`1 / ‖rho‖` contribution supplied by the local oscillation theorem.
-/
theorem actualDynamicBoundaryMainWitness_realTransfer
    {beta c loss : ℝ} {H : ℝ → ℝ}
    (hloss : 0 < loss)
    (hlossC : loss < c)
    (hresidual :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H
              (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
              (m : ℝ)))
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * targetZeroPowerAmplitude beta (m : ℝ))) :
    0 < c - loss ∧
      HasFarTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) * targetZeroPowerAmplitude beta x) := by
  refine ⟨sub_pos.mpr hlossC, ?_⟩
  exact
    (actualDynamicBoundaryMainWitness_naturalTransfer
      hloss hresidual hmain).toReal

end PrimeNumberTheorem
