import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryPackage
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageNaturalSignAlternative
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTUnnormalizedTargetAmplitudeTransfer

/-!
# Variable-boundary exponent transfer

The existing dynamic-boundary modules vary the truncation height while
keeping the boundary real part fixed.  This file permits a genuinely moving
boundary `beta x`.  It records the exact variable target scale, the actual
finite zeta package at that boundary, and the transfer from an unsigned
moving-package witness to one persistent sign of the true PNT error.
-/

namespace PrimeNumberTheorem

open scoped Topology
open Complex Filter ZeroForcedOscillation

noncomputable section

/-- The equal-real-part zeta package at the height and boundary selected at
the current scale. -/
noncomputable def variableBoundaryZeroPackage
    (H beta : ℝ → ℝ) (x : ℝ) : Finset ℂ :=
  equalRealPartZeroPackage (H x) (beta x)

/-- The natural target amplitude for a moving boundary exponent. -/
noncomputable def variableBoundaryTargetAmplitude
    (beta : ℝ → ℝ) (x : ℝ) : ℝ :=
  targetZeroPowerAmplitude (beta x) x

/-- At every scale, the selected boundary is a right edge of the visible
positive-ordinate zero set. -/
def IsVariableBoundaryRightEdge
    (H beta : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, ∀ rho ∈ positiveNontrivialZerosFinset (H x),
    rho.re ≤ beta x

theorem mem_variableBoundaryZeroPackage
    {H beta : ℝ → ℝ} {x : ℝ} {rho : ℂ} :
    rho ∈ variableBoundaryZeroPackage H beta x ↔
      RiemannHypothesis.IsNontrivialZero rho ∧
        |rho.im| ≤ H x ∧ rho.re = beta x := by
  simp [variableBoundaryZeroPackage, mem_equalRealPartZeroPackage]

/-- A visible positive zero outside the complete moving boundary package lies
strictly to the left of the selected boundary. -/
theorem positiveOutside_variableBoundaryZeroPackage_re_lt
    {H beta : ℝ → ℝ}
    (hright : IsVariableBoundaryRightEdge H beta)
    {x : ℝ} {rho : ℂ}
    (hrho :
      rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x)
        (variableBoundaryZeroPackage H beta x)) :
    rho.re < beta x := by
  have hrhoFull : rho ∈ positiveNontrivialZerosFinset (H x) :=
    (Finset.mem_sdiff.mp hrho).1
  rcases mem_positiveNontrivialZerosFinset.mp hrhoFull with
    ⟨hzero, him, hheight⟩
  have hle := hright x rho hrhoFull
  apply lt_of_le_of_ne hle
  intro hre
  exact (Finset.mem_sdiff.mp hrho).2
    (mem_variableBoundaryZeroPackage.mpr
      ⟨hzero, by simpa [abs_of_pos him] using hheight, hre⟩)

/-- Exact explicit-formula decomposition around the genuinely moving
equal-real-part package. -/
theorem relativeChebyshevPsi0Error_eq_variableBoundaryPackage_add_actualResiduals
    (H beta : ℝ → ℝ) (x : ℝ) :
    relativeChebyshevPsi0Error x =
      dynamicVisibleClusterPNTMain H
          (variableBoundaryZeroPackage H beta x) x +
        (actualPNTClosedRealAxisRelativeTerm x +
          actualPNTExplicitFormulaRelativeRemainder H x +
          dynamicOutsideClusterPNTComplement H
            (variableBoundaryZeroPackage H beta x) x) := by
  exact relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
    H (variableBoundaryZeroPackage H beta x) x

/-- Multiplying the moving relative target scale by the positive sample point
restores the exact variable exponent `x^(beta x)`. -/
theorem self_mul_variableBoundaryTargetAmplitude
    {beta : ℝ → ℝ} {x : ℝ} (hx : 0 < x) :
    x * variableBoundaryTargetAmplitude beta x = x ^ (beta x) := by
  exact self_mul_targetZeroPowerAmplitude hx

/-- The variable boundary target amplitude is positive at all sufficiently
large natural sample points. -/
theorem eventually_variableBoundaryTargetAmplitude_pos
    (beta : ℝ → ℝ) :
    ∀ᶠ m : ℕ in atTop,
      0 < variableBoundaryTargetAmplitude beta (m : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmPos : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  simp only [variableBoundaryTargetAmplitude, targetZeroPowerAmplitude]
  exact Real.rpow_pos_of_pos hmPos _

/-- An unsigned moving-package witness and a residual negligible at the same
variable scale force one persistent sign in the genuine relative PNT error. -/
theorem variableBoundaryMainWitness_naturalSignAlternativeTransfer
    {H beta : ℝ → ℝ} {c loss : ℝ}
    (hloss : 0 < loss) (hlossC : loss < c)
    (hresidual :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ =>
          variableBoundaryTargetAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H
              (variableBoundaryZeroPackage H beta (m : ℝ))
              (m : ℝ)))
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude beta (m : ℝ))) :
    0 < c - loss ∧
      (HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          (fun m : ℕ =>
            (c - loss) *
              variableBoundaryTargetAmplitude beta (m : ℝ)) ∨
        HasFarNaturalPointNegativeTargetAmplitudeWitness
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          (fun m : ℕ =>
            (c - loss) *
              variableBoundaryTargetAmplitude beta (m : ℝ))) := by
  have hsmall :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H
              (variableBoundaryZeroPackage H beta (m : ℝ))
              (m : ℝ)| <
          loss * variableBoundaryTargetAmplitude beta (m : ℝ) :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      (eventually_variableBoundaryTargetAmplitude_pos beta) hresidual hloss
  refine ⟨sub_pos.mpr hlossC, ?_⟩
  rcases hmain.signAlternative with hpos | hneg
  · exact Or.inl (hpos.transfer_eventually_sub_lt hsmall)
  · exact Or.inr (hneg.transfer_eventually_sub_lt hsmall)

/-- Positive relative-error witnesses transfer to the unnormalized error with
a genuinely variable exponent. -/
theorem
    HasFarPositiveTargetAmplitudeWitness.relativeChebyshevPsi0Error_to_unnormalized_variableExponent
    {beta : ℝ → ℝ} {q : ℝ}
    (hwitness :
      HasFarPositiveTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x => q * variableBoundaryTargetAmplitude beta x)) :
    HasFarPositiveTargetAmplitudeWitness
      chebyshevPsi0Error (fun x => q * x ^ (beta x)) := by
  intro X
  rcases hwitness (max X 1) with ⟨x, hxMax, hxWitness⟩
  have hxOne : 1 ≤ x := (le_max_right X 1).trans hxMax
  have hxPos : 0 < x := zero_lt_one.trans_le hxOne
  have hscaled := mul_le_mul_of_nonneg_left hxWitness hxPos.le
  refine ⟨x, (le_max_left X 1).trans hxMax, ?_⟩
  calc
    q * x ^ (beta x) =
        x * (q * variableBoundaryTargetAmplitude beta x) := by
          rw [← self_mul_variableBoundaryTargetAmplitude hxPos]
          ring
    _ ≤ x * relativeChebyshevPsi0Error x := hscaled
    _ = chebyshevPsi0Error x :=
      (chebyshevPsi0Error_eq_self_mul_relative hxPos.ne').symm

/-- Negative relative-error witnesses transfer to the unnormalized error with
a genuinely variable exponent. -/
theorem
    HasFarNegativeTargetAmplitudeWitness.relativeChebyshevPsi0Error_to_unnormalized_variableExponent
    {beta : ℝ → ℝ} {q : ℝ}
    (hwitness :
      HasFarNegativeTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x => q * variableBoundaryTargetAmplitude beta x)) :
    HasFarNegativeTargetAmplitudeWitness
      chebyshevPsi0Error (fun x => q * x ^ (beta x)) := by
  intro X
  rcases hwitness (max X 1) with ⟨x, hxMax, hxWitness⟩
  have hxOne : 1 ≤ x := (le_max_right X 1).trans hxMax
  have hxPos : 0 < x := zero_lt_one.trans_le hxOne
  have hscaled := mul_le_mul_of_nonneg_left hxWitness hxPos.le
  refine ⟨x, (le_max_left X 1).trans hxMax, ?_⟩
  calc
    chebyshevPsi0Error x =
        x * relativeChebyshevPsi0Error x :=
      chebyshevPsi0Error_eq_self_mul_relative hxPos.ne'
    _ ≤ x * (-(q * variableBoundaryTargetAmplitude beta x)) := hscaled
    _ = -(q * x ^ (beta x)) := by
      rw [← self_mul_variableBoundaryTargetAmplitude hxPos]
      ring

/-- Variable-boundary transfer stated directly for the unnormalized centered
Chebyshev error. -/
theorem variableBoundaryMainWitness_unnormalizedSignAlternativeTransfer
    {H beta : ℝ → ℝ} {c loss : ℝ}
    (hloss : 0 < loss) (hlossC : loss < c)
    (hresidual :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ =>
          variableBoundaryTargetAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H
              (variableBoundaryZeroPackage H beta (m : ℝ))
              (m : ℝ)))
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude beta (m : ℝ))) :
    0 < c - loss ∧
      (HasFarPositiveTargetAmplitudeWitness
          chebyshevPsi0Error
          (fun x : ℝ => (c - loss) * x ^ (beta x)) ∨
        HasFarNegativeTargetAmplitudeWitness
          chebyshevPsi0Error
          (fun x : ℝ => (c - loss) * x ^ (beta x))) := by
  rcases
      variableBoundaryMainWitness_naturalSignAlternativeTransfer
        hloss hlossC hresidual hmain with
    ⟨hcoefficient, hsign⟩
  refine ⟨hcoefficient, ?_⟩
  rcases hsign with hpos | hneg
  · exact Or.inl
      hpos.toReal.relativeChebyshevPsi0Error_to_unnormalized_variableExponent
  · exact Or.inr
      hneg.toReal.relativeChebyshevPsi0Error_to_unnormalized_variableExponent

end
end PrimeNumberTheorem
