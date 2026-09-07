import HardyTheorem.AFECriticalDyadicCanonicalSelector

/-!
# A unit-phase logarithmic critical-line approximate functional equation

The Carlson critical-boundary argument needs less than the sharp symmetric
AFE recorded in `HardyTheorem.AFE`.  The dual multiplier may be any unit
complex number, and a single logarithm in the `t^(-1/4)` remainder is
absorbed by the half-range power saving.  This file records that weaker
analytic target and proves the phase-independent pointwise energy algebra.

It does not assert the analytic target.  Its proof is the remaining
Titchmarsh 4.13 transformation step.
-/

open Complex

namespace HardyTheorem
namespace AFE

/-- The logarithmic, unit-phase square-root AFE sufficient for the
half-length Carlson critical-boundary estimate.  No regularity of the
existential phase as a function of height is required downstream. -/
def zeta_critical_unitPhase_logAfe_target : Prop :=
  ∃ R T0 : ℝ, 0 < R ∧ 1 ≤ T0 ∧ ∀ t : ℝ, T0 ≤ t →
    ∃ phase remainder : ℂ,
      ‖phase‖ = 1 ∧
      riemannZeta ((1 / 2 : ℂ) + I * t) =
        criticalAfeMainSum t + phase * criticalAfeDualSum t + remainder ∧
      ‖remainder‖ ≤
        R * t ^ (-1 / 4 : ℝ) * (1 + Real.log t)

/-- Multiplication by an arbitrary unit phase does not change the dual AFE
energy.  In particular, the Carlson moment argument never uses the argument
of the functional-equation multiplier. -/
theorem criticalAfeUnitPhaseDualProduct_normSq_eq_mainProduct
    (phase : ℂ) (hphase : ‖phase‖ = 1) (X : ℕ) (t : ℝ) :
    Complex.normSq
        (phase *
          (criticalAfeDualSum t *
            selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) =
      Complex.normSq
        (criticalAfeMainSum t *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) := by
  rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul,
    criticalAfeDualSum_eq_conj_mainSum, Complex.normSq_conj]
  have hphaseSq : Complex.normSq phase = 1 := by
    rw [Complex.normSq_eq_norm_sq, hphase]
    norm_num
  rw [hphaseSq, one_mul]

private theorem normSq_add_add_le_three_unitPhase (A B C : ℂ) :
    Complex.normSq (A + B + C) ≤
      3 * (Complex.normSq A + Complex.normSq B + Complex.normSq C) := by
  simp only [Complex.normSq_eq_norm_sq]
  have htri : ‖A + B + C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ :=
    (norm_add_le (A + B) C).trans
      (add_le_add (norm_add_le A B) le_rfl)
  have hsquare : ‖A + B + C‖ ^ 2 ≤
      (‖A‖ + ‖B‖ + ‖C‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
        (norm_nonneg _))).2 htri
  calc
    ‖A + B + C‖ ^ 2 ≤ (‖A‖ + ‖B‖ + ‖C‖) ^ 2 := hsquare
    _ ≤ 3 * (‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2) := by
      nlinarith [sq_nonneg (‖A‖ - ‖B‖), sq_nonneg (‖A‖ - ‖C‖),
        sq_nonneg (‖B‖ - ‖C‖)]

/-- A unit-phase AFE decomposition is bounded by two copies of the main
Dirichlet-polynomial energy and the actual remainder energy. -/
theorem normSq_criticalUnitPhaseAfeProduct_le_three_components
    (phase remainder : ℂ) (hphase : ‖phase‖ = 1)
    (X : ℕ) (t : ℝ)
    (hdecomp :
      riemannZeta ((1 / 2 : ℂ) + I * t) =
        criticalAfeMainSum t + phase * criticalAfeDualSum t + remainder) :
    Complex.normSq
        (riemannZeta ((1 / 2 : ℂ) + I * t) *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) ≤
      3 *
        (2 * Complex.normSq
          (criticalAfeMainSum t *
            selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) +
          Complex.normSq
            (remainder *
              selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) := by
  let M := selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)
  have hproduct :
      riemannZeta ((1 / 2 : ℂ) + I * t) * M =
        criticalAfeMainSum t * M +
          phase * (criticalAfeDualSum t * M) + remainder * M := by
    rw [hdecomp]
    ring
  rw [hproduct]
  have hthree := normSq_add_add_le_three_unitPhase
    (criticalAfeMainSum t * M)
    (phase * (criticalAfeDualSum t * M))
    (remainder * M)
  rw [criticalAfeUnitPhaseDualProduct_normSq_eq_mainProduct
    phase hphase X t] at hthree
  simpa only [M, add_assoc, two_mul] using hthree

end AFE
end HardyTheorem
