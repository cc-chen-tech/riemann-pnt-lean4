import WeilExtremalKernels.ArchimedeanHPlus
import WeilExtremalKernels.ArchimedeanTailBudget

/-!
# The actual finite archimedean rank-two tail

This module specializes the generic rank-two integration layer to the
Guinand-Weil weight

`pi⁻² * h₊(r) * sin²(L*r/2) / rho`.

It constructs the actual finite interval increment, proves eventual positive
semidefiniteness, and bounds its pointwise quadratic-form budget by the
logarithmic kernel whose improper integral was computed separately.

The threshold supplied here is non-explicit. The paper's threshold `7`, the
improper matrix limit, and the final explicit `B_T` matrix statement remain
separate quantitative steps.
-/

namespace WeilExtremalKernels

/-- The finite rank-two increment with the paper's actual archimedean
weight. -/
noncomputable def paperActualArchimedeanRankTwoIncrement
    (N : ℕ) (L rho a b : ℝ) : FiniteMatrix (2 * N + 1) :=
  paperArchimedeanRankTwoIncrement N
    (paperArchimedeanWeight L rho) rho a b

/-- Scalar logarithmic envelope for the actual pointwise matrix density. -/
noncomputable def paperArchimedeanRankTwoLogEnvelope
    (N : ℕ) (rho r : ℝ) : ℝ :=
  (2 * ((2 * N + 1 : ℕ) : ℝ) * rho / Real.pi ^ 2) *
    (Real.log r / (r - rho * N) ^ 2)

/-- Once `h₊` satisfies its nonnegative logarithmic envelope, the actual
rank-two pointwise budget has exactly the scalar shape needed by the proved
improper integral. -/
theorem paperArchimedeanRankTwoPointwiseBudget_le_log_envelope
    (N : ℕ) {L rho r : ℝ}
    (hrho : 0 < rho)
    (hh0 : 0 ≤ archimedeanHPlus r)
    (hhlog : archimedeanHPlus r ≤ Real.log r) :
    paperArchimedeanRankTwoPointwiseBudget N
        (paperArchimedeanWeight L rho) rho r ≤
      paperArchimedeanRankTwoLogEnvelope N rho r := by
  have hweight :=
    paperArchimedeanWeight_le_log_envelope
      (L := L) hrho hh0 hhlog
  have hfactorNonneg :
      0 ≤ 2 * ((2 * N + 1 : ℕ) : ℝ) *
        (rho / (r - rho * N)) ^ 2 := by
    positivity
  unfold paperArchimedeanRankTwoPointwiseBudget
    paperArchimedeanRankTwoLogEnvelope
  calc
    paperArchimedeanWeight L rho r *
          (2 * ((2 * N + 1 : ℕ) : ℝ) *
            (rho / (r - rho * N)) ^ 2) ≤
        (Real.log r / (Real.pi ^ 2 * rho)) *
          (2 * ((2 * N + 1 : ℕ) : ℝ) *
            (rho / (r - rho * N)) ^ 2) :=
      mul_le_mul_of_nonneg_right hweight hfactorNonneg
    _ = (2 * ((2 * N + 1 : ℕ) : ℝ) * rho / Real.pi ^ 2) *
        (Real.log r / (r - rho * N) ^ 2) := by
      field_simp

/-- Beyond one common non-explicit threshold, every finite interval of the
actual rank-two tail is positive semidefinite, provided it lies to the right
of all Cauchy poles. -/
theorem
    exists_T0_quadraticForm_paperActualArchimedeanRankTwoIncrement_nonneg :
    ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ (N : ℕ) (L : ℝ) {rho a b : ℝ},
        0 < rho → T0 ≤ a → rho * N < a → a ≤ b →
        ∀ x : FiniteVector (2 * N + 1),
          0 ≤ quadraticForm
            (paperActualArchimedeanRankTwoIncrement N L rho a b) x := by
  obtain ⟨T0, hT01, hT0⟩ :=
    exists_one_le_eventually_archimedeanHPlus_bounds
  refine ⟨T0, hT01, ?_⟩
  intro N L rho a b hrho hT0a ha hab x
  unfold paperActualArchimedeanRankTwoIncrement
  apply quadraticForm_paperArchimedeanRankTwoIncrement_nonneg
      N hab (continuous_paperArchimedeanWeight L rho).continuousOn
      ?_ hrho ha x
  intro r hr
  exact paperArchimedeanWeight_nonneg hrho
    (hT0 r (hT0a.trans hr.1)).1

/-- On the same eventual range, the actual finite increment is controlled by
the integral of its exact pointwise budget. This is the matrix step before
replacing that budget by the logarithmic envelope and evaluating the scalar
improper integral. -/
theorem
    exists_T0_quadraticForm_paperActualArchimedeanRankTwoIncrement_le :
    ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ (N : ℕ) (L : ℝ) {rho a b : ℝ},
        0 < rho → T0 ≤ a → rho * N < a → a ≤ b →
        ∀ x : FiniteVector (2 * N + 1),
          quadraticForm
              (paperActualArchimedeanRankTwoIncrement N L rho a b) x ≤
            (∫ r in a..b,
              paperArchimedeanRankTwoPointwiseBudget N
                (paperArchimedeanWeight L rho) rho r) *
              squaredNorm x := by
  obtain ⟨T0, hT01, hT0⟩ :=
    exists_one_le_eventually_archimedeanHPlus_bounds
  refine ⟨T0, hT01, ?_⟩
  intro N L rho a b hrho hT0a ha hab x
  unfold paperActualArchimedeanRankTwoIncrement
  apply quadraticForm_paperArchimedeanRankTwoIncrement_le
      N hab (continuous_paperArchimedeanWeight L rho).continuousOn
      ?_ hrho ha x
  intro r hr
  exact paperArchimedeanWeight_nonneg hrho
    (hT0 r (hT0a.trans hr.1)).1

end WeilExtremalKernels
