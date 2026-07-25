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

open MeasureTheory Set

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

/-- The explicit scalar budget obtained by integrating the logarithmic
envelope from `T` to positive infinity. -/
noncomputable def paperArchimedeanRankTwoTailBudget
    (N : ℕ) (rho T : ℝ) : ℝ :=
  (2 * ((2 * N + 1 : ℕ) : ℝ) * rho / Real.pi ^ 2) *
    (Real.log T / (T - rho * N) +
      (rho * N)⁻¹ * Real.log (T / (T - rho * N)))

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

/-- The logarithmic rank-two envelope is integrable on every tail lying to
the right of its pole. -/
theorem integrableOn_Ioi_paperArchimedeanRankTwoLogEnvelope
    (N : ℕ) {rho T : ℝ}
    (hN : 0 < N) (hrho : 0 < rho)
    (hT : rho * N < T) (hT1 : 1 ≤ T) :
    IntegrableOn
      (paperArchimedeanRankTwoLogEnvelope N rho) (Ioi T) := by
  have hb : 0 < rho * N := by positivity
  unfold paperArchimedeanRankTwoLogEnvelope
  exact
    (integrableOn_Ioi_log_div_sub_sq hb hT hT1).const_mul
      (2 * ((2 * N + 1 : ℕ) : ℝ) * rho / Real.pi ^ 2)

/-- Exact evaluation of the improper integral of the rank-two logarithmic
envelope. -/
theorem integral_Ioi_paperArchimedeanRankTwoLogEnvelope
    (N : ℕ) {rho T : ℝ}
    (hN : 0 < N) (hrho : 0 < rho)
    (hT : rho * N < T) (hT1 : 1 ≤ T) :
    ∫ r in Ioi T, paperArchimedeanRankTwoLogEnvelope N rho r =
      paperArchimedeanRankTwoTailBudget N rho T := by
  have hb : 0 < rho * N := by positivity
  unfold paperArchimedeanRankTwoLogEnvelope
    paperArchimedeanRankTwoTailBudget
  rw [integral_const_mul,
    integral_Ioi_log_div_sub_sq hb hT hT1]

/-- Every finite interval of the nonnegative logarithmic envelope is bounded
by its exact improper tail budget. -/
theorem intervalIntegral_paperArchimedeanRankTwoLogEnvelope_le_tailBudget
    (N : ℕ) {rho T R : ℝ}
    (hN : 0 < N) (hrho : 0 < rho)
    (hT : rho * N < T) (hT1 : 1 ≤ T) (hTR : T ≤ R) :
    (∫ r in T..R, paperArchimedeanRankTwoLogEnvelope N rho r) ≤
      paperArchimedeanRankTwoTailBudget N rho T := by
  have hInt :=
    integrableOn_Ioi_paperArchimedeanRankTwoLogEnvelope
      N hN hrho hT hT1
  rw [← integral_Ioi_paperArchimedeanRankTwoLogEnvelope
    N hN hrho hT hT1, intervalIntegral.integral_of_le hTR]
  apply setIntegral_mono_set hInt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hlog : 0 ≤ Real.log r :=
      Real.log_nonneg (hT1.trans hr.le)
    unfold paperArchimedeanRankTwoLogEnvelope
    positivity
  · exact Filter.Eventually.of_forall fun _ hr => hr.1

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

/-- The finite actual matrix tail admits the explicit scalar `B_T` bound,
uniformly in its upper endpoint. The only non-explicit datum is the common
starting threshold inherited from the eventual `h₊` estimates. -/
theorem
    exists_T0_quadraticForm_paperActualArchimedeanRankTwoIncrement_le_tailBudget :
    ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ (N : ℕ) (L : ℝ) {rho T R : ℝ},
        0 < N → 0 < rho → T0 ≤ T → rho * N < T → T ≤ R →
        ∀ x : FiniteVector (2 * N + 1),
          quadraticForm
              (paperActualArchimedeanRankTwoIncrement N L rho T R) x ≤
            paperArchimedeanRankTwoTailBudget N rho T * squaredNorm x := by
  obtain ⟨T0, hT01, hT0⟩ :=
    exists_one_le_eventually_archimedeanHPlus_bounds
  refine ⟨T0, hT01, ?_⟩
  intro N L rho T R hN hrho hT0T hPole hTR x
  have hweightNonneg :
      ∀ r ∈ Icc T R, 0 ≤ paperArchimedeanWeight L rho r := by
    intro r hr
    exact paperArchimedeanWeight_nonneg hrho
      (hT0 r (hT0T.trans hr.1)).1
  have hmatrix :
      quadraticForm
          (paperActualArchimedeanRankTwoIncrement N L rho T R) x ≤
        (∫ r in T..R,
          paperArchimedeanRankTwoPointwiseBudget N
            (paperArchimedeanWeight L rho) rho r) *
          squaredNorm x := by
    unfold paperActualArchimedeanRankTwoIncrement
    exact quadraticForm_paperArchimedeanRankTwoIncrement_le
      N hTR (continuous_paperArchimedeanWeight L rho).continuousOn
      hweightNonneg hrho hPole x
  have hactualInt :
      IntervalIntegrable
        (paperArchimedeanRankTwoPointwiseBudget N
          (paperArchimedeanWeight L rho) rho) volume T R :=
    (continuousOn_paperArchimedeanRankTwoPointwiseBudget
      N (continuous_paperArchimedeanWeight L rho).continuousOn hPole
      |>.intervalIntegrable_of_Icc hTR)
  have henvIoi :=
    integrableOn_Ioi_paperArchimedeanRankTwoLogEnvelope
      N hN hrho hPole (hT01.trans hT0T)
  have henvInt :
      IntervalIntegrable
        (paperArchimedeanRankTwoLogEnvelope N rho) volume T R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hTR]
    exact henvIoi.mono_set Ioc_subset_Ioi_self
  have hintegral :
      (∫ r in T..R,
          paperArchimedeanRankTwoPointwiseBudget N
            (paperArchimedeanWeight L rho) rho r) ≤
        ∫ r in T..R,
          paperArchimedeanRankTwoLogEnvelope N rho r := by
    apply intervalIntegral.integral_mono_on hTR hactualInt henvInt
    intro r hr
    have hh := hT0 r (hT0T.trans hr.1)
    exact paperArchimedeanRankTwoPointwiseBudget_le_log_envelope
      N hrho hh.1 hh.2
  calc
    quadraticForm
          (paperActualArchimedeanRankTwoIncrement N L rho T R) x ≤
        (∫ r in T..R,
          paperArchimedeanRankTwoPointwiseBudget N
            (paperArchimedeanWeight L rho) rho r) *
          squaredNorm x :=
      hmatrix
    _ ≤
        (∫ r in T..R,
          paperArchimedeanRankTwoLogEnvelope N rho r) *
          squaredNorm x :=
      mul_le_mul_of_nonneg_right hintegral (squaredNorm_nonneg x)
    _ ≤ paperArchimedeanRankTwoTailBudget N rho T * squaredNorm x :=
      mul_le_mul_of_nonneg_right
        (intervalIntegral_paperArchimedeanRankTwoLogEnvelope_le_tailBudget
          N hN hrho hPole (hT01.trans hT0T) hTR)
        (squaredNorm_nonneg x)

end WeilExtremalKernels
