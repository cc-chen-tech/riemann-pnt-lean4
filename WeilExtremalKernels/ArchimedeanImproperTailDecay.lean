import WeilExtremalKernels.ArchimedeanImproperTail

/-!
# Decay of the cutoff-free finite archimedean tail

For fixed finite dimension `2 * N + 1`, frequency parameter `L`, and scale
`rho`, this module lets the lower cutoff `T` tend to positive infinity in the
improper matrix tail constructed in `ArchimedeanImproperTail`.

The proof uses the actual improper integral and the already evaluated scalar
budget `B_T`: every entry is dominated by the logarithmic envelope, while
every quadratic form lies between zero and `B_T * ‖x‖²`; the proved limit
`B_T -> 0` then supplies entrywise, finite-matrix, and quadratic-form decay.

The resulting stability thresholds are non-explicit and all parameters
`N`, `L`, and `rho` are fixed before `T -> +infinity`. Nothing here passes to
an infinite-dimensional Weil criterion.
-/

namespace WeilExtremalKernels

open Filter MeasureTheory Set
open scoped BigOperators Topology

/-- For fixed finite data and a fixed entry, the norm of the cutoff-free
actual tail is eventually bounded by the same scalar budget `B_T` that
controls its quadratic form. -/
theorem
    eventually_norm_paperActualArchimedeanRankTwoTail_entry_le_tailBudget
    (N : ℕ) (L rho : ℝ) (hN : 0 < N) (hrho : 0 < rho)
    (i j : Fin (2 * N + 1)) :
    ∀ᶠ T : ℝ in atTop,
      ‖paperActualArchimedeanRankTwoTail N L rho T i j‖ ≤
        paperArchimedeanRankTwoTailBudget N rho T := by
  obtain ⟨Th, hTh1, hTh⟩ :=
    exists_one_le_eventually_archimedeanHPlus_bounds
  filter_upwards
      [eventually_ge_atTop (max Th (rho * N + 1))] with T hT
  have hThT : Th ≤ T :=
    (le_max_left Th (rho * N + 1)).trans hT
  have hT1 : 1 ≤ T := hTh1.trans hThT
  have hPole : rho * N < T := by
    have h := (le_max_right Th (rho * N + 1)).trans hT
    linarith
  have hh :
      ∀ r, T ≤ r →
        0 ≤ archimedeanHPlus r ∧
          archimedeanHPlus r ≤ Real.log r := by
    intro r hr
    exact hTh r (hThT.trans hr)
  have henv :=
    integrableOn_Ioi_paperArchimedeanRankTwoLogEnvelope
      N hN hrho hPole hT1
  have hentryMajorant :
      ∀ᵐ r ∂volume.restrict (Ioi T),
        ‖paperArchimedeanRankTwoDensity N
            (paperArchimedeanWeight L rho r) rho r i j‖ ≤
          paperArchimedeanRankTwoLogEnvelope N rho r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact
      norm_paperActualArchimedeanRankTwoDensity_entry_le_logEnvelope
        N hrho (hPole.trans hr) (hh r hr.le).1 (hh r hr.le).2 i j
  unfold paperActualArchimedeanRankTwoTail
  calc
    ‖∫ r in Ioi T,
        paperArchimedeanRankTwoDensity N
          (paperArchimedeanWeight L rho r) rho r i j‖ ≤
        ∫ r in Ioi T,
          paperArchimedeanRankTwoLogEnvelope N rho r :=
      norm_integral_le_of_norm_le henv hentryMajorant
    _ = paperArchimedeanRankTwoTailBudget N rho T :=
      integral_Ioi_paperArchimedeanRankTwoLogEnvelope
        N hN hrho hPole hT1

/-- Every fixed entry of the cutoff-free actual tail tends to zero as its
lower cutoff tends to positive infinity. -/
theorem tendsto_paperActualArchimedeanRankTwoTail_entry_atTop
    (N : ℕ) (L rho : ℝ) (hN : 0 < N) (hrho : 0 < rho)
    (i j : Fin (2 * N + 1)) :
    Tendsto
      (fun T => paperActualArchimedeanRankTwoTail N L rho T i j)
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  exact squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_norm_paperActualArchimedeanRankTwoTail_entry_le_tailBudget
      N L rho hN hrho i j)
    (tendsto_paperArchimedeanRankTwoTailBudget_atTop N rho)

/-- For fixed finite data, the entire cutoff-free matrix tail tends
entrywise to the zero matrix. -/
theorem tendsto_paperActualArchimedeanRankTwoTail_atTop
    (N : ℕ) (L rho : ℝ) (hN : 0 < N) (hrho : 0 < rho) :
    Tendsto
      (paperActualArchimedeanRankTwoTail N L rho)
      atTop (nhds 0) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  exact tendsto_paperActualArchimedeanRankTwoTail_entry_atTop
    N L rho hN hrho i j

/-- For fixed finite data, one eventual range simultaneously controls every
quadratic form of the cutoff-free tail by `B_T * ‖x‖²`. -/
theorem eventually_quadraticForm_paperActualArchimedeanRankTwoTail_bounds
    (N : ℕ) (L rho : ℝ) (hN : 0 < N) (hrho : 0 < rho) :
    ∀ᶠ T : ℝ in atTop,
      ∀ x : FiniteVector (2 * N + 1),
        0 ≤ quadraticForm
            (paperActualArchimedeanRankTwoTail N L rho T) x ∧
          quadraticForm
              (paperActualArchimedeanRankTwoTail N L rho T) x ≤
            paperArchimedeanRankTwoTailBudget N rho T *
              squaredNorm x := by
  obtain ⟨T0, -, htail⟩ :=
    exists_T0_tendsto_paperActualArchimedeanRankTwoIncrement_and_quadraticForm_bounds
  filter_upwards
      [eventually_ge_atTop (max T0 (rho * N + 1))] with T hT
  have hT0T : T0 ≤ T :=
    (le_max_left T0 (rho * N + 1)).trans hT
  have hPole : rho * N < T := by
    have h := (le_max_right T0 (rho * N + 1)).trans hT
    linarith
  exact (htail N L hN hrho hT0T hPole).2

/-- Every fixed quadratic form of the cutoff-free actual tail tends to zero.
The proof uses the uniform improper-tail bound and the decay `B_T -> 0`. -/
theorem tendsto_quadraticForm_paperActualArchimedeanRankTwoTail_atTop
    (N : ℕ) (L rho : ℝ) (hN : 0 < N) (hrho : 0 < rho)
    (x : FiniteVector (2 * N + 1)) :
    Tendsto
      (fun T =>
        quadraticForm
          (paperActualArchimedeanRankTwoTail N L rho T) x)
      atTop (nhds 0) := by
  have hbounds :=
    eventually_quadraticForm_paperActualArchimedeanRankTwoTail_bounds
      N L rho hN hrho
  have hmajor :
      Tendsto
        (fun T =>
          paperArchimedeanRankTwoTailBudget N rho T * squaredNorm x)
        atTop (nhds 0) := by
    simpa using
      (tendsto_paperArchimedeanRankTwoTailBudget_atTop N rho).mul
        tendsto_const_nhds
  apply squeeze_zero'
  · filter_upwards [hbounds] with T hT
    exact (hT x).1
  · filter_upwards [hbounds] with T hT
    exact (hT x).2
  · exact hmajor

/-- An exact finite `LDL^T` certificate with a verified positive Euclidean
margin remains positive after adding the cutoff-free actual tail. Moreover,
for any fixed `epsilon > 0`, the added quadratic-form contribution is
eventually at most `epsilon * ‖x‖²`, uniformly in `x`. -/
theorem
    eventually_quadraticForm_add_paperActualArchimedeanRankTwoTail_stable_of_exactLDL_margin
    (N : ℕ) (L rho : ℝ) (hN : 0 < N) (hrho : 0 < rho)
    (A : FiniteMatrix (2 * N + 1))
    (certificate : LDLCertificate (2 * N + 1))
    (mu epsilon : ℝ)
    (hreconstruct : A = certificate.reconstruct)
    (hdiagonal : ∀ k, 0 ≤ certificate.diagonal k)
    (hmu : 0 < mu)
    (hmargin : ∀ x,
      mu * squaredNorm x ≤
        quadraticForm certificate.reconstruct x)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ T : ℝ in atTop,
      ∀ x : FiniteVector (2 * N + 1),
        0 ≤ quadraticForm
            (A + paperActualArchimedeanRankTwoTail N L rho T) x ∧
          mu * squaredNorm x ≤
            quadraticForm
              (A + paperActualArchimedeanRankTwoTail N L rho T) x ∧
          (x ≠ 0 →
            0 < quadraticForm
              (A + paperActualArchimedeanRankTwoTail N L rho T) x) ∧
          quadraticForm
              (A + paperActualArchimedeanRankTwoTail N L rho T) x ≤
            quadraticForm A x + epsilon * squaredNorm x := by
  have hbounds :=
    eventually_quadraticForm_paperActualArchimedeanRankTwoTail_bounds
      N L rho hN hrho
  have hbudgetSmall :
      ∀ᶠ T : ℝ in atTop,
        paperArchimedeanRankTwoTailBudget N rho T < epsilon :=
    (tendsto_paperArchimedeanRankTwoTailBudget_atTop N rho).eventually_lt_const
      hepsilon
  have hAnonneg :
      ∀ x : FiniteVector (2 * N + 1), 0 ≤ quadraticForm A x :=
    quadraticForm_nonneg_of_certificate
      A certificate hreconstruct hdiagonal
  filter_upwards [hbounds, hbudgetSmall] with T htail hbudget
  intro x
  have hmarginA :
      mu * squaredNorm x ≤ quadraticForm A x := by
    rw [hreconstruct]
    exact hmargin x
  have htailSmall :
      quadraticForm
          (paperActualArchimedeanRankTwoTail N L rho T) x ≤
        epsilon * squaredNorm x :=
    (htail x).2.trans
      (mul_le_mul_of_nonneg_right hbudget.le (squaredNorm_nonneg x))
  rw [quadraticForm_add]
  have hlower :
      mu * squaredNorm x ≤
        quadraticForm A x +
          quadraticForm
            (paperActualArchimedeanRankTwoTail N L rho T) x :=
    hmarginA.trans
      (le_add_of_nonneg_right (htail x).1)
  refine ⟨add_nonneg (hAnonneg x) (htail x).1, hlower, ?_, ?_⟩
  · intro hx
    exact
      (mul_pos hmu (squaredNorm_pos hx)).trans_le hlower
  · linarith

/-- Concrete threshold form of the exact-`LDL^T` positive-margin stability
result. The threshold depends on all fixed finite data and on `epsilon`; it
is not computed explicitly. -/
theorem
    exists_T_quadraticForm_add_paperActualArchimedeanRankTwoTail_stable_of_exactLDL_margin
    (N : ℕ) (L rho : ℝ) (hN : 0 < N) (hrho : 0 < rho)
    (A : FiniteMatrix (2 * N + 1))
    (certificate : LDLCertificate (2 * N + 1))
    (mu epsilon : ℝ)
    (hreconstruct : A = certificate.reconstruct)
    (hdiagonal : ∀ k, 0 ≤ certificate.diagonal k)
    (hmu : 0 < mu)
    (hmargin : ∀ x,
      mu * squaredNorm x ≤
        quadraticForm certificate.reconstruct x)
    (hepsilon : 0 < epsilon) :
    ∃ T1 : ℝ, ∀ T, T1 ≤ T →
      ∀ x : FiniteVector (2 * N + 1),
        0 ≤ quadraticForm
            (A + paperActualArchimedeanRankTwoTail N L rho T) x ∧
          mu * squaredNorm x ≤
            quadraticForm
              (A + paperActualArchimedeanRankTwoTail N L rho T) x ∧
          (x ≠ 0 →
            0 < quadraticForm
              (A + paperActualArchimedeanRankTwoTail N L rho T) x) ∧
          quadraticForm
              (A + paperActualArchimedeanRankTwoTail N L rho T) x ≤
            quadraticForm A x + epsilon * squaredNorm x :=
  eventually_atTop.1
    (eventually_quadraticForm_add_paperActualArchimedeanRankTwoTail_stable_of_exactLDL_margin
      N L rho hN hrho A certificate mu epsilon
        hreconstruct hdiagonal hmu hmargin hepsilon)

/-- Any fixed strict negative witness for the finite matrix remains negative
after adding the cutoff-free actual tail once the lower cutoff is large
enough. This removes the `B_T` hypothesis from the caller by using
`B_T -> 0`. -/
theorem
    eventually_quadraticForm_add_paperActualArchimedeanRankTwoTail_neg_of_witness
    (N : ℕ) (L rho : ℝ) (hN : 0 < N) (hrho : 0 < rho)
    (A : FiniteMatrix (2 * N + 1))
    (x : FiniteVector (2 * N + 1))
    (hnegative : quadraticForm A x < 0) :
    ∀ᶠ T : ℝ in atTop,
      quadraticForm
        (A + paperActualArchimedeanRankTwoTail N L rho T) x < 0 := by
  have hbounds :=
    eventually_quadraticForm_paperActualArchimedeanRankTwoTail_bounds
      N L rho hN hrho
  have hscaled :
      Tendsto
        (fun T =>
          paperArchimedeanRankTwoTailBudget N rho T * squaredNorm x)
        atTop (nhds 0) := by
    simpa using
      (tendsto_paperArchimedeanRankTwoTailBudget_atTop N rho).mul
        tendsto_const_nhds
  have hsmall :
      ∀ᶠ T : ℝ in atTop,
        paperArchimedeanRankTwoTailBudget N rho T * squaredNorm x <
          -quadraticForm A x :=
    hscaled.eventually_lt_const (neg_pos.mpr hnegative)
  filter_upwards [hbounds, hsmall] with T htail hsmallT
  rw [quadraticForm_add]
  linarith [(htail x).2]

/-- Concrete threshold form of cutoff-free negative-witness stability. The
threshold is non-explicit and is only asserted for the fixed finite data. -/
theorem
    exists_T_quadraticForm_add_paperActualArchimedeanRankTwoTail_neg_of_witness
    (N : ℕ) (L rho : ℝ) (hN : 0 < N) (hrho : 0 < rho)
    (A : FiniteMatrix (2 * N + 1))
    (x : FiniteVector (2 * N + 1))
    (hnegative : quadraticForm A x < 0) :
    ∃ T1 : ℝ, ∀ T, T1 ≤ T →
      quadraticForm
        (A + paperActualArchimedeanRankTwoTail N L rho T) x < 0 :=
  eventually_atTop.1
    (eventually_quadraticForm_add_paperActualArchimedeanRankTwoTail_neg_of_witness
      N L rho hN hrho A x hnegative)

end WeilExtremalKernels
