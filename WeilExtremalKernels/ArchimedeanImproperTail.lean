import WeilExtremalKernels.ArchimedeanActualTail

/-!
# The cutoff-free finite archimedean tail

This module constructs the entrywise improper integral of the actual
Guinand-Weil rank-two density. It proves that the finite increments with
upper endpoint `R` converge to this matrix as `R -> +infinity`, and transfers
the nonnegativity and explicit `B_T` bound to the limit.

The starting threshold remains non-explicit. This is a finite-dimensional
archimedean-tail result; it does not transfer the finite dictionary to the
infinite-dimensional Weil criterion.
-/

namespace WeilExtremalKernels

open Filter MeasureTheory Set
open scoped BigOperators Topology

/-- The cutoff-free finite matrix obtained by integrating the actual
archimedean rank-two density from `T` to positive infinity. -/
noncomputable def paperActualArchimedeanRankTwoTail
    (N : ℕ) (L rho T : ℝ) : FiniteMatrix (2 * N + 1) :=
  fun i j =>
    ∫ r in Ioi T,
      paperArchimedeanRankTwoDensity N
        (paperArchimedeanWeight L rho r) rho r i j

/-- A single entry of the actual rank-two density is controlled by the same
logarithmic envelope used for the operator budget. -/
theorem norm_paperActualArchimedeanRankTwoDensity_entry_le_logEnvelope
    (N : ℕ) {L rho r : ℝ}
    (hrho : 0 < rho) (hPole : rho * N < r)
    (hh0 : 0 ≤ archimedeanHPlus r)
    (hhlog : archimedeanHPlus r ≤ Real.log r)
    (i j : Fin (2 * N + 1)) :
    ‖paperArchimedeanRankTwoDensity N
        (paperArchimedeanWeight L rho r) rho r i j‖ ≤
      paperArchimedeanRankTwoLogEnvelope N rho r := by
  let q : ℝ := rho / (r - rho * N)
  have hq : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hrho.le (sub_pos.mpr hPole).le
  have hsqPlus (k : Fin (2 * N + 1)) :
      (paperCauchyPlusVector N rho r k) ^ 2 ≤ q ^ 2 := by
    simpa only [paperCauchyPlusVector, q] using
      (cauchyTailVector_sq_le
        (centeredIndexCoordinate N) hrho hPole
        (abs_centeredIndexCoordinate_le N) k).1
  have hsqMinus (k : Fin (2 * N + 1)) :
      (paperCauchyMinusVector N rho r k) ^ 2 ≤ q ^ 2 := by
    simpa only [paperCauchyMinusVector, q] using
      (cauchyTailVector_sq_le
        (centeredIndexCoordinate N) hrho hPole
        (abs_centeredIndexCoordinate_le N) k).2
  have habsPlus (k : Fin (2 * N + 1)) :
      |paperCauchyPlusVector N rho r k| ≤ q := by
    apply (sq_le_sq₀ (abs_nonneg _) hq).1
    simpa only [sq_abs] using hsqPlus k
  have habsMinus (k : Fin (2 * N + 1)) :
      |paperCauchyMinusVector N rho r k| ≤ q := by
    apply (sq_le_sq₀ (abs_nonneg _) hq).1
    simpa only [sq_abs] using hsqMinus k
  have hpair :
      |paperCauchyPlusVector N rho r i *
            paperCauchyPlusVector N rho r j +
          paperCauchyMinusVector N rho r i *
            paperCauchyMinusVector N rho r j| ≤
        2 * q ^ 2 := by
    calc
      |paperCauchyPlusVector N rho r i *
              paperCauchyPlusVector N rho r j +
            paperCauchyMinusVector N rho r i *
              paperCauchyMinusVector N rho r j| ≤
          |paperCauchyPlusVector N rho r i *
              paperCauchyPlusVector N rho r j| +
            |paperCauchyMinusVector N rho r i *
              paperCauchyMinusVector N rho r j| :=
        abs_add_le _ _
      _ =
          |paperCauchyPlusVector N rho r i| *
              |paperCauchyPlusVector N rho r j| +
            |paperCauchyMinusVector N rho r i| *
              |paperCauchyMinusVector N rho r j| := by
        rw [abs_mul, abs_mul]
      _ ≤ q * q + q * q := by
        exact add_le_add
          (mul_le_mul (habsPlus i) (habsPlus j) (abs_nonneg _) hq)
          (mul_le_mul (habsMinus i) (habsMinus j) (abs_nonneg _) hq)
      _ = 2 * q ^ 2 := by ring
  have hweight :
      0 ≤ paperArchimedeanWeight L rho r :=
    paperArchimedeanWeight_nonneg hrho hh0
  have hn : (1 : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (2 * N))
  have hentryBudget :
      ‖paperArchimedeanRankTwoDensity N
          (paperArchimedeanWeight L rho r) rho r i j‖ ≤
        paperArchimedeanRankTwoPointwiseBudget N
          (paperArchimedeanWeight L rho) rho r := by
    unfold paperArchimedeanRankTwoDensity weightedRankTwoGramMatrix
      rankTwoGramMatrix rankOneGramMatrix
      paperArchimedeanRankTwoPointwiseBudget
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hweight]
    calc
      paperArchimedeanWeight L rho r *
          |paperCauchyPlusVector N rho r i *
                paperCauchyPlusVector N rho r j +
              paperCauchyMinusVector N rho r i *
                paperCauchyMinusVector N rho r j| ≤
          paperArchimedeanWeight L rho r * (2 * q ^ 2) :=
        mul_le_mul_of_nonneg_left hpair hweight
      _ ≤ paperArchimedeanWeight L rho r *
          (2 * ((2 * N + 1 : ℕ) : ℝ) *
            (rho / (r - rho * N)) ^ 2) := by
        dsimp [q]
        gcongr
        nlinarith [sq_nonneg (rho / (r - rho * N))]
  exact hentryBudget.trans
    (paperArchimedeanRankTwoPointwiseBudget_le_log_envelope
      N hrho hh0 hhlog)

/-- Above a tail on which the `h_+` bounds hold, every matrix entry of the
actual rank-two density is integrable on `Ioi T`. -/
theorem integrableOn_Ioi_paperActualArchimedeanRankTwoDensity_entry
    (N : ℕ) {L rho T : ℝ}
    (hN : 0 < N) (hrho : 0 < rho)
    (hT : rho * N < T) (hT1 : 1 ≤ T)
    (hh : ∀ r, T ≤ r →
      0 ≤ archimedeanHPlus r ∧ archimedeanHPlus r ≤ Real.log r)
    (i j : Fin (2 * N + 1)) :
    IntegrableOn
      (fun r =>
        paperArchimedeanRankTwoDensity N
          (paperArchimedeanWeight L rho r) rho r i j)
      (Ioi T) := by
  have henv :=
    integrableOn_Ioi_paperArchimedeanRankTwoLogEnvelope
      N hN hrho hT hT1
  apply Integrable.mono' henv
  · apply Measurable.aestronglyMeasurable
    have hw : Measurable (paperArchimedeanWeight L rho) :=
      (continuous_paperArchimedeanWeight L rho).measurable
    have hp (k : Fin (2 * N + 1)) :
        Measurable (paperCauchyPlusVector N rho · k) := by
      unfold paperCauchyPlusVector cauchyTailPlusVector
      exact ((measurable_id.div_const rho).sub measurable_const).inv
    have hm (k : Fin (2 * N + 1)) :
        Measurable (paperCauchyMinusVector N rho · k) := by
      unfold paperCauchyMinusVector cauchyTailMinusVector
      exact ((measurable_id.div_const rho).add measurable_const).inv
    unfold paperArchimedeanRankTwoDensity weightedRankTwoGramMatrix
      rankTwoGramMatrix rankOneGramMatrix
    exact hw.mul ((hp i).mul (hp j) |>.add ((hm i).mul (hm j)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact norm_paperActualArchimedeanRankTwoDensity_entry_le_logEnvelope
      N hrho (hT.trans hr) (hh r hr.le).1 (hh r hr.le).2 i j

/-- The finite actual increments converge entrywise to the cutoff-free
matrix tail. -/
theorem tendsto_paperActualArchimedeanRankTwoIncrement_entry_atTop
    (N : ℕ) {L rho T : ℝ}
    (hN : 0 < N) (hrho : 0 < rho)
    (hT : rho * N < T) (hT1 : 1 ≤ T)
    (hh : ∀ r, T ≤ r →
      0 ≤ archimedeanHPlus r ∧ archimedeanHPlus r ≤ Real.log r)
    (i j : Fin (2 * N + 1)) :
    Tendsto
      (fun R =>
        paperActualArchimedeanRankTwoIncrement N L rho T R i j)
      atTop
      (nhds (paperActualArchimedeanRankTwoTail N L rho T i j)) := by
  have hInt :=
    integrableOn_Ioi_paperActualArchimedeanRankTwoDensity_entry
      N (L := L) hN hrho hT hT1 hh i j
  simpa only [paperActualArchimedeanRankTwoIncrement,
    paperArchimedeanRankTwoIncrement, intervalIntegratedMatrix,
    paperActualArchimedeanRankTwoTail] using
    (intervalIntegral_tendsto_integral_Ioi T hInt tendsto_id)

/-- The finite actual increments converge as finite matrices to the
cutoff-free tail. -/
theorem tendsto_paperActualArchimedeanRankTwoIncrement_atTop
    (N : ℕ) {L rho T : ℝ}
    (hN : 0 < N) (hrho : 0 < rho)
    (hT : rho * N < T) (hT1 : 1 ≤ T)
    (hh : ∀ r, T ≤ r →
      0 ≤ archimedeanHPlus r ∧ archimedeanHPlus r ≤ Real.log r) :
    Tendsto
      (fun R => paperActualArchimedeanRankTwoIncrement N L rho T R)
      atTop
      (nhds (paperActualArchimedeanRankTwoTail N L rho T)) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  exact tendsto_paperActualArchimedeanRankTwoIncrement_entry_atTop
    N hN hrho hT hT1 hh i j

/-- Quadratic forms of the finite increments converge to the quadratic form
of the cutoff-free matrix tail. -/
theorem tendsto_quadraticForm_paperActualArchimedeanRankTwoIncrement_atTop
    (N : ℕ) {L rho T : ℝ}
    (hN : 0 < N) (hrho : 0 < rho)
    (hT : rho * N < T) (hT1 : 1 ≤ T)
    (hh : ∀ r, T ≤ r →
      0 ≤ archimedeanHPlus r ∧ archimedeanHPlus r ≤ Real.log r)
    (x : FiniteVector (2 * N + 1)) :
    Tendsto
      (fun R =>
        quadraticForm
          (paperActualArchimedeanRankTwoIncrement N L rho T R) x)
      atTop
      (nhds
        (quadraticForm
          (paperActualArchimedeanRankTwoTail N L rho T) x)) := by
  unfold quadraticForm
  apply tendsto_finset_sum
  intro i _
  apply tendsto_finset_sum
  intro j _
  exact
    ((tendsto_const_nhds.mul
      (tendsto_paperActualArchimedeanRankTwoIncrement_entry_atTop
        N hN hrho hT hT1 hh i j)).mul tendsto_const_nhds)

/-- Beyond one common threshold, the finite actual increments converge to a
cutoff-free matrix whose quadratic form is nonnegative and bounded by the
same explicit scalar budget `B_T`. -/
theorem
    exists_T0_tendsto_paperActualArchimedeanRankTwoIncrement_and_quadraticForm_bounds :
    ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ (N : ℕ) (L : ℝ) {rho T : ℝ},
        0 < N → 0 < rho → T0 ≤ T → rho * N < T →
        Tendsto
          (fun R =>
            paperActualArchimedeanRankTwoIncrement N L rho T R)
          atTop
          (nhds (paperActualArchimedeanRankTwoTail N L rho T)) ∧
        ∀ x : FiniteVector (2 * N + 1),
          0 ≤ quadraticForm
              (paperActualArchimedeanRankTwoTail N L rho T) x ∧
            quadraticForm
                (paperActualArchimedeanRankTwoTail N L rho T) x ≤
              paperArchimedeanRankTwoTailBudget N rho T *
                squaredNorm x := by
  obtain ⟨Th, hTh1, hTh⟩ :=
    exists_one_le_eventually_archimedeanHPlus_bounds
  obtain ⟨Tb, hTb1, hTb⟩ :=
    exists_T0_quadraticForm_paperActualArchimedeanRankTwoIncrement_le_tailBudget
  refine ⟨max Th Tb, hTh1.trans (le_max_left _ _), ?_⟩
  intro N L rho T hN hrho hT0T hPole
  have hThT : Th ≤ T := (le_max_left Th Tb).trans hT0T
  have hTbT : Tb ≤ T := (le_max_right Th Tb).trans hT0T
  have hT1 : 1 ≤ T := hTh1.trans hThT
  have hh :
      ∀ r, T ≤ r →
        0 ≤ archimedeanHPlus r ∧
          archimedeanHPlus r ≤ Real.log r := by
    intro r hr
    exact hTh r (hThT.trans hr)
  have hmatrix :=
    tendsto_paperActualArchimedeanRankTwoIncrement_atTop
      N (L := L) hN hrho hPole hT1 hh
  refine ⟨hmatrix, ?_⟩
  intro x
  have hqf :=
    tendsto_quadraticForm_paperActualArchimedeanRankTwoIncrement_atTop
      N (L := L) hN hrho hPole hT1 hh x
  constructor
  · apply ge_of_tendsto hqf
    filter_upwards [eventually_ge_atTop T] with R hTR
    unfold paperActualArchimedeanRankTwoIncrement
    exact quadraticForm_paperArchimedeanRankTwoIncrement_nonneg
      N hTR (continuous_paperArchimedeanWeight L rho).continuousOn
      (fun r hr =>
        paperArchimedeanWeight_nonneg hrho (hh r hr.1).1)
      hrho hPole x
  · apply le_of_tendsto hqf
    filter_upwards [eventually_ge_atTop T] with R hTR
    exact hTb N L hN hrho hTbT hPole hTR x

/-- Exact finite `LDL^T` positivity transfers through the cutoff-free actual
archimedean tail. -/
theorem
    exists_T0_quadraticForm_add_paperActualArchimedeanRankTwoTail_nonneg_of_certificate :
    ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ (N : ℕ) (L : ℝ) {rho T : ℝ},
        0 < N → 0 < rho → T0 ≤ T → rho * N < T →
        ∀ (A : FiniteMatrix (2 * N + 1))
          (certificate : LDLCertificate (2 * N + 1)),
          A = certificate.reconstruct →
          (∀ k, 0 ≤ certificate.diagonal k) →
          ∀ x : FiniteVector (2 * N + 1),
            0 ≤ quadraticForm
              (A + paperActualArchimedeanRankTwoTail N L rho T) x := by
  obtain ⟨T0, hT01, htail⟩ :=
    exists_T0_tendsto_paperActualArchimedeanRankTwoIncrement_and_quadraticForm_bounds
  refine ⟨T0, hT01, ?_⟩
  intro N L rho T hN hrho hT0T hPole A certificate
    hreconstruct hdiagonal
  exact quadraticForm_nonneg_add_of_tail_nonneg
    A (paperActualArchimedeanRankTwoTail N L rho T)
    (quadraticForm_nonneg_of_certificate
      A certificate hreconstruct hdiagonal)
    (fun x => (htail N L hN hrho hT0T hPole).2 x |>.1)

/-- A finite negative witness that clears `B_T` remains negative after adding
the entire cutoff-free actual archimedean tail. -/
theorem
    exists_T0_quadraticForm_add_paperActualArchimedeanRankTwoTail_neg_of_tailBudget :
    ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ (N : ℕ) (L : ℝ) {rho T : ℝ},
        0 < N → 0 < rho → T0 ≤ T → rho * N < T →
        ∀ (A : FiniteMatrix (2 * N + 1))
          (x : FiniteVector (2 * N + 1)),
          quadraticForm A x <
              -paperArchimedeanRankTwoTailBudget N rho T * squaredNorm x →
          quadraticForm
              (A + paperActualArchimedeanRankTwoTail N L rho T) x < 0 := by
  obtain ⟨T0, hT01, htail⟩ :=
    exists_T0_tendsto_paperActualArchimedeanRankTwoIncrement_and_quadraticForm_bounds
  refine ⟨T0, hT01, ?_⟩
  intro N L rho T hN hrho hT0T hPole A x hfinite
  exact quadraticForm_neg_add_of_tail_upper
    A (paperActualArchimedeanRankTwoTail N L rho T) x
    (paperArchimedeanRankTwoTailBudget N rho T) hfinite
    ((htail N L hN hrho hT0T hPole).2 x |>.2)

end WeilExtremalKernels
