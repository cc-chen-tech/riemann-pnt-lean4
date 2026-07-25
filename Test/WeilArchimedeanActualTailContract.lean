import WeilExtremalKernels.ArchimedeanActualTail

open WeilExtremalKernels

example
    (N : ℕ) {L rho r : ℝ}
    (hrho : 0 < rho)
    (hh0 : 0 ≤ archimedeanHPlus r)
    (hhlog : archimedeanHPlus r ≤ Real.log r) :
    paperArchimedeanRankTwoPointwiseBudget N
        (paperArchimedeanWeight L rho) rho r ≤
      paperArchimedeanRankTwoLogEnvelope N rho r :=
  paperArchimedeanRankTwoPointwiseBudget_le_log_envelope
    N hrho hh0 hhlog

example :
    ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ (N : ℕ) (L : ℝ) {rho a b : ℝ},
        0 < rho → T0 ≤ a → rho * N < a → a ≤ b →
        ∀ x : FiniteVector (2 * N + 1),
          0 ≤ quadraticForm
            (paperActualArchimedeanRankTwoIncrement N L rho a b) x :=
  exists_T0_quadraticForm_paperActualArchimedeanRankTwoIncrement_nonneg

example :
    ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ (N : ℕ) (L : ℝ) {rho a b : ℝ},
        0 < rho → T0 ≤ a → rho * N < a → a ≤ b →
        ∀ x : FiniteVector (2 * N + 1),
          quadraticForm
              (paperActualArchimedeanRankTwoIncrement N L rho a b) x ≤
            (∫ r in a..b,
              paperArchimedeanRankTwoPointwiseBudget N
                (paperArchimedeanWeight L rho) rho r) *
              squaredNorm x :=
  exists_T0_quadraticForm_paperActualArchimedeanRankTwoIncrement_le

example
    (N : ℕ) {rho T : ℝ}
    (hN : 0 < N) (hrho : 0 < rho)
    (hT : rho * N < T) (hT1 : 1 ≤ T) :
    ∫ r in Set.Ioi T, paperArchimedeanRankTwoLogEnvelope N rho r =
      paperArchimedeanRankTwoTailBudget N rho T :=
  integral_Ioi_paperArchimedeanRankTwoLogEnvelope
    N hN hrho hT hT1

example (N : ℕ) (rho : ℝ) :
    Filter.Tendsto (paperArchimedeanRankTwoTailBudget N rho)
      Filter.atTop (nhds 0) :=
  tendsto_paperArchimedeanRankTwoTailBudget_atTop N rho

example :
    ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ (N : ℕ) (L : ℝ) {rho T R : ℝ},
        0 < N → 0 < rho → T0 ≤ T → rho * N < T → T ≤ R →
        ∀ x : FiniteVector (2 * N + 1),
          quadraticForm
              (paperActualArchimedeanRankTwoIncrement N L rho T R) x ≤
            paperArchimedeanRankTwoTailBudget N rho T * squaredNorm x :=
  exists_T0_quadraticForm_paperActualArchimedeanRankTwoIncrement_le_tailBudget

example :
    ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ (N : ℕ) (L : ℝ) {rho T R : ℝ},
        0 < rho → T0 ≤ T → rho * N < T → T ≤ R →
        ∀ (A : FiniteMatrix (2 * N + 1))
          (certificate : LDLCertificate (2 * N + 1)),
          A = certificate.reconstruct →
          (∀ k, 0 ≤ certificate.diagonal k) →
          ∀ x : FiniteVector (2 * N + 1),
            0 ≤ quadraticForm
              (A + paperActualArchimedeanRankTwoIncrement N L rho T R) x :=
  exists_T0_quadraticForm_add_paperActualArchimedeanRankTwoIncrement_nonneg_of_certificate

example :
    ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ (N : ℕ) (L : ℝ) {rho T R : ℝ},
        0 < N → 0 < rho → T0 ≤ T → rho * N < T → T ≤ R →
        ∀ (A : FiniteMatrix (2 * N + 1))
          (x : FiniteVector (2 * N + 1)),
          quadraticForm A x <
              -paperArchimedeanRankTwoTailBudget N rho T * squaredNorm x →
          quadraticForm
              (A + paperActualArchimedeanRankTwoIncrement N L rho T R) x <
            0 :=
  exists_T0_quadraticForm_add_paperActualArchimedeanRankTwoIncrement_neg_of_tailBudget
