import WeilExtremalKernels.ArchimedeanImproperTail

open Filter WeilExtremalKernels

example
    (N : ℕ) {L rho r : ℝ}
    (hrho : 0 < rho) (hPole : rho * N < r)
    (hh0 : 0 ≤ archimedeanHPlus r)
    (hhlog : archimedeanHPlus r ≤ Real.log r)
    (i j : Fin (2 * N + 1)) :
    ‖paperArchimedeanRankTwoDensity N
        (paperArchimedeanWeight L rho r) rho r i j‖ ≤
      paperArchimedeanRankTwoLogEnvelope N rho r :=
  norm_paperActualArchimedeanRankTwoDensity_entry_le_logEnvelope
    N hrho hPole hh0 hhlog i j

example
    (N : ℕ) {L rho T : ℝ}
    (hN : 0 < N) (hrho : 0 < rho)
    (hT : rho * N < T) (hT1 : 1 ≤ T)
    (hh : ∀ r, T ≤ r →
      0 ≤ archimedeanHPlus r ∧ archimedeanHPlus r ≤ Real.log r) :
    Tendsto
      (fun R => paperActualArchimedeanRankTwoIncrement N L rho T R)
      atTop
      (nhds (paperActualArchimedeanRankTwoTail N L rho T)) :=
  tendsto_paperActualArchimedeanRankTwoIncrement_atTop
    N hN hrho hT hT1 hh

example :
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
                squaredNorm x :=
  exists_T0_tendsto_paperActualArchimedeanRankTwoIncrement_and_quadraticForm_bounds

example :
    ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ (N : ℕ) (L : ℝ) {rho T : ℝ},
        0 < N → 0 < rho → T0 ≤ T → rho * N < T →
        ∀ (A : FiniteMatrix (2 * N + 1))
          (certificate : LDLCertificate (2 * N + 1)),
          A = certificate.reconstruct →
          (∀ k, 0 ≤ certificate.diagonal k) →
          ∀ x : FiniteVector (2 * N + 1),
            0 ≤ quadraticForm
              (A + paperActualArchimedeanRankTwoTail N L rho T) x :=
  exists_T0_quadraticForm_add_paperActualArchimedeanRankTwoTail_nonneg_of_certificate

example :
    ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ (N : ℕ) (L : ℝ) {rho T : ℝ},
        0 < N → 0 < rho → T0 ≤ T → rho * N < T →
        ∀ (A : FiniteMatrix (2 * N + 1))
          (x : FiniteVector (2 * N + 1)),
          quadraticForm A x <
              -paperArchimedeanRankTwoTailBudget N rho T * squaredNorm x →
          quadraticForm
              (A + paperActualArchimedeanRankTwoTail N L rho T) x < 0 :=
  exists_T0_quadraticForm_add_paperActualArchimedeanRankTwoTail_neg_of_tailBudget
