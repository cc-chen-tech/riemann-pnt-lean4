import WeilExtremalKernels.ArchimedeanImproperTailDecay

open Filter WeilExtremalKernels

example
    (N : ℕ) (L rho : ℝ) (hN : 0 < N) (hrho : 0 < rho)
    (i j : Fin (2 * N + 1)) :
    ∀ᶠ T : ℝ in atTop,
      ‖paperActualArchimedeanRankTwoTail N L rho T i j‖ ≤
        paperArchimedeanRankTwoTailBudget N rho T :=
  eventually_norm_paperActualArchimedeanRankTwoTail_entry_le_tailBudget
    N L rho hN hrho i j

example
    (N : ℕ) (L rho : ℝ) (hN : 0 < N) (hrho : 0 < rho)
    (i j : Fin (2 * N + 1)) :
    Tendsto
      (fun T => paperActualArchimedeanRankTwoTail N L rho T i j)
      atTop (nhds 0) :=
  tendsto_paperActualArchimedeanRankTwoTail_entry_atTop
    N L rho hN hrho i j

example
    (N : ℕ) (L rho : ℝ) (hN : 0 < N) (hrho : 0 < rho) :
    Tendsto
      (paperActualArchimedeanRankTwoTail N L rho)
      atTop (nhds 0) :=
  tendsto_paperActualArchimedeanRankTwoTail_atTop
    N L rho hN hrho

example
    (N : ℕ) (L rho : ℝ) (hN : 0 < N) (hrho : 0 < rho) :
    ∀ᶠ T : ℝ in atTop,
      ∀ x : FiniteVector (2 * N + 1),
        0 ≤ quadraticForm
            (paperActualArchimedeanRankTwoTail N L rho T) x ∧
          quadraticForm
              (paperActualArchimedeanRankTwoTail N L rho T) x ≤
            paperArchimedeanRankTwoTailBudget N rho T *
              squaredNorm x :=
  eventually_quadraticForm_paperActualArchimedeanRankTwoTail_bounds
    N L rho hN hrho

example
    (N : ℕ) (L rho : ℝ) (hN : 0 < N) (hrho : 0 < rho)
    (x : FiniteVector (2 * N + 1)) :
    Tendsto
      (fun T =>
        quadraticForm
          (paperActualArchimedeanRankTwoTail N L rho T) x)
      atTop (nhds 0) :=
  tendsto_quadraticForm_paperActualArchimedeanRankTwoTail_atTop
    N L rho hN hrho x

example
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
            quadraticForm A x + epsilon * squaredNorm x :=
  eventually_quadraticForm_add_paperActualArchimedeanRankTwoTail_stable_of_exactLDL_margin
    N L rho hN hrho A certificate mu epsilon
      hreconstruct hdiagonal hmu hmargin hepsilon

example
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
  exists_T_quadraticForm_add_paperActualArchimedeanRankTwoTail_stable_of_exactLDL_margin
    N L rho hN hrho A certificate mu epsilon
      hreconstruct hdiagonal hmu hmargin hepsilon

example
    (N : ℕ) (L rho : ℝ) (hN : 0 < N) (hrho : 0 < rho)
    (A : FiniteMatrix (2 * N + 1))
    (x : FiniteVector (2 * N + 1))
    (hnegative : quadraticForm A x < 0) :
    ∀ᶠ T : ℝ in atTop,
      quadraticForm
        (A + paperActualArchimedeanRankTwoTail N L rho T) x < 0 :=
  eventually_quadraticForm_add_paperActualArchimedeanRankTwoTail_neg_of_witness
    N L rho hN hrho A x hnegative

example
    (N : ℕ) (L rho : ℝ) (hN : 0 < N) (hrho : 0 < rho)
    (A : FiniteMatrix (2 * N + 1))
    (x : FiniteVector (2 * N + 1))
    (hnegative : quadraticForm A x < 0) :
    ∃ T1 : ℝ, ∀ T, T1 ≤ T →
      quadraticForm
        (A + paperActualArchimedeanRankTwoTail N L rho T) x < 0 :=
  exists_T_quadraticForm_add_paperActualArchimedeanRankTwoTail_neg_of_witness
    N L rho hN hrho A x hnegative
