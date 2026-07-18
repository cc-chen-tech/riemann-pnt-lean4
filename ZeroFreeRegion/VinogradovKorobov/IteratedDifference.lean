import ZeroFreeRegion.VinogradovKorobov.ExponentialSum
import ZeroFreeRegion.VinogradovKorobov.VanDerCorputRange

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- The signed finite difference naturally produced by the autocorrelation
`e(f(n)) * conj(e(f(n+h)))`. -/
def phaseDifference (h : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  f n - f (n + h)

/-- Iterated signed finite differences.  The head of the list is the outermost
difference, matching successive van der Corput A-process steps. -/
def iteratedPhaseDifference : List ℕ → (ℕ → ℝ) → ℕ → ℝ
  | [], f => f
  | h :: shifts, f => phaseDifference h (iteratedPhaseDifference shifts f)

/-- The normalized squared-norm envelope produced by one A-process step when
the `ell`-th differenced sum is bounded by `B ell`. -/
noncomputable def aProcessSquaredBound
    (B : ℕ → ℝ) (N L : ℕ) : ℝ :=
  (((N : ℝ) + ((L : ℝ) - 1)) * N) / L +
    (2 * ((N : ℝ) + ((L : ℝ) - 1)) *
      ∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * B ell) / (L : ℝ) ^ 2

@[simp] lemma iteratedPhaseDifference_nil (f : ℕ → ℝ) :
    iteratedPhaseDifference [] f = f := rfl

@[simp] lemma iteratedPhaseDifference_cons
    (h : ℕ) (shifts : List ℕ) (f : ℕ → ℝ) :
    iteratedPhaseDifference (h :: shifts) f =
      phaseDifference h (iteratedPhaseDifference shifts f) := rfl

/-- Autocorrelation adds one finite-difference direction to the phase. -/
lemma phaseTerm_mul_conj_shift_eq_phaseTerm_difference
    (f : ℕ → ℝ) (n h : ℕ) :
    phaseTerm f n * (starRingEnd ℂ) (phaseTerm f (n + h)) =
      phaseTerm (phaseDifference h f) n := by
  simpa only [phaseTerm, phaseDifference] using
    phaseTerm_mul_conj_shift f n h

/-- Signed finite differences commute, so the order of A-process directions
does not affect the resulting phase. -/
lemma phaseDifference_commute (f : ℕ → ℝ) (h k n : ℕ) :
    phaseDifference h (phaseDifference k f) n =
      phaseDifference k (phaseDifference h f) n := by
  unfold phaseDifference
  rw [show n + h + k = n + k + h by omega]
  ring

/-- The autocorrelation sum of an iterated phase is exactly the exponential
sum for the phase with one additional finite difference. -/
lemma iteratedPhase_correlation_eq
    (f : ℕ → ℝ) (shifts : List ℕ) (ell N : ℕ) :
    (∑ n ∈ Finset.range (N - ell),
        phaseTerm (iteratedPhaseDifference shifts f) n *
          (starRingEnd ℂ)
            (phaseTerm (iteratedPhaseDifference shifts f) (n + ell))) =
      ∑ n ∈ Finset.range (N - ell),
        phaseTerm (iteratedPhaseDifference (ell :: shifts) f) n := by
  apply Finset.sum_congr rfl
  intro n hn
  exact phaseTerm_mul_conj_shift_eq_phaseTerm_difference
    (iteratedPhaseDifference shifts f) n ell

/-- Recursive van der Corput A-process: a quantitative bound for every
one-more-differenced phase controls the current iterated phase sum. -/
theorem vanDerCorputIteratedPhaseOfDifferenceBounds
    (f : ℕ → ℝ) (shifts : List ℕ) (B : ℕ → ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hcor : ∀ ell ∈ Finset.Icc 1 (L - 1),
      ‖∑ n ∈ Finset.range (N - ell),
        phaseTerm (iteratedPhaseDifference (ell :: shifts) f) n‖ ≤ B ell) :
    (L : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.range N,
          phaseTerm (iteratedPhaseDifference shifts f) n‖ ^ 2 ≤
      (L : ℝ) * ((N : ℝ) + ((L : ℝ) - 1)) * N +
        2 * ((N : ℝ) + ((L : ℝ) - 1)) *
          ∑ ell ∈ Finset.Icc 1 (L - 1),
            ((L : ℝ) - (ell : ℝ)) * B ell := by
  have hbase := vanDerCorputRangeOfCorrelationBounds
    (fun n ↦ phaseTerm (iteratedPhaseDifference shifts f) n)
    B N L hL hLN (by
      intro ell hell
      rw [iteratedPhase_correlation_eq]
      exact hcor ell hell)
  have hdiag :
      (∑ n ∈ Finset.range N,
        ‖phaseTerm (iteratedPhaseDifference shifts f) n‖ ^ 2) = (N : ℝ) := by
    simp only [norm_phaseTerm, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  rw [hdiag] at hbase
  exact hbase

/-- Normalized one-step A-process bound after division by the square of the
differencing length. -/
theorem norm_iteratedPhase_sum_sq_le_aProcess
    (f : ℕ → ℝ) (shifts : List ℕ) (B : ℕ → ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hcor : ∀ ell ∈ Finset.Icc 1 (L - 1),
      ‖∑ n ∈ Finset.range (N - ell),
        phaseTerm (iteratedPhaseDifference (ell :: shifts) f) n‖ ≤ B ell) :
    ‖∑ n ∈ Finset.range N,
        phaseTerm (iteratedPhaseDifference shifts f) n‖ ^ 2 ≤
      aProcessSquaredBound B N L := by
  have hbase := vanDerCorputIteratedPhaseOfDifferenceBounds
    f shifts B N L hL hLN hcor
  have hLpos : 0 < (L : ℝ) := Nat.cast_pos.mpr (by omega)
  calc
    ‖∑ n ∈ Finset.range N,
        phaseTerm (iteratedPhaseDifference shifts f) n‖ ^ 2 =
        ((L : ℝ) ^ 2 *
          ‖∑ n ∈ Finset.range N,
            phaseTerm (iteratedPhaseDifference shifts f) n‖ ^ 2) /
          (L : ℝ) ^ 2 := by field_simp
    _ ≤ ((L : ℝ) * ((N : ℝ) + ((L : ℝ) - 1)) * N +
          2 * ((N : ℝ) + ((L : ℝ) - 1)) *
            ∑ ell ∈ Finset.Icc 1 (L - 1),
              ((L : ℝ) - (ell : ℝ)) * B ell) /
          (L : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hbase (sq_nonneg (L : ℝ))
    _ = aProcessSquaredBound B N L := by
      unfold aProcessSquaredBound
      field_simp

/-- Variant accepting squared bounds for the next-level sums. -/
theorem norm_iteratedPhase_sum_sq_le_aProcess_of_sq_bounds
    (f : ℕ → ℝ) (shifts : List ℕ) (Q : ℕ → ℝ) (N L : ℕ)
    (hL : 1 ≤ L) (hLN : L ≤ N)
    (hcorSq : ∀ ell ∈ Finset.Icc 1 (L - 1),
      ‖∑ n ∈ Finset.range (N - ell),
        phaseTerm (iteratedPhaseDifference (ell :: shifts) f) n‖ ^ 2 ≤ Q ell) :
    ‖∑ n ∈ Finset.range N,
        phaseTerm (iteratedPhaseDifference shifts f) n‖ ^ 2 ≤
      aProcessSquaredBound (fun ell ↦ Real.sqrt (Q ell)) N L := by
  apply norm_iteratedPhase_sum_sq_le_aProcess
    f shifts (fun ell ↦ Real.sqrt (Q ell)) N L hL hLN
  intro ell hell
  exact Real.le_sqrt_of_sq_le (hcorSq ell hell)

/-- Two explicit recursive A-process steps.  The second-level bounds are
normalized first and then transferred through a square root into the outer
step. -/
theorem norm_iteratedPhase_sum_sq_le_two_aProcess
    (f : ℕ → ℝ) (shifts : List ℕ)
    (C : ℕ → ℕ → ℝ) (L₂ : ℕ → ℕ) (N L₁ : ℕ)
    (hL₁ : 1 ≤ L₁) (hL₁N : L₁ ≤ N)
    (hL₂ : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1), 1 ≤ L₂ ell₁)
    (hL₂N : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1), L₂ ell₁ ≤ N - ell₁)
    (hsecond : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1),
      ∀ ell₂ ∈ Finset.Icc 1 (L₂ ell₁ - 1),
        ‖∑ n ∈ Finset.range (N - ell₁ - ell₂),
          phaseTerm
            (iteratedPhaseDifference (ell₂ :: ell₁ :: shifts) f) n‖ ≤
          C ell₁ ell₂) :
    ‖∑ n ∈ Finset.range N,
        phaseTerm (iteratedPhaseDifference shifts f) n‖ ^ 2 ≤
      aProcessSquaredBound
        (fun ell₁ ↦ Real.sqrt
          (aProcessSquaredBound (C ell₁) (N - ell₁) (L₂ ell₁)))
        N L₁ := by
  apply norm_iteratedPhase_sum_sq_le_aProcess_of_sq_bounds
    f shifts
    (fun ell₁ ↦ aProcessSquaredBound (C ell₁) (N - ell₁) (L₂ ell₁))
    N L₁ hL₁ hL₁N
  intro ell₁ hell₁
  apply norm_iteratedPhase_sum_sq_le_aProcess
    f (ell₁ :: shifts) (C ell₁) (N - ell₁) (L₂ ell₁)
    (hL₂ ell₁ hell₁) (hL₂N ell₁ hell₁)
  intro ell₂ hell₂
  exact hsecond ell₁ hell₁ ell₂ hell₂

end ZeroFreeRegion.VinogradovKorobov
