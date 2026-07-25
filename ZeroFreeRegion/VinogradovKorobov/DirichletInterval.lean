import ZeroFreeRegion.VinogradovKorobov.DirichletPrefix
import ZeroFreeRegion.VinogradovKorobov.ConstantAProcessSchedule

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- A finite Dirichlet polynomial on the half-open integer interval
`[m, m + N)`. -/
noncomputable def dirichletInterval
    (sigma t : ℝ) (m N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico m (m + N),
    1 / (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t)

private lemma dirichletWeight_le_one
    {sigma : ℝ} (hsigma : 0 ≤ sigma) {n : ℕ} (hn : 1 ≤ n) :
    dirichletWeight sigma n ≤ 1 := by
  have h := Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
    (neg_nonpos.mpr hsigma)
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (n : ℝ) ∈ Set.Ioi 0 by exact Set.mem_Ioi.mpr (by exact_mod_cast hn))
    (by exact_mod_cast hn)
  simpa only [dirichletWeight, Nat.cast_one, Real.one_rpow] using h

/-- The trivial length bound for a positive-start Dirichlet interval in the
closed right half-plane. -/
theorem norm_dirichletInterval_le_length
    (sigma t : ℝ) (m N : ℕ) (hsigma : 0 ≤ sigma) (hm : 0 < m) :
    ‖dirichletInterval sigma t m N‖ ≤ N := by
  rw [dirichletInterval, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  calc
    ‖∑ i ∈ Finset.range N,
        1 / ((m + i : ℕ) : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ≤
        ∑ i ∈ Finset.range N,
          ‖1 / ((m + i : ℕ) : ℂ) ^
            ((sigma : ℂ) + Complex.I * t)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have him : 1 ≤ m + i := by omega
      rw [inv_nat_cpow_eq_dirichletWeight_mul_zetaOscillation
        (by omega : m + i ≠ 0) sigma t]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (dirichletWeight_nonneg sigma (m + i)),
        norm_zetaOscillation, mul_one]
      exact dirichletWeight_le_one hsigma him
    _ = N := by simp

/-- Consecutive Dirichlet intervals concatenate exactly. -/
lemma dirichletInterval_add_length
    (sigma t : ℝ) (m N₁ N₂ : ℕ) :
    dirichletInterval sigma t m (N₁ + N₂) =
      dirichletInterval sigma t m N₁ +
        dirichletInterval sigma t (m + N₁) N₂ := by
  unfold dirichletInterval
  rw [show m + (N₁ + N₂) = (m + N₁) + N₂ by omega]
  exact (Finset.sum_Ico_consecutive
    (fun n ↦ 1 / (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t))
    (m := m) (n := m + N₁) (k := (m + N₁) + N₂)
    (by omega) (by omega)).symm

/-- A long interval of length `q * B` is the sum of `q` consecutive blocks
of length `B`. -/
lemma dirichletInterval_mul_length
    (sigma t : ℝ) (m q B : ℕ) :
    dirichletInterval sigma t m (q * B) =
      ∑ j ∈ Finset.range q,
        dirichletInterval sigma t (m + j * B) B := by
  induction q with
  | zero => simp [dirichletInterval]
  | succ q ih =>
      rw [Nat.succ_mul, dirichletInterval_add_length, ih,
        Finset.sum_range_succ]

/-- Euclidean division splits an arbitrary interval into equal full blocks
and one final remainder block. -/
lemma dirichletInterval_division_blocks
    (sigma t : ℝ) (m N B : ℕ) (_hB : 0 < B) :
    dirichletInterval sigma t m N =
      ∑ j ∈ Finset.range (N / B),
          dirichletInterval sigma t (m + j * B) B +
        dirichletInterval sigma t (m + (N / B) * B) (N % B) := by
  have hsplit := dirichletInterval_add_length sigma t m
    ((N / B) * B) (N % B)
  rw [Nat.div_add_mod'] at hsplit
  rw [dirichletInterval_mul_length] at hsplit
  exact hsplit

/-- The scale-form logarithmic estimate on an interval of exactly `N`
integer terms. -/
theorem norm_dirichletInterval_le_weight_mul_harmonic_of_scale
    (sigma t : ℝ) (m N L : ℕ)
    (hsigma : 0 ≤ sigma) (ht : 0 < t) (hm : 0 < m) (hL : 1 ≤ L)
    (hscale : t * ((L - 1 : ℕ) : ℝ) ≤
      (m : ℝ) * ((m : ℝ) + 2)) :
    ‖dirichletInterval sigma t m N‖ ≤
      dirichletWeight sigma m *
        max (L : ℝ)
          (Real.sqrt (zetaOscillationHarmonicBound t m N L)) := by
  cases N with
  | zero =>
      simp only [dirichletInterval, Nat.add_zero, Finset.Ico_self,
        Finset.sum_empty, norm_zero]
      exact mul_nonneg (dirichletWeight_nonneg sigma m)
        ((Real.sqrt_nonneg _).trans (le_max_right _ _))
  | succ N =>
      have hbound :=
        norm_dirichletBlock_le_weight_mul_harmonic_end_of_scale
          sigma t m N L hsigma ht hm hL hscale
      simpa only [dirichletInterval, Finset.sum_Ico_eq_sum_range,
        Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hbound

/-- Summed harmonic control for a long interval split into equal consecutive
blocks. -/
theorem norm_dirichletInterval_mul_le_sum_harmonic_of_scale
    (sigma t : ℝ) (m q B L : ℕ)
    (hsigma : 0 ≤ sigma) (ht : 0 < t) (hm : 0 < m) (hL : 1 ≤ L)
    (hscale : ∀ j < q,
      t * ((L - 1 : ℕ) : ℝ) ≤
        ((m + j * B : ℕ) : ℝ) * (((m + j * B : ℕ) : ℝ) + 2)) :
    ‖dirichletInterval sigma t m (q * B)‖ ≤
      ∑ j ∈ Finset.range q,
        dirichletWeight sigma (m + j * B) *
          max (L : ℝ)
            (Real.sqrt
              (zetaOscillationHarmonicBound t (m + j * B) B L)) := by
  rw [dirichletInterval_mul_length]
  calc
    ‖∑ j ∈ Finset.range q,
        dirichletInterval sigma t (m + j * B) B‖ ≤
        ∑ j ∈ Finset.range q,
          ‖dirichletInterval sigma t (m + j * B) B‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range q,
        dirichletWeight sigma (m + j * B) *
          max (L : ℝ)
            (Real.sqrt
              (zetaOscillationHarmonicBound t (m + j * B) B L)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply norm_dirichletInterval_le_weight_mul_harmonic_of_scale
        sigma t (m + j * B) B L hsigma ht
      · omega
      · exact hL
      · exact hscale j (Finset.mem_range.mp hj)

/-- First prefix length at which the constant A-process schedule budget is
automatically admissible. -/
def constantAProcessPrefixThreshold (depth h : ℕ) : ℕ :=
  depth * (h - 1) + 1

/-- Uniform prefix estimate obtained from the trivial bound below the
schedule threshold and the explicit arbitrary-depth power bound above it. -/
theorem norm_zetaOscillation_prefix_le_max_constantAProcessExplicitPower
    (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m) (hh : 1 ≤ h)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hscale : ∀ K, constantAProcessPrefixThreshold depth h ≤ K → K ≤ N →
      2 * Real.pi * (h : ℝ) ≤
        zetaAProcessUniformLeafDeltaLower t m K depth *
          (h : ℝ) ^ depth * (K : ℝ)) :
    ∀ K ≤ N,
      ‖∑ n ∈ Finset.range K, zetaOscillation t (m + n)‖ ≤
        max (constantAProcessPrefixThreshold depth h : ℝ)
          (6 * (1 + Real.log h) * (N : ℝ) /
            (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ)) := by
  intro K hKN
  by_cases hthreshold : constantAProcessPrefixThreshold depth h ≤ K
  · have hbudget : depth * (h - 1) < K := by
      unfold constantAProcessPrefixThreshold at hthreshold
      omega
    have hbound := norm_zetaPhase_sum_le_constantAProcessExplicitPower
      t m K depth h ht hm hh hbudget hmajor
      (hscale K hthreshold hKN)
    have hmono :
        6 * (1 + Real.log h) * (K : ℝ) /
            (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ) ≤
          6 * (1 + Real.log h) * (N : ℝ) /
            (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ) := by
      have hlog : 0 ≤ Real.log (h : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hh)
      have hKNreal : (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hKN
      gcongr
    calc
      ‖∑ n ∈ Finset.range K, zetaOscillation t (m + n)‖ =
          ‖∑ n ∈ Finset.range K, phaseTerm (shiftedZetaPhase t m) n‖ := by
        apply congrArg norm
        apply Finset.sum_congr rfl
        intro n hn
        exact (phaseTerm_shiftedZetaPhase t m n).symm
      _ ≤ 6 * (1 + Real.log h) * (K : ℝ) /
            (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ) := hbound
      _ ≤ 6 * (1 + Real.log h) * (N : ℝ) /
            (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ) := hmono
      _ ≤ max (constantAProcessPrefixThreshold depth h : ℝ)
          (6 * (1 + Real.log h) * (N : ℝ) /
            (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ)) := le_max_right _ _
  · have hKthreshold : K ≤ constantAProcessPrefixThreshold depth h := by omega
    calc
      ‖∑ n ∈ Finset.range K, zetaOscillation t (m + n)‖ ≤
          ∑ n ∈ Finset.range K, ‖zetaOscillation t (m + n)‖ := norm_sum_le _ _
      _ = K := by
        simp only [norm_zetaOscillation, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]
      _ ≤ constantAProcessPrefixThreshold depth h := by exact_mod_cast hKthreshold
      _ ≤ max (constantAProcessPrefixThreshold depth h : ℝ)
          (6 * (1 + Real.log h) * (N : ℝ) /
            (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ)) := le_max_left _ _

/-- Abel transfer of the explicit arbitrary-depth prefix bound to a weighted
Dirichlet interval. -/
theorem norm_dirichletInterval_le_weight_mul_constantAProcessExplicitPower
    (sigma t : ℝ) (m N depth h : ℕ)
    (hsigma : 0 ≤ sigma) (ht : 0 < t) (hm : 0 < m) (hh : 1 ≤ h)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hscale : ∀ K, constantAProcessPrefixThreshold depth h ≤ K → K ≤ N →
      2 * Real.pi * (h : ℝ) ≤
        zetaAProcessUniformLeafDeltaLower t m K depth *
          (h : ℝ) ^ depth * (K : ℝ)) :
    ‖dirichletInterval sigma t m N‖ ≤
      dirichletWeight sigma m *
        max (constantAProcessPrefixThreshold depth h : ℝ)
          (6 * (1 + Real.log h) * (N : ℝ) /
            (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ)) := by
  cases N with
  | zero =>
      simp only [dirichletInterval, Nat.add_zero, Finset.Ico_self,
        Finset.sum_empty, norm_zero]
      apply mul_nonneg (dirichletWeight_nonneg sigma m)
      exact (Nat.cast_nonneg _).trans (le_max_left _ _)
  | succ N =>
      rw [dirichletInterval, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left]
      apply norm_dirichletBlock_le_weight_mul sigma t m N
        (max (constantAProcessPrefixThreshold depth h : ℝ)
          (6 * (1 + Real.log h) * ((N + 1 : ℕ) : ℝ) /
            (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ))) hsigma hm
      have hprefix :=
        norm_zetaOscillation_prefix_le_max_constantAProcessExplicitPower
          t m (N + 1) depth h ht hm hh hmajor hscale
      intro k hk
      exact hprefix (k + 1) (by omega)

/-- Long-interval transfer of the explicit arbitrary-depth estimate.  Every
full block is controlled by its own scale hypotheses; the final Euclidean
remainder is bounded trivially by its length. -/
theorem norm_dirichletInterval_le_sum_constantAProcessExplicitPower
    (sigma t : ℝ) (m N B depth h : ℕ)
    (hsigma : 0 ≤ sigma) (ht : 0 < t) (hm : 0 < m)
    (hB : 0 < B) (hh : 1 ≤ h)
    (hmajor : ∀ j < N / B,
      t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
        (((m + j * B : ℕ) : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hscale : ∀ j < N / B, ∀ K,
      constantAProcessPrefixThreshold depth h ≤ K → K ≤ B →
        2 * Real.pi * (h : ℝ) ≤
          zetaAProcessUniformLeafDeltaLower t (m + j * B) K depth *
            (h : ℝ) ^ depth * (K : ℝ)) :
    ‖dirichletInterval sigma t m N‖ ≤
      ∑ j ∈ Finset.range (N / B),
          dirichletWeight sigma (m + j * B) *
            max (constantAProcessPrefixThreshold depth h : ℝ)
              (6 * (1 + Real.log h) * (B : ℝ) /
                (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ)) +
        (N % B : ℕ) := by
  rw [dirichletInterval_division_blocks sigma t m N B hB]
  calc
    ‖(∑ j ∈ Finset.range (N / B),
          dirichletInterval sigma t (m + j * B) B) +
        dirichletInterval sigma t (m + (N / B) * B) (N % B)‖ ≤
        ‖∑ j ∈ Finset.range (N / B),
          dirichletInterval sigma t (m + j * B) B‖ +
        ‖dirichletInterval sigma t (m + (N / B) * B) (N % B)‖ :=
      norm_add_le _ _
    _ ≤ (∑ j ∈ Finset.range (N / B),
          ‖dirichletInterval sigma t (m + j * B) B‖) +
        ‖dirichletInterval sigma t (m + (N / B) * B) (N % B)‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (∑ j ∈ Finset.range (N / B),
          dirichletWeight sigma (m + j * B) *
            max (constantAProcessPrefixThreshold depth h : ℝ)
              (6 * (1 + Real.log h) * (B : ℝ) /
                (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ))) +
        (N % B : ℕ) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro j hj
        apply norm_dirichletInterval_le_weight_mul_constantAProcessExplicitPower
          sigma t (m + j * B) B depth h hsigma ht (by omega) hh
        · exact hmajor j (Finset.mem_range.mp hj)
        · exact hscale j (Finset.mem_range.mp hj)
      · exact norm_dirichletInterval_le_length sigma t
          (m + (N / B) * B) (N % B) hsigma (by omega)

/-- One left-endpoint majorant and one global right-endpoint scale condition
imply all local full-block A-process hypotheses. -/
theorem constantAProcessBlockConditions_of_global_scale
    (t : ℝ) (m N B depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hscale : 2 * Real.pi * (h : ℝ) ≤
      zetaAProcessUniformLeafDeltaLower t m N depth *
        (h : ℝ) ^ depth *
          (constantAProcessPrefixThreshold depth h : ℝ)) :
    (∀ j < N / B,
      t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
        (((m + j * B : ℕ) : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi) ∧
    (∀ j < N / B, ∀ K,
      constantAProcessPrefixThreshold depth h ≤ K → K ≤ B →
        2 * Real.pi * (h : ℝ) ≤
          zetaAProcessUniformLeafDeltaLower t (m + j * B) K depth *
            (h : ℝ) ^ depth * (K : ℝ)) := by
  constructor
  · intro j hj
    have hdelta := zetaAProcessUniformLeafDeltaLower_antitone_endpoint
      t m 0 (m + j * B) 0 depth ht.le (by omega) (by omega)
    calc
      t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
          (((m + j * B : ℕ) : ℝ) ^ (depth + 1))⁻¹) =
          zetaAProcessUniformLeafDeltaLower t (m + j * B) 0 depth *
            (h : ℝ) ^ depth := by
        unfold zetaAProcessUniformLeafDeltaLower
        simp only [Nat.add_zero]
        ring
      _ ≤ zetaAProcessUniformLeafDeltaLower t m 0 depth *
            (h : ℝ) ^ depth :=
        mul_le_mul_of_nonneg_right hdelta (by positivity)
      _ = t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
          ((m : ℝ) ^ (depth + 1))⁻¹) := by
        unfold zetaAProcessUniformLeafDeltaLower
        simp only [Nat.add_zero]
        ring
      _ ≤ Real.pi := hmajor
  · intro j hj K hthreshold hKB
    have hjq : j + 1 ≤ N / B := by omega
    have hmul : (j + 1) * B ≤ (N / B) * B :=
      Nat.mul_le_mul_right B hjq
    have hquotient : (N / B) * B ≤ N := Nat.div_mul_le_self N B
    have hend : m + j * B + K ≤ m + N := by
      have hblock : j * B + K ≤ (j + 1) * B := by
        have hprefix := Nat.add_le_add_left hKB (j * B)
        simpa only [Nat.succ_mul] using hprefix
      omega
    have hdelta := zetaAProcessUniformLeafDeltaLower_antitone_endpoint
      t (m + j * B) K m N depth ht.le (by omega) hend
    have hglobalNonneg :
        0 ≤ zetaAProcessUniformLeafDeltaLower t m N depth := by
      unfold zetaAProcessUniformLeafDeltaLower
      positivity
    have hthresholdReal :
        (constantAProcessPrefixThreshold depth h : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hthreshold
    calc
      2 * Real.pi * (h : ℝ) ≤
          zetaAProcessUniformLeafDeltaLower t m N depth *
            (h : ℝ) ^ depth *
              (constantAProcessPrefixThreshold depth h : ℝ) := hscale
      _ ≤ zetaAProcessUniformLeafDeltaLower t m N depth *
            (h : ℝ) ^ depth * (K : ℝ) := by
        exact mul_le_mul_of_nonneg_left hthresholdReal
          (mul_nonneg hglobalNonneg (by positivity))
      _ ≤ zetaAProcessUniformLeafDeltaLower t (m + j * B) K depth *
            (h : ℝ) ^ depth * (K : ℝ) := by
        have hcore := mul_le_mul_of_nonneg_right hdelta
          (show 0 ≤ (h : ℝ) ^ depth by positivity)
        exact mul_le_mul_of_nonneg_right hcore (Nat.cast_nonneg K)

/-- The long-interval A-process estimate with all local block hypotheses
discharged by one condition at the left endpoint and one condition at the
global right endpoint. -/
theorem norm_dirichletInterval_le_sum_constantAProcessExplicitPower_of_global_scale
    (sigma t : ℝ) (m N B depth h : ℕ)
    (hsigma : 0 ≤ sigma) (ht : 0 < t) (hm : 0 < m)
    (hB : 0 < B) (hh : 1 ≤ h)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hscale : 2 * Real.pi * (h : ℝ) ≤
      zetaAProcessUniformLeafDeltaLower t m N depth *
        (h : ℝ) ^ depth *
          (constantAProcessPrefixThreshold depth h : ℝ)) :
    ‖dirichletInterval sigma t m N‖ ≤
      ∑ j ∈ Finset.range (N / B),
          dirichletWeight sigma (m + j * B) *
            max (constantAProcessPrefixThreshold depth h : ℝ)
              (6 * (1 + Real.log h) * (B : ℝ) /
                (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ)) +
        (N % B : ℕ) := by
  obtain ⟨hmajorLocal, hscaleLocal⟩ :=
    constantAProcessBlockConditions_of_global_scale
      t m N B depth h ht hm hmajor hscale
  exact norm_dirichletInterval_le_sum_constantAProcessExplicitPower
    sigma t m N B depth h hsigma ht hm hB hh hmajorLocal hscaleLocal

/-- Scale-explicit long-interval estimate with the block sum replaced by the
number of blocks times the left-endpoint Dirichlet weight. -/
theorem norm_dirichletInterval_le_numBlocks_mul_constantAProcessExplicitPower
    (sigma t : ℝ) (m N B depth h : ℕ)
    (hsigma : 0 ≤ sigma) (ht : 0 < t) (hm : 0 < m)
    (hB : 0 < B) (hh : 1 ≤ h)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hscale : 2 * Real.pi * (h : ℝ) ≤
      zetaAProcessUniformLeafDeltaLower t m N depth *
        (h : ℝ) ^ depth *
          (constantAProcessPrefixThreshold depth h : ℝ)) :
    ‖dirichletInterval sigma t m N‖ ≤
      (N / B : ℕ) * dirichletWeight sigma m *
        max (constantAProcessPrefixThreshold depth h : ℝ)
          (6 * (1 + Real.log h) * (B : ℝ) /
            (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ)) +
        (N % B : ℕ) := by
  have hsum :=
    norm_dirichletInterval_le_sum_constantAProcessExplicitPower_of_global_scale
      sigma t m N B depth h hsigma ht hm hB hh hmajor hscale
  refine hsum.trans ?_
  apply add_le_add
  · calc
      ∑ j ∈ Finset.range (N / B),
          dirichletWeight sigma (m + j * B) *
            max (constantAProcessPrefixThreshold depth h : ℝ)
              (6 * (1 + Real.log h) * (B : ℝ) /
                (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ)) ≤
          ∑ _j ∈ Finset.range (N / B),
            dirichletWeight sigma m *
              max (constantAProcessPrefixThreshold depth h : ℝ)
                (6 * (1 + Real.log h) * (B : ℝ) /
                  (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_right
          (dirichletWeight_le_of_le hsigma hm (by omega))
        exact (Nat.cast_nonneg _).trans (le_max_left _ _)
      _ = (N / B : ℕ) * dirichletWeight sigma m *
          max (constantAProcessPrefixThreshold depth h : ℝ)
            (6 * (1 + Real.log h) * (B : ℝ) /
              (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  · exact le_rfl

end ZeroFreeRegion.VinogradovKorobov
