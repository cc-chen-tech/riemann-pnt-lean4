import PrimeNumberTheorem.PositiveFourierKernel

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- Coefficients supported on the tail beginning at `j`. -/
def tailCoefficient (j : ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  if j ≤ n then c n else 0

/-- The first kernel followed by successive differences of a kernel sequence. -/
def positiveKernelIncrement (g : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => g 0
  | n + 1 => fun t => g (n + 1) t - g n t

/-- Integrability is preserved by the successive-difference construction. -/
theorem integrable_positiveKernelIncrement
    {g : ℕ → ℝ → ℝ} (hg : ∀ j, Integrable (g j)) (j : ℕ) :
    Integrable (positiveKernelIncrement g j) := by
  cases j with
  | zero => simpa [positiveKernelIncrement] using hg 0
  | succ j =>
      simpa [positiveKernelIncrement] using (hg (j + 1)).sub (hg j)

/-- A pointwise increasing sequence of nonnegative kernels has nonnegative
successive increments. -/
theorem positiveKernelIncrement_nonneg
    {g : ℕ → ℝ → ℝ} (hg0 : ∀ t, 0 ≤ g 0 t)
    (hmono : ∀ j t, g j t ≤ g (j + 1) t) (j : ℕ) (t : ℝ) :
    0 ≤ positiveKernelIncrement g j t := by
  cases j with
  | zero => simpa [positiveKernelIncrement] using hg0 t
  | succ j =>
      simpa [positiveKernelIncrement] using sub_nonneg.mpr (hmono j t)

/-- Fourier kernels of successive increments telescope back to the kernel at
the last scale. -/
theorem sum_fourierKernel_positiveKernelIncrement
    {g : ℕ → ℝ → ℝ} (hg : ∀ j, Integrable (g j)) (n : ℕ) (xi : ℝ) :
    (∑ j ∈ Finset.range (n + 1),
      fourierKernel (positiveKernelIncrement g j) xi) =
        fourierKernel (g n) xi := by
  induction n with
  | zero => simp [positiveKernelIncrement]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show fourierKernel (positiveKernelIncrement g (n + 1)) xi =
          fourierKernel (g (n + 1)) xi - fourierKernel (g n) xi by
        simpa [positiveKernelIncrement] using
          (fourierKernel_sub (hg (n + 1)) (hg n) (xi := xi))]
      ring

/-- For a fixed pair `(m,n)`, tail coefficients retain exactly the increments
up to `min m n`, so the Fourier kernels telescope to that scale. -/
theorem sum_tailCoefficient_fourierKernel_increment
    {c : ℕ → ℂ} {g : ℕ → ℝ → ℝ} (hg : ∀ j, Integrable (g j))
    {N m n : ℕ} (hm : m < N) (_hn : n < N) (xi : ℝ) :
    (∑ j ∈ Finset.range N,
      conj (tailCoefficient j c m) * tailCoefficient j c n *
        fourierKernel (positiveKernelIncrement g j) xi) =
      conj (c m) * c n * fourierKernel (g (min m n)) xi := by
  let f : ℕ → ℂ := fun j =>
    conj (tailCoefficient j c m) * tailCoefficient j c n *
      fourierKernel (positiveKernelIncrement g j) xi
  have hminN : min m n < N :=
    lt_of_le_of_lt (min_le_left m n) hm
  have hsubset : Finset.range (min m n + 1) ⊆ Finset.range N :=
    Finset.range_mono (Nat.succ_le_iff.mpr hminN)
  have hzero : ∀ j ∈ Finset.range N,
      j ∉ Finset.range (min m n + 1) → f j = 0 := by
    intro j hjN hjOutside
    have hjgt : min m n < j := by
      have hjNotLt : ¬j < min m n + 1 := by
        simpa only [Finset.mem_range] using hjOutside
      omega
    by_cases hjm : j ≤ m
    · have hjn : ¬j ≤ n := by
        intro hjn
        exact (not_le_of_gt hjgt) (le_min hjm hjn)
      simp [f, tailCoefficient, hjn]
    · simp [f, tailCoefficient, hjm]
  have hsum :
      (∑ j ∈ Finset.range (min m n + 1), f j) =
        ∑ j ∈ Finset.range N, f j :=
    Finset.sum_subset hsubset hzero
  change (∑ j ∈ Finset.range N, f j) = _
  rw [← hsum]
  calc
    (∑ j ∈ Finset.range (min m n + 1), f j) =
        ∑ j ∈ Finset.range (min m n + 1),
          (conj (c m) * c n) *
            fourierKernel (positiveKernelIncrement g j) xi := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ min m n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hjm : j ≤ m := hjle.trans (min_le_left m n)
      have hjn : j ≤ n := hjle.trans (min_le_right m n)
      simp [f, tailCoefficient, hjm, hjn]
    _ = (conj (c m) * c n) *
        (∑ j ∈ Finset.range (min m n + 1),
          fourierKernel (positiveKernelIncrement g j) xi) := by
      rw [Finset.mul_sum]
    _ = conj (c m) * c n * fourierKernel (g (min m n)) xi := by
      rw [sum_fourierKernel_positiveKernelIncrement hg]

/-- Finite version of Carneiro--Littmann's tail-kernel identity: after
exchanging the three finite sums, each pair sees the kernel at its minimum
tail index. -/
theorem sum_tail_fourierKernelForm_eq_min_kernel
    {N : ℕ} {c : ℕ → ℂ} {omega : ℕ → ℝ}
    {g : ℕ → ℝ → ℝ} (hg : ∀ j, Integrable (g j)) :
    (∑ j ∈ Finset.range N,
      finiteFourierKernelForm (Finset.range N)
        (tailCoefficient j c) omega (positiveKernelIncrement g j)) =
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        conj (c m) * c n *
          fourierKernel (g (min m n)) (omega n - omega m) := by
  unfold finiteFourierKernelForm
  calc
    (∑ j ∈ Finset.range N, ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        conj (tailCoefficient j c m) * tailCoefficient j c n *
          fourierKernel (positiveKernelIncrement g j) (omega n - omega m)) =
        ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range N,
          conj (tailCoefficient j c m) * tailCoefficient j c n *
            fourierKernel (positiveKernelIncrement g j) (omega n - omega m) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
    _ = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        conj (c m) * c n *
          fourierKernel (g (min m n)) (omega n - omega m) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact sum_tailCoefficient_fourierKernel_increment hg
        (Finset.mem_range.mp hm) (Finset.mem_range.mp hn) (omega n - omega m)

/-- If the minimum-index kernel has a prescribed diagonal value and a
reciprocal-frequency formula off the diagonal, its double sum splits into the
weighted diagonal and the Hilbert form. -/
theorem sum_min_fourierKernel_eq_diagonal_add_mul_hilbert
    {N : ℕ} {c : ℕ → ℂ} {omega : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    {diagonal : ℕ → ℂ} {kappa : ℂ}
    (hzero : ∀ n ∈ Finset.range N,
      fourierKernel (g n) 0 = diagonal n)
    (hkernel : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      fourierKernel (g (min m n)) (omega n - omega m) =
        kappa / (omega n - omega m)) :
    (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      conj (c m) * c n *
        fourierKernel (g (min m n)) (omega n - omega m)) =
      (∑ n ∈ Finset.range N, diagonal n * (‖c n‖ ^ 2 : ℂ)) +
        kappa * hilbertForm (Finset.range N) c omega := by
  have hpair : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N,
      conj (c m) * c n *
          fourierKernel (g (min m n)) (omega n - omega m) =
        if m = n then diagonal m * (‖c m‖ ^ 2 : ℂ)
        else kappa * (conj (c m) * c n / (omega n - omega m)) := by
    intro m hm n hn
    by_cases hmn : m = n
    · subst n
      rw [if_pos rfl, min_self, sub_self, hzero m hm]
      rw [← ofReal_pow, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_conj_mul_self]
      ring
    · rw [if_neg hmn, hkernel m hm n hn hmn]
      ring
  have hdiag :
      (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        if m = n then diagonal m * (‖c m‖ ^ 2 : ℂ) else 0) =
        ∑ n ∈ Finset.range N, diagonal n * (‖c n‖ ^ 2 : ℂ) := by
    apply Finset.sum_congr rfl
    intro m hm
    simp [hm]
  have hoff :
      (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        if m = n then 0
        else kappa * (conj (c m) * c n / (omega n - omega m))) =
        kappa * hilbertForm (Finset.range N) c omega := by
    unfold hilbertForm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hmn : m = n <;> simp [hmn]
  calc
    (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        conj (c m) * c n *
          fourierKernel (g (min m n)) (omega n - omega m)) =
        ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          if m = n then diagonal m * (‖c m‖ ^ 2 : ℂ)
          else kappa * (conj (c m) * c n / (omega n - omega m)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact hpair m hm n hn
    _ = (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          if m = n then diagonal m * (‖c m‖ ^ 2 : ℂ) else 0) +
        (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          if m = n then 0
          else kappa * (conj (c m) * c n / (omega n - omega m))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hmn : m = n <;> simp [hmn]
    _ = (∑ n ∈ Finset.range N, diagonal n * (‖c n‖ ^ 2 : ℂ)) +
        kappa * hilbertForm (Finset.range N) c omega := by
      rw [hdiag, hoff]

/-- If the kernel sequence starts nonnegative and increases pointwise, the sum
of all tail increment forms has nonnegative real part. -/
theorem sum_tail_fourierKernelForm_re_nonneg
    {N : ℕ} {c : ℕ → ℂ} {omega : ℕ → ℝ}
    {g : ℕ → ℝ → ℝ} (hg : ∀ j, Integrable (g j))
    (hg0 : ∀ t, 0 ≤ g 0 t)
    (hmono : ∀ j t, g j t ≤ g (j + 1) t) :
    0 ≤ ((∑ j ∈ Finset.range N,
      finiteFourierKernelForm (Finset.range N)
        (tailCoefficient j c) omega (positiveKernelIncrement g j))).re := by
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun j hj =>
    finiteFourierKernelForm_re_nonneg
      (integrable_positiveKernelIncrement hg j)
      (positiveKernelIncrement_nonneg hg0 hmono j)

/-- A positive increasing kernel sequence with off-diagonal value `-2i / ξ`
supplies the minus side of the weighted Hilbert certificate. -/
theorem hilbertForm_minus_certificate_of_positive_kernelSequence
    {N : ℕ} {c : ℕ → ℂ} {omega weight : ℕ → ℝ}
    {g : ℕ → ℝ → ℝ} {C : ℝ}
    (hg : ∀ j, Integrable (g j)) (hg0 : ∀ t, 0 ≤ g 0 t)
    (hmono : ∀ j t, g j t ≤ g (j + 1) t)
    (hzero : ∀ n ∈ Finset.range N,
      fourierKernel (g n) 0 = ((2 * C * weight n : ℝ) : ℂ))
    (hkernel : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      fourierKernel (g (min m n)) (omega n - omega m) =
        (-2 * Complex.I) / (omega n - omega m)) :
    0 ≤ (((C * ∑ n ∈ Finset.range N,
        weight n * ‖c n‖ ^ 2 : ℝ) : ℂ) -
      Complex.I * hilbertForm (Finset.range N) c omega).re := by
  let W : ℝ := ∑ n ∈ Finset.range N, weight n * ‖c n‖ ^ 2
  let total : ℂ := ∑ j ∈ Finset.range N,
    finiteFourierKernelForm (Finset.range N)
      (tailCoefficient j c) omega (positiveKernelIncrement g j)
  have hnonneg : 0 ≤ total.re := by
    dsimp [total]
    exact sum_tail_fourierKernelForm_re_nonneg hg hg0 hmono
  have htotal : total =
      (∑ n ∈ Finset.range N,
        (((2 * C * weight n : ℝ) : ℂ)) * (‖c n‖ ^ 2 : ℂ)) +
        (-2 * Complex.I) * hilbertForm (Finset.range N) c omega := by
    dsimp [total]
    rw [sum_tail_fourierKernelForm_eq_min_kernel hg]
    exact sum_min_fourierKernel_eq_diagonal_add_mul_hilbert hzero hkernel
  have hdiag :
      (∑ n ∈ Finset.range N,
        (((2 * C * weight n : ℝ) : ℂ)) * (‖c n‖ ^ 2 : ℂ)) =
        ((2 * C * W : ℝ) : ℂ) := by
    calc
      (∑ n ∈ Finset.range N,
          (((2 * C * weight n : ℝ) : ℂ)) * (‖c n‖ ^ 2 : ℂ)) =
          ∑ n ∈ Finset.range N,
            ((2 * C * (weight n * ‖c n‖ ^ 2) : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro n hn
        push_cast
        ring
      _ = ((∑ n ∈ Finset.range N,
          2 * C * (weight n * ‖c n‖ ^ 2) : ℝ) : ℂ) := by
        push_cast
        rfl
      _ = ((2 * C * W : ℝ) : ℂ) := by
        congr 1
        dsimp [W]
        rw [Finset.mul_sum]
  have hfactor : total = (2 : ℂ) *
      (((C * W : ℝ) : ℂ) -
        Complex.I * hilbertForm (Finset.range N) c omega) := by
    rw [htotal, hdiag]
    push_cast
    ring
  rw [hfactor] at hnonneg
  have htwice : 0 ≤ 2 * ((((C * W : ℝ) : ℂ) -
      Complex.I * hilbertForm (Finset.range N) c omega).re) := by
    simpa using hnonneg
  change 0 ≤ ((((C * W : ℝ) : ℂ) -
    Complex.I * hilbertForm (Finset.range N) c omega).re)
  linarith

/-- A positive increasing kernel sequence with off-diagonal value `2i / ξ`
supplies the plus side of the weighted Hilbert certificate. -/
theorem hilbertForm_plus_certificate_of_positive_kernelSequence
    {N : ℕ} {c : ℕ → ℂ} {omega weight : ℕ → ℝ}
    {g : ℕ → ℝ → ℝ} {C : ℝ}
    (hg : ∀ j, Integrable (g j)) (hg0 : ∀ t, 0 ≤ g 0 t)
    (hmono : ∀ j t, g j t ≤ g (j + 1) t)
    (hzero : ∀ n ∈ Finset.range N,
      fourierKernel (g n) 0 = ((2 * C * weight n : ℝ) : ℂ))
    (hkernel : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      fourierKernel (g (min m n)) (omega n - omega m) =
        (2 * Complex.I) / (omega n - omega m)) :
    0 ≤ (((C * ∑ n ∈ Finset.range N,
        weight n * ‖c n‖ ^ 2 : ℝ) : ℂ) +
      Complex.I * hilbertForm (Finset.range N) c omega).re := by
  let W : ℝ := ∑ n ∈ Finset.range N, weight n * ‖c n‖ ^ 2
  let total : ℂ := ∑ j ∈ Finset.range N,
    finiteFourierKernelForm (Finset.range N)
      (tailCoefficient j c) omega (positiveKernelIncrement g j)
  have hnonneg : 0 ≤ total.re := by
    dsimp [total]
    exact sum_tail_fourierKernelForm_re_nonneg hg hg0 hmono
  have htotal : total =
      (∑ n ∈ Finset.range N,
        (((2 * C * weight n : ℝ) : ℂ)) * (‖c n‖ ^ 2 : ℂ)) +
        (2 * Complex.I) * hilbertForm (Finset.range N) c omega := by
    dsimp [total]
    rw [sum_tail_fourierKernelForm_eq_min_kernel hg]
    exact sum_min_fourierKernel_eq_diagonal_add_mul_hilbert hzero hkernel
  have hdiag :
      (∑ n ∈ Finset.range N,
        (((2 * C * weight n : ℝ) : ℂ)) * (‖c n‖ ^ 2 : ℂ)) =
        ((2 * C * W : ℝ) : ℂ) := by
    calc
      (∑ n ∈ Finset.range N,
          (((2 * C * weight n : ℝ) : ℂ)) * (‖c n‖ ^ 2 : ℂ)) =
          ∑ n ∈ Finset.range N,
            ((2 * C * (weight n * ‖c n‖ ^ 2) : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro n hn
        push_cast
        ring
      _ = ((∑ n ∈ Finset.range N,
          2 * C * (weight n * ‖c n‖ ^ 2) : ℝ) : ℂ) := by
        push_cast
        rfl
      _ = ((2 * C * W : ℝ) : ℂ) := by
        congr 1
        dsimp [W]
        rw [Finset.mul_sum]
  have hfactor : total = (2 : ℂ) *
      (((C * W : ℝ) : ℂ) +
        Complex.I * hilbertForm (Finset.range N) c omega) := by
    rw [htotal, hdiag]
    push_cast
    ring
  rw [hfactor] at hnonneg
  have htwice : 0 ≤ 2 * ((((C * W : ℝ) : ℂ) +
      Complex.I * hilbertForm (Finset.range N) c omega).re) := by
    simpa using hnonneg
  change 0 ≤ ((((C * W : ℝ) : ℂ) +
    Complex.I * hilbertForm (Finset.range N) c omega).re)
  linarith

/-- Two positive increasing kernel sequences of opposite high-frequency signs
discharge the weighted Hilbert hypothesis in the finite exponential-sum
mean-square estimate. -/
theorem finiteExponentialSum_meanSquare_le_of_positive_kernelSequences
    {N : ℕ} {c : ℕ → ℂ} {omega weight : ℕ → ℝ}
    {gMinus gPlus : ℕ → ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b)
    (homega : Set.InjOn omega (Finset.range N : Set ℕ))
    (hweight : ∀ n ∈ Finset.range N, 0 ≤ weight n)
    (hgMinus : ∀ j, Integrable (gMinus j))
    (hgMinus0 : ∀ t, 0 ≤ gMinus 0 t)
    (hmonoMinus : ∀ j t, gMinus j t ≤ gMinus (j + 1) t)
    (hzeroMinus : ∀ n ∈ Finset.range N,
      fourierKernel (gMinus n) 0 = ((2 * C * weight n : ℝ) : ℂ))
    (hkernelMinus : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      fourierKernel (gMinus (min m n)) (omega n - omega m) =
        (-2 * Complex.I) / (omega n - omega m))
    (hgPlus : ∀ j, Integrable (gPlus j))
    (hgPlus0 : ∀ t, 0 ≤ gPlus 0 t)
    (hmonoPlus : ∀ j t, gPlus j t ≤ gPlus (j + 1) t)
    (hzeroPlus : ∀ n ∈ Finset.range N,
      fourierKernel (gPlus n) 0 = ((2 * C * weight n : ℝ) : ℂ))
    (hkernelPlus : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      fourierKernel (gPlus (min m n)) (omega n - omega m) =
        (2 * Complex.I) / (omega n - omega m)) :
    ∫ t in a..b, ‖finiteExponentialSum (Finset.range N) c omega t‖ ^ 2 ≤
      (b - a) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 +
        2 * C * ∑ n ∈ Finset.range N, weight n * ‖c n‖ ^ 2 := by
  apply finiteExponentialSum_meanSquare_le_of_two_sided_certificate
    hab homega hweight
  · intro d
    exact hilbertForm_plus_certificate_of_positive_kernelSequence
      (c := d) hgPlus hgPlus0 hmonoPlus hzeroPlus hkernelPlus
  · intro d
    exact hilbertForm_minus_certificate_of_positive_kernelSequence
      (c := d) hgMinus hgMinus0 hmonoMinus hzeroMinus hkernelMinus

end DirichletPolynomial
end PrimeNumberTheorem
