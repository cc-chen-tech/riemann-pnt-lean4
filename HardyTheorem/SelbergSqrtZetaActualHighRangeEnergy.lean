import HardyTheorem.SelbergSqrtZetaGapDecomposition
import HardyTheorem.SelbergSqrtZetaRectangularParseval

open Complex
open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# Actual signed high-range energy for the square-root-zeta mollifier

The complete-zeta part of the high range is kept as the square of the actual
signed tapered convolution.  The pair support is first reindexed exactly into
an arithmetic convolution; only then is a square norm taken.  This avoids the
fiber-cardinality Cauchy--Schwarz and coefficientwise absolute-value losses in
the previous high-range estimate.
-/

/-- The finite signed pair sum is the exact convolution square against zeta
for every positive product index.  Terms outside the finite mollifier box
vanish through `selbergShortTaperedSqrtZeta`; no absolute values are inserted. -/
theorem selbergSqrtZetaShortCompleteRangePairSum_eq_shortConvolution
    {X k : ℕ} (hk : 1 ≤ k) :
    selbergSqrtZetaShortCompleteRangePairSum X k =
      (((selbergShortTaperedSqrtZeta X *
          selbergShortTaperedSqrtZeta X) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) k) := by
  classical
  let S := selbergShortCompleteRangePairs X k
  let U := k.divisors.biUnion (fun d => d.divisorsAntidiagonal)
  let f : ℕ × ℕ → ℝ := fun p =>
    selbergShortTaperedSqrtZeta X p.1 *
      selbergShortTaperedSqrtZeta X p.2
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  have hsub : S ⊆ U := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpBox, hpDvd⟩
    rcases Finset.mem_product.mp hpBox with ⟨hp1, hp2⟩
    have hpProd0 : p.1 * p.2 ≠ 0 :=
      Nat.mul_ne_zero
        (Nat.ne_of_gt (Finset.mem_Icc.mp hp1).1)
        (Nat.ne_of_gt (Finset.mem_Icc.mp hp2).1)
    exact Finset.mem_biUnion.mpr
      ⟨p.1 * p.2, Nat.mem_divisors.mpr ⟨hpDvd, hk0⟩,
        Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hpProd0⟩⟩
  have hzero : ∀ p ∈ U, p ∉ S → f p = 0 := by
    intro p hpU hpNotS
    rcases Finset.mem_biUnion.mp hpU with ⟨d, hd, hpd⟩
    have hpProd := Nat.mem_divisorsAntidiagonal.mp hpd
    have hpDvd : p.1 * p.2 ∣ k := by
      rw [hpProd.1]
      exact (Nat.mem_divisors.mp hd).1
    by_cases hp1 : p.1 ∈ Finset.Icc 1 X
    · by_cases hp2 : p.2 ∈ Finset.Icc 1 X
      · exact (hpNotS (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hp1, hp2⟩, hpDvd⟩)).elim
      · unfold f
        rw [selbergShortTaperedSqrtZeta_apply,
          selbergShortTaperedSqrtZeta_apply, if_pos hp1, if_neg hp2]
        simp
    · unfold f
      rw [selbergShortTaperedSqrtZeta_apply,
        selbergShortTaperedSqrtZeta_apply, if_neg hp1]
      simp
  have hdisjoint :
      Set.PairwiseDisjoint (↑k.divisors : Set ℕ)
        (fun d => d.divisorsAntidiagonal) := by
    intro d hd e he hde
    change Disjoint d.divisorsAntidiagonal e.divisorsAntidiagonal
    rw [Finset.disjoint_left]
    intro p hpd hpe
    have hpdProd := (Nat.mem_divisorsAntidiagonal.mp hpd).1
    have hpeProd := (Nat.mem_divisorsAntidiagonal.mp hpe).1
    exact hde (hpdProd.symm.trans hpeProd)
  unfold selbergSqrtZetaShortCompleteRangePairSum
  calc
    (∑ p ∈ selbergShortCompleteRangePairs X k,
        selbergSqrtZetaTaperedCoeff X p.1 *
          selbergSqrtZetaTaperedCoeff X p.2) =
        ∑ p ∈ S, f p := by
      apply Finset.sum_congr rfl
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpBox, _hpDvd⟩
      rcases Finset.mem_product.mp hpBox with ⟨hp1, hp2⟩
      unfold f
      rw [selbergShortTaperedSqrtZeta_apply,
        selbergShortTaperedSqrtZeta_apply, if_pos hp1, if_pos hp2]
    _ = ∑ p ∈ U, f p :=
      Finset.sum_subset hsub hzero
    _ = ∑ d ∈ k.divisors, ∑ p ∈ d.divisorsAntidiagonal, f p := by
      exact Finset.sum_biUnion hdisjoint
    _ = ∑ d ∈ k.divisors,
        (selbergShortTaperedSqrtZeta X *
          selbergShortTaperedSqrtZeta X) d := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [ArithmeticFunction.mul_apply]
    _ = (((selbergShortTaperedSqrtZeta X *
          selbergShortTaperedSqrtZeta X) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) k) := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]

/-- In the complete-zeta range `k ≤ N`, the actual collected square energy is
exactly the square of the signed finite convolution divided by `k`. -/
theorem
    normSq_selbergSqrtZetaShortDirichletCollectedCoeff_eq_signedPairSum_sq_div
    {N X k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    Complex.normSq (selbergSqrtZetaShortDirichletCollectedCoeff N X k) =
      (selbergSqrtZetaShortCompleteRangePairSum X k) ^ 2 / (k : ℝ) := by
  rw [selbergSqrtZetaShortDirichletCollectedCoeff_eq_pairSum hk hkN,
    Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_inv,
    Complex.normSq_ofReal]
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hsqrt : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) := by
    nlinarith [Real.sq_sqrt hk0]
  rw [hsqrt]
  ring

/-- The interval multiplier preserves the actual signed pair square throughout
the complete-zeta high range.  Unlike the former pointwise estimate, this
contains neither a fiber cardinality nor a sum of coefficient absolute values. -/
theorem
    normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_signedPairSum
    {N X k : ℕ} (hk : 1 < k) (hkN : k ≤ N) (H : ℝ) :
    Complex.normSq
        (MathlibAux.slidingExponentialCoefficient H
          (selbergSqrtZetaShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency k) ≤
      (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
        ((selbergSqrtZetaShortCompleteRangePairSum X k) ^ 2 / (k : ℝ)) := by
  have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hkReal
  have hfreq : selbergShortDirichletCollectedFrequency k ≠ 0 := by
    rw [selbergShortDirichletCollectedFrequency_eq_neg_log]
    exact neg_ne_zero.mpr hlog.ne'
  have hfreqAbs :
      |selbergShortDirichletCollectedFrequency k| =
        Real.log (k : ℝ) := by
    rw [selbergShortDirichletCollectedFrequency_eq_neg_log, abs_neg,
      abs_of_pos hlog]
  have hslide := MathlibAux.norm_slidingExponentialCoefficient_le_min
    (selbergSqrtZetaShortDirichletCollectedCoeff N X)
    selbergShortDirichletCollectedFrequency k hfreq (H := H)
  rw [hfreqAbs] at hslide
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖MathlibAux.slidingExponentialCoefficient H
          (selbergSqrtZetaShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency k‖ ^ 2 ≤
        (‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖ *
          min |H| (2 / Real.log (k : ℝ))) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hslide
    _ = (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
        Complex.normSq
          (selbergSqrtZetaShortDirichletCollectedCoeff N X k) := by
      rw [Complex.normSq_eq_norm_sq]
      ring
    _ = (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
        ((selbergSqrtZetaShortCompleteRangePairSum X k) ^ 2 / (k : ℝ)) := by
      rw [
        normSq_selbergSqrtZetaShortDirichletCollectedCoeff_eq_signedPairSum_sq_div
          hk.le hkN]

/-- Summed actual high-range energy on `X < k ≤ N`.  The right side squares
the signed convolution only after all factor pairs have been collected. -/
theorem
    sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_completeHighRange_le_signedPairEnergy
    {N X : ℕ} (hX : 1 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc X N,
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      ∑ k ∈ Finset.Ioc X N,
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergSqrtZetaShortCompleteRangePairSum X k) ^ 2 / (k : ℝ)) := by
  apply Finset.sum_le_sum
  intro k hk
  have hkData := Finset.mem_Ioc.mp hk
  exact
    normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_signedPairSum
      (hX.trans_lt hkData.1) hkData.2 H

/-- The full diagonal energy uses the proved constant low range, the actual
signed pair energy on `X < k ≤ N`, and leaves only the genuinely
zeta-truncated range `N < k` as an actual collected-coefficient tail. -/
theorem
    sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_signedPairEnergy_add_actualTail
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (hXN : X ≤ N)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (15 : ℝ) / 4 * H ^ 2 +
        ((∑ k ∈ Finset.Ioc X N,
            (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
              ((selbergSqrtZetaShortCompleteRangePairSum X k) ^ 2 /
                (k : ℝ))) +
          ∑ k ∈ Finset.Ioc N (N * X * X),
            Complex.normSq
              (MathlibAux.slidingExponentialCoefficient H
                (selbergSqrtZetaShortDirichletCollectedCoeff N X)
                selbergShortDirichletCollectedFrequency k)) := by
  have hXone : 1 ≤ X := by omega
  have hNsupport : N ≤ N * X * X := by
    calc
      N = N * 1 * 1 := by simp
      _ ≤ N * X * X := Nat.mul_le_mul (Nat.mul_le_mul_left N hXone) hXone
  have hsplit :
      Finset.Ioc X N ∪ Finset.Ioc N (N * X * X) =
        Finset.Ioc X (N * X * X) :=
    Finset.Ioc_union_Ioc_eq_Ioc hXN hNsupport
  have hdisjoint :
      Disjoint (Finset.Ioc X N) (Finset.Ioc N (N * X * X)) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have hbase :=
    sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_highRange
      hN (by omega : 1 < X) hlarge H
  rw [min_eq_right hXN, ← hsplit, Finset.sum_union hdisjoint] at hbase
  exact hbase.trans
    (add_le_add le_rfl
      (add_le_add
        (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_completeHighRange_le_signedPairEnergy
          hXone H)
        le_rfl))

/-- The full diagonal budget with the zeta-truncation tail absorbed into the
same exact rational coefficient energy supplied by rectangular Parseval, while
retaining the uniform tail-frequency decay `(2 / log (N + 1))^2`. -/
theorem
    sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_signedPairEnergy_add_logDecay_mul_rationalEnergy
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (hXN : X ≤ N)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (15 : ℝ) / 4 * H ^ 2 +
        ((∑ k ∈ Finset.Ioc X N,
            (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
              ((selbergSqrtZetaShortCompleteRangePairSum X k) ^ 2 /
                (k : ℝ))) +
          (2 / Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
              Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff N X q)) := by
  exact
    (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_signedPairEnergy_add_actualTail
      hN hX hXN hlarge H).trans
      (add_le_add le_rfl
        (add_le_add le_rfl
          (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_tail_le_logDecay_mul_signedRationalEnergy
            hN X H)))

/-- The strengthened diagonal budget retaining the exact mixed-product cutoff
in the zeta-truncation tail.  In particular, it does not enlarge the tail to
the entire rational coefficient energy. -/
theorem
    sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_signedPairEnergy_add_logDecay_mul_mixedTailEnergy
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (hXN : X ≤ N)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (15 : ℝ) / 4 * H ^ 2 +
        ((∑ k ∈ Finset.Ioc X N,
            (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
              ((selbergSqrtZetaShortCompleteRangePairSum X k) ^ 2 /
                (k : ℝ))) +
          (2 / Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 *
            selbergSqrtZetaSignedRationalMixedProductTailEnergy N X N) := by
  exact
    (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_signedPairEnergy_add_actualTail
      hN hX hXN hlarge H).trans
      (add_le_add le_rfl
        (add_le_add le_rfl
          (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_tail_le_logDecay_mul_signedRationalMixedProductTailEnergy
            hN X H)))

/-- Direct gap-sum endpoint with the actual signed high-range pair energy.
The off-diagonal and the `k > N` truncation tail remain actual collected
quantities; the `X²` pair-cardinality majorant is absent. -/
theorem
    selbergSqrtZetaShortDirichletGapSum_le_signedPairEnergy_add_actualTail_add_offDiagonal
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (hXN : X ≤ N)
    (hlarge : Real.log 4 + 5 ≤ Real.log X)
    {A B H : ℝ} (hAB : A ≤ B) :
    selbergSqrtZetaShortDirichletGapSum N X A B H ≤
      (B - A) *
          ((15 : ℝ) / 4 * H ^ 2 +
            ((∑ k ∈ Finset.Ioc X N,
                (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
                  ((selbergSqrtZetaShortCompleteRangePairSum X k) ^ 2 /
                    (k : ℝ))) +
              ∑ k ∈ Finset.Ioc N (N * X * X),
                Complex.normSq
                  (MathlibAux.slidingExponentialCoefficient H
                    (selbergSqrtZetaShortDirichletCollectedCoeff N X)
                    selbergShortDirichletCollectedFrequency k))) +
        H ^ 2 *
          ∑ m ∈ Finset.Ioc 1 (N * X * X),
            ∑ n ∈ Finset.Ioc 1 (N * X * X),
              2 *
                    ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ *
                  ‖selbergSqrtZetaShortDirichletCollectedCoeff N X n‖ /
                |selbergShortDirichletCollectedFrequency m -
                  selbergShortDirichletCollectedFrequency n| := by
  rw [selbergSqrtZetaShortDirichletGapSum_eq_slidingExponentialGapSum]
  apply
    (MathlibAux.slidingExponentialGapSum_le_diagonal_add_frequencyGap
      (Finset.Ioc 1 (N * X * X))
      (selbergSqrtZetaShortDirichletCollectedCoeff N X)
      selbergShortDirichletCollectedFrequency hAB).trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_signedPairEnergy_add_actualTail
        hN hX hXN hlarge H)
      (sub_nonneg.mpr hAB))
    le_rfl

/-- Gap-sum endpoint in which the actual zeta-truncation tail has been
eliminated in favor of the common rational coefficient energy.  The remaining
non-diagonal logarithmic gap form is unchanged. -/
theorem
    selbergSqrtZetaShortDirichletGapSum_le_signedPairEnergy_add_logDecay_mul_rationalEnergy_add_offDiagonal
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (hXN : X ≤ N)
    (hlarge : Real.log 4 + 5 ≤ Real.log X)
    {A B H : ℝ} (hAB : A ≤ B) :
    selbergSqrtZetaShortDirichletGapSum N X A B H ≤
      (B - A) *
          ((15 : ℝ) / 4 * H ^ 2 +
            ((∑ k ∈ Finset.Ioc X N,
                (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
                  ((selbergSqrtZetaShortCompleteRangePairSum X k) ^ 2 /
                    (k : ℝ))) +
              (2 / Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 *
                ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
                  Complex.normSq
                    (selbergSqrtZetaSignedRationalCoeff N X q))) +
        H ^ 2 *
          ∑ m ∈ Finset.Ioc 1 (N * X * X),
            ∑ n ∈ Finset.Ioc 1 (N * X * X),
              2 *
                    ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ *
                  ‖selbergSqrtZetaShortDirichletCollectedCoeff N X n‖ /
                |selbergShortDirichletCollectedFrequency m -
                  selbergShortDirichletCollectedFrequency n| := by
  rw [selbergSqrtZetaShortDirichletGapSum_eq_slidingExponentialGapSum]
  apply
    (MathlibAux.slidingExponentialGapSum_le_diagonal_add_frequencyGap
      (Finset.Ioc 1 (N * X * X))
      (selbergSqrtZetaShortDirichletCollectedCoeff N X)
      selbergShortDirichletCollectedFrequency hAB).trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_signedPairEnergy_add_logDecay_mul_rationalEnergy
        hN hX hXN hlarge H)
      (sub_nonneg.mpr hAB))
    le_rfl

/-- The `hsmall` gap-sum endpoint with the exact mixed-product tail retained.
This is strictly structured for the remaining arithmetic estimate: only
product frequencies above `N` occur in the tail term. -/
theorem
    selbergSqrtZetaShortDirichletGapSum_le_signedPairEnergy_add_logDecay_mul_mixedTailEnergy_add_offDiagonal
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (hXN : X ≤ N)
    (hlarge : Real.log 4 + 5 ≤ Real.log X)
    {A B H : ℝ} (hAB : A ≤ B) :
    selbergSqrtZetaShortDirichletGapSum N X A B H ≤
      (B - A) *
          ((15 : ℝ) / 4 * H ^ 2 +
            ((∑ k ∈ Finset.Ioc X N,
                (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
                  ((selbergSqrtZetaShortCompleteRangePairSum X k) ^ 2 /
                    (k : ℝ))) +
              (2 / Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 *
                selbergSqrtZetaSignedRationalMixedProductTailEnergy N X N)) +
        H ^ 2 *
          ∑ m ∈ Finset.Ioc 1 (N * X * X),
            ∑ n ∈ Finset.Ioc 1 (N * X * X),
              2 *
                    ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ *
                  ‖selbergSqrtZetaShortDirichletCollectedCoeff N X n‖ /
                |selbergShortDirichletCollectedFrequency m -
                  selbergShortDirichletCollectedFrequency n| := by
  rw [selbergSqrtZetaShortDirichletGapSum_eq_slidingExponentialGapSum]
  apply
    (MathlibAux.slidingExponentialGapSum_le_diagonal_add_frequencyGap
      (Finset.Ioc 1 (N * X * X))
      (selbergSqrtZetaShortDirichletCollectedCoeff N X)
      selbergShortDirichletCollectedFrequency hAB).trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_signedPairEnergy_add_logDecay_mul_mixedTailEnergy
        hN hX hXN hlarge H)
      (sub_nonneg.mpr hAB))
    le_rfl

end HardyTheorem
