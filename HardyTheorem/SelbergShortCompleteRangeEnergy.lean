import HardyTheorem.SelbergShortCompleteRangeArithmetic

open scoped BigOperators

namespace HardyTheorem

/-!
# Complete-range square energy for the Selberg short coefficient

On `1 <= k <= N`, the collected convolution is the full coefficient of the
square of the finite Selberg mollifier.  This file expands its square without
discarding signs.  The simultaneous divisibility conditions on two product
pairs are combined into one least-common-multiple condition, exposing the
arithmetic kernel that must be estimated in the Selberg mean-square argument.
-/

/-- The four mollifier indices contributing to the square of the complete
coefficient at `k`, represented as two pairs. -/
noncomputable def selbergShortCompleteRangeQuadruples
    (X k : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (((Finset.Icc 1 X).product (Finset.Icc 1 X)).product
      ((Finset.Icc 1 X).product (Finset.Icc 1 X))).filter
    (fun q => Nat.lcm (q.1.1 * q.1.2) (q.2.1 * q.2.2) ∣ k)

/-- The fixed four-index box before imposing the divisibility condition at a
particular product index `k`. -/
noncomputable def selbergShortCompleteRangeQuadrupleSupport
    (X : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((Finset.Icc 1 X).product (Finset.Icc 1 X)).product
    ((Finset.Icc 1 X).product (Finset.Icc 1 X))

/-- The fixed support for one pair of mollifier indices. -/
noncomputable def selbergShortCompleteRangePairSupport
    (X : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 X).product (Finset.Icc 1 X)

/-- The product index represented by one mollifier pair. -/
def selbergShortCompleteRangePairProduct (p : ℕ × ℕ) : ℕ :=
  p.1 * p.2

/-- The signed weight represented by one mollifier pair. -/
noncomputable def selbergShortCompleteRangePairWeight
    (X : ℕ) (p : ℕ × ℕ) : ℝ :=
  selbergMoebiusCoeff X p.1 * selbergMoebiusCoeff X p.2

/-- The coefficient obtained by collecting all two-index mollifier terms with
the same product `r`. -/
noncomputable def selbergShortDoubleMoebiusCoeff
    (X r : ℕ) : ℝ :=
  ∑ p ∈ (selbergShortCompleteRangePairSupport X).filter
      (fun p => selbergShortCompleteRangePairProduct p = r),
    selbergShortCompleteRangePairWeight X p

/-- The least-common-multiple modulus attached to two mollifier products. -/
def selbergShortCompleteRangeLcm
    (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  Nat.lcm (q.1.1 * q.1.2) (q.2.1 * q.2.2)

/-- The signed product of the four tapered Moebius coefficients. -/
noncomputable def selbergShortCompleteRangeQuadrupleWeight
    (X : ℕ) (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℝ :=
  (selbergMoebiusCoeff X q.1.1 * selbergMoebiusCoeff X q.1.2) *
    (selbergMoebiusCoeff X q.2.1 * selbergMoebiusCoeff X q.2.2)

/-- The finite harmonic mass of multiples of `r` in `[L,U]`. -/
noncomputable def selbergShortLcmHarmonicKernel
    (L U r : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc L U).filter (fun k => r ∣ k), (k : ℝ)⁻¹

/-- Collecting one finite mollifier-pair sum by the represented product is
exact for every product-dependent kernel. -/
theorem sum_completeRangePairWeight_mul_kernel_eq_collected
    (X : ℕ) (F : ℕ → ℝ) :
    (∑ p ∈ selbergShortCompleteRangePairSupport X,
        selbergShortCompleteRangePairWeight X p *
          F (selbergShortCompleteRangePairProduct p)) =
      ∑ r ∈ Finset.Icc 1 (X * X),
        selbergShortDoubleMoebiusCoeff X r * F r := by
  classical
  let P := selbergShortCompleteRangePairSupport X
  let R := Finset.Icc 1 (X * X)
  let g := selbergShortCompleteRangePairProduct
  let w := selbergShortCompleteRangePairWeight X
  have hmaps : ∀ p ∈ P, g p ∈ R := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    exact Finset.mem_Icc.mpr
      ⟨Nat.mul_pos (Finset.mem_Icc.mp hp1).1
          (Finset.mem_Icc.mp hp2).1,
        Nat.mul_le_mul (Finset.mem_Icc.mp hp1).2
          (Finset.mem_Icc.mp hp2).2⟩
  have hfiber :
      (∑ p ∈ P, w p * F (g p)) =
        ∑ r ∈ R, ∑ p ∈ P.filter (fun p => g p = r),
          w p * F (g p) := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps (fun p => w p * F (g p))
  change (∑ p ∈ P, w p * F (g p)) = _
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro r _hr
  calc
    (∑ p ∈ P.filter (fun p => g p = r), w p * F (g p)) =
        ∑ p ∈ P.filter (fun p => g p = r), w p * F r := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = (∑ p ∈ P.filter (fun p => g p = r), w p) * F r := by
      rw [Finset.sum_mul]
    _ = selbergShortDoubleMoebiusCoeff X r * F r := by
      rfl

/-- A four-index mollifier sum whose kernel depends only on the two represented
products is exactly the corresponding two-index quadratic form in the
collected coefficients `selbergShortDoubleMoebiusCoeff`. -/
theorem sum_completeRangeQuadrupleWeight_mul_kernel_eq_doubleCollected
    (X : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ q ∈ selbergShortCompleteRangeQuadrupleSupport X,
        selbergShortCompleteRangeQuadrupleWeight X q *
          F (selbergShortCompleteRangePairProduct q.1)
            (selbergShortCompleteRangePairProduct q.2)) =
      ∑ r ∈ Finset.Icc 1 (X * X),
        ∑ s ∈ Finset.Icc 1 (X * X),
          selbergShortDoubleMoebiusCoeff X r *
            selbergShortDoubleMoebiusCoeff X s * F r s := by
  classical
  let P := selbergShortCompleteRangePairSupport X
  let g := selbergShortCompleteRangePairProduct
  let w := selbergShortCompleteRangePairWeight X
  have hsupport :
      selbergShortCompleteRangeQuadrupleSupport X = P.product P := by
    rfl
  rw [hsupport]
  change (∑ q ∈ P.product P,
      w q.1 * w q.2 * F (g q.1) (g q.2)) = _
  calc
    (∑ q ∈ P.product P,
        w q.1 * w q.2 * F (g q.1) (g q.2)) =
        ∑ p ∈ P, ∑ q ∈ P, w p * w q * F (g p) (g q) := by
      exact Finset.sum_product P P
        (fun q : (ℕ × ℕ) × (ℕ × ℕ) =>
          w q.1 * w q.2 * F (g q.1) (g q.2))
    _ =
        ∑ p ∈ P, w p *
          ∑ q ∈ P, w q * F (g p) (g q) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      ring
    _ = ∑ p ∈ P, w p *
          ∑ s ∈ Finset.Icc 1 (X * X),
            selbergShortDoubleMoebiusCoeff X s * F (g p) s := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [sum_completeRangePairWeight_mul_kernel_eq_collected]
    _ = ∑ r ∈ Finset.Icc 1 (X * X),
          selbergShortDoubleMoebiusCoeff X r *
            (∑ s ∈ Finset.Icc 1 (X * X),
              selbergShortDoubleMoebiusCoeff X s * F r s) := by
      simpa only [P, w, g] using
        (sum_completeRangePairWeight_mul_kernel_eq_collected X
          (fun r => ∑ s ∈ Finset.Icc 1 (X * X),
            selbergShortDoubleMoebiusCoeff X s * F r s))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _hs
      ring

/-- Positive multiples of `r` up to `N` are exactly the image of
`1,...,N/r` under multiplication by `r`. -/
theorem Icc_one_filter_dvd_eq_image_mul
    {N r : ℕ} (hr : 0 < r) :
    (Finset.Icc 1 N).filter (fun k => r ∣ k) =
      (Finset.Icc 1 (N / r)).image (fun j => r * j) := by
  classical
  ext k
  constructor
  · intro hk
    rcases Finset.mem_filter.mp hk with ⟨hkIcc, hdvd⟩
    rcases hdvd with ⟨j, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Nat.pos_of_mul_pos_left (Finset.mem_Icc.mp hkIcc).1
    · rw [Nat.le_div_iff_mul_le hr]
      simpa [Nat.mul_comm] using (Finset.mem_Icc.mp hkIcc).2
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      constructor
      · exact Nat.mul_pos hr (Finset.mem_Icc.mp hj).1
      · have hjUpper : j * r ≤ N :=
          (Nat.le_div_iff_mul_le hr).mp (Finset.mem_Icc.mp hj).2
        simpa [Nat.mul_comm] using hjUpper
    · exact dvd_mul_right r j

/-- The harmonic mass of positive multiples of `r` up to `N` is exactly
`H_(N/r) / r`. -/
theorem selbergShortLcmHarmonicKernel_one_eq_inv_mul_harmonic
    {N r : ℕ} (hr : 0 < r) :
    selbergShortLcmHarmonicKernel 1 N r =
      (r : ℝ)⁻¹ * (harmonic (N / r) : ℝ) := by
  classical
  rw [selbergShortLcmHarmonicKernel,
    Icc_one_filter_dvd_eq_image_mul hr]
  have hinj : Set.InjOn (fun j : ℕ => r * j) (Finset.Icc 1 (N / r)) := by
    intro a _ha b _hb hab
    exact Nat.mul_left_cancel hr hab
  calc
    (∑ k ∈ (Finset.Icc 1 (N / r)).image (fun j => r * j),
        (k : ℝ)⁻¹) =
        ∑ j ∈ Finset.Icc 1 (N / r), ((r * j : ℕ) : ℝ)⁻¹ := by
      exact Finset.sum_image hinj
    _ = ∑ j ∈ Finset.Icc 1 (N / r),
          (r : ℝ)⁻¹ * (j : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro j _hj
      simp only [Nat.cast_mul, mul_inv_rev]
      ring
    _ = (r : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 (N / r), (j : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
    _ = (r : ℝ)⁻¹ * (harmonic (N / r) : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]

/-- Taking the product of the two complete divisor-pair fibers is equivalent
to imposing one least-common-multiple divisibility condition. -/
theorem selbergShortCompleteRangePairs_product_eq_quadruples
    (X k : ℕ) :
    (selbergShortCompleteRangePairs X k).product
        (selbergShortCompleteRangePairs X k) =
      selbergShortCompleteRangeQuadruples X k := by
  classical
  ext q
  simp only [selbergShortCompleteRangePairs,
    selbergShortCompleteRangeQuadruples, Finset.mem_filter,
    Nat.lcm_dvd_iff]
  aesop

/-- The square of the complete double mollifier coefficient is the signed
quadruple sum with the exact least-common-multiple divisibility kernel. -/
theorem selbergShortCompleteRangeCoeff_sq_eq_lcmSum
    (X k : ℕ) :
    (∑ p ∈ selbergShortCompleteRangePairs X k,
        selbergMoebiusCoeff X p.1 * selbergMoebiusCoeff X p.2) ^ 2 =
      ∑ q ∈ selbergShortCompleteRangeQuadruples X k,
        (selbergMoebiusCoeff X q.1.1 * selbergMoebiusCoeff X q.1.2) *
          (selbergMoebiusCoeff X q.2.1 * selbergMoebiusCoeff X q.2.2) := by
  classical
  rw [pow_two, Finset.sum_mul]
  calc
    (∑ p ∈ selbergShortCompleteRangePairs X k,
        (selbergMoebiusCoeff X p.1 * selbergMoebiusCoeff X p.2) *
          ∑ q ∈ selbergShortCompleteRangePairs X k,
            selbergMoebiusCoeff X q.1 * selbergMoebiusCoeff X q.2) =
        ∑ p ∈ selbergShortCompleteRangePairs X k,
          ∑ q ∈ selbergShortCompleteRangePairs X k,
            (selbergMoebiusCoeff X p.1 * selbergMoebiusCoeff X p.2) *
              (selbergMoebiusCoeff X q.1 * selbergMoebiusCoeff X q.2) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.mul_sum]
    _ = ∑ q ∈ (selbergShortCompleteRangePairs X k).product
          (selbergShortCompleteRangePairs X k),
          (selbergMoebiusCoeff X q.1.1 * selbergMoebiusCoeff X q.1.2) *
            (selbergMoebiusCoeff X q.2.1 * selbergMoebiusCoeff X q.2.2) := by
      exact (Finset.sum_product
        (selbergShortCompleteRangePairs X k)
        (selbergShortCompleteRangePairs X k)
        (fun q : (ℕ × ℕ) × (ℕ × ℕ) =>
          (selbergMoebiusCoeff X q.1.1 * selbergMoebiusCoeff X q.1.2) *
            (selbergMoebiusCoeff X q.2.1 * selbergMoebiusCoeff X q.2.2))).symm
    _ = _ := by
      rw [selbergShortCompleteRangePairs_product_eq_quadruples]

/-- In the complete range, the square of the real collected convolution is
the exact signed least-common-multiple quadruple sum. -/
theorem selbergShortCollectedDirichletConvolution_sq_eq_lcmSum
    {N X k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    (selbergShortCollectedDirichletConvolution N X k) ^ 2 =
      ∑ q ∈ selbergShortCompleteRangeQuadruples X k,
        (selbergMoebiusCoeff X q.1.1 * selbergMoebiusCoeff X q.1.2) *
          (selbergMoebiusCoeff X q.2.1 * selbergMoebiusCoeff X q.2.2) := by
  rw [selbergShortCollectedDirichletConvolution_eq_completeRange hk1 hkN]
  exact selbergShortCompleteRangeCoeff_sq_eq_lcmSum X k

/-- The critical-line normalization turns the complex square norm of a
collected coefficient into the real convolution square weighted by `1/k`. -/
theorem normSq_selbergShortDirichletCollectedCoeff_eq_convolution_sq_mul_inv
    {N X k : ℕ} (hk : 1 ≤ k) :
    Complex.normSq (selbergShortDirichletCollectedCoeff N X k) =
      (selbergShortCollectedDirichletConvolution N X k) ^ 2 * (k : ℝ)⁻¹ := by
  rw [selbergShortDirichletCollectedCoeff_eq_convolution,
    Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_inv,
    Complex.normSq_ofReal]
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hsqrt : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) := by
    nlinarith [Real.sq_sqrt hk0]
  rw [hsqrt]
  ring

/-- Summing the complete-range square energy and exchanging the two finite
sums produces the exact least-common-multiple harmonic kernel.  This retains
all signs of the Moebius weights; no absolute-value or divisor-count loss has
been introduced. -/
theorem sum_selbergShortCollectedDirichletConvolution_sq_mul_inv_eq_lcmKernel
    {N X L U : ℕ} (hL : 1 ≤ L) (hUN : U ≤ N) :
    (∑ k ∈ Finset.Icc L U,
        (selbergShortCollectedDirichletConvolution N X k) ^ 2 *
          (k : ℝ)⁻¹) =
      ∑ q ∈ selbergShortCompleteRangeQuadrupleSupport X,
        selbergShortCompleteRangeQuadrupleWeight X q *
          selbergShortLcmHarmonicKernel L U
            (selbergShortCompleteRangeLcm q) := by
  classical
  let K := Finset.Icc L U
  let Q := selbergShortCompleteRangeQuadrupleSupport X
  let w := selbergShortCompleteRangeQuadrupleWeight X
  let m := selbergShortCompleteRangeLcm
  have hcomplete : ∀ k ∈ K,
      (selbergShortCollectedDirichletConvolution N X k) ^ 2 =
        ∑ q ∈ Q.filter (fun q => m q ∣ k), w q := by
    intro k hk
    have hkData : L ≤ k ∧ k ≤ U := Finset.mem_Icc.mp hk
    have hk1 : 1 ≤ k := hL.trans hkData.1
    have hkN : k ≤ N := hkData.2.trans hUN
    simpa only [Q, w, m, selbergShortCompleteRangeQuadrupleSupport,
      selbergShortCompleteRangeQuadrupleWeight,
      selbergShortCompleteRangeLcm,
      selbergShortCompleteRangeQuadruples] using
        (selbergShortCollectedDirichletConvolution_sq_eq_lcmSum
          (N := N) (X := X) hk1 hkN)
  change (∑ k ∈ K,
      (selbergShortCollectedDirichletConvolution N X k) ^ 2 *
        (k : ℝ)⁻¹) = _
  calc
    (∑ k ∈ K,
        (selbergShortCollectedDirichletConvolution N X k) ^ 2 *
          (k : ℝ)⁻¹) =
        ∑ k ∈ K, (∑ q ∈ Q.filter (fun q => m q ∣ k), w q) *
          (k : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hcomplete k hk]
    _ = ∑ k ∈ K, ∑ q ∈ Q.filter (fun q => m q ∣ k),
          w q * (k : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_mul]
    _ = ∑ k ∈ K, ∑ q ∈ Q,
          if m q ∣ k then w q * (k : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_filter]
    _ = ∑ q ∈ Q, ∑ k ∈ K,
          if m q ∣ k then w q * (k : ℝ)⁻¹ else 0 :=
      Finset.sum_comm
    _ = ∑ q ∈ Q, w q *
          ∑ k ∈ K.filter (fun k => m q ∣ k), (k : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Finset.mul_sum, Finset.sum_filter]
    _ = _ := by
      rfl

/-- On any interval contained in the complete range, the actual collected
complex coefficient energy equals the signed least-common-multiple harmonic
kernel. -/
theorem sum_normSq_selbergShortDirichletCollectedCoeff_eq_lcmKernel
    {N X L U : ℕ} (hL : 1 ≤ L) (hUN : U ≤ N) :
    (∑ k ∈ Finset.Icc L U,
        Complex.normSq (selbergShortDirichletCollectedCoeff N X k)) =
      ∑ q ∈ selbergShortCompleteRangeQuadrupleSupport X,
        selbergShortCompleteRangeQuadrupleWeight X q *
          selbergShortLcmHarmonicKernel L U
            (selbergShortCompleteRangeLcm q) := by
  calc
    (∑ k ∈ Finset.Icc L U,
        Complex.normSq (selbergShortDirichletCollectedCoeff N X k)) =
        ∑ k ∈ Finset.Icc L U,
          (selbergShortCollectedDirichletConvolution N X k) ^ 2 *
            (k : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact normSq_selbergShortDirichletCollectedCoeff_eq_convolution_sq_mul_inv
        (hL.trans (Finset.mem_Icc.mp hk).1)
    _ = _ :=
      sum_selbergShortCollectedDirichletConvolution_sq_mul_inv_eq_lcmKernel
        hL hUN

/-- Over the whole complete range `1 <= k <= N`, the lcm kernel has the closed
form `H_(N/r) / r`.  This is the exact signed Selberg quadratic form before any
arithmetic estimate is applied. -/
theorem sum_normSq_selbergShortDirichletCollectedCoeff_completeRange_eq_lcmHarmonic
    (N X : ℕ) :
    (∑ k ∈ Finset.Icc 1 N,
        Complex.normSq (selbergShortDirichletCollectedCoeff N X k)) =
      ∑ q ∈ selbergShortCompleteRangeQuadrupleSupport X,
        selbergShortCompleteRangeQuadrupleWeight X q *
          ((selbergShortCompleteRangeLcm q : ℝ)⁻¹ *
            (harmonic (N / selbergShortCompleteRangeLcm q) : ℝ)) := by
  rw [sum_normSq_selbergShortDirichletCollectedCoeff_eq_lcmKernel
    (N := N) (X := X) (L := 1) (U := N) le_rfl le_rfl]
  apply Finset.sum_congr rfl
  intro q hq
  have hqData := Finset.mem_product.mp hq
  have hqLeft := Finset.mem_product.mp hqData.1
  have hqRight := Finset.mem_product.mp hqData.2
  have hleftPos : 0 < q.1.1 * q.1.2 :=
    Nat.mul_pos (Finset.mem_Icc.mp hqLeft.1).1
      (Finset.mem_Icc.mp hqLeft.2).1
  have hrightPos : 0 < q.2.1 * q.2.2 :=
    Nat.mul_pos (Finset.mem_Icc.mp hqRight.1).1
      (Finset.mem_Icc.mp hqRight.2).1
  have hlcm : 0 < selbergShortCompleteRangeLcm q :=
    Nat.lcm_pos hleftPos hrightPos
  rw [selbergShortLcmHarmonicKernel_one_eq_inv_mul_harmonic hlcm]

/-- The same complete-range energy after collecting each pair product first.
This is the standard two-index signed Selberg quadratic form in the finite
coefficients `selbergShortDoubleMoebiusCoeff`. -/
theorem sum_normSq_selbergShortDirichletCollectedCoeff_completeRange_eq_doubleLcmHarmonic
    (N X : ℕ) :
    (∑ k ∈ Finset.Icc 1 N,
        Complex.normSq (selbergShortDirichletCollectedCoeff N X k)) =
      ∑ r ∈ Finset.Icc 1 (X * X),
        ∑ s ∈ Finset.Icc 1 (X * X),
          selbergShortDoubleMoebiusCoeff X r *
            selbergShortDoubleMoebiusCoeff X s *
              ((Nat.lcm r s : ℝ)⁻¹ *
                (harmonic (N / Nat.lcm r s) : ℝ)) := by
  rw [sum_normSq_selbergShortDirichletCollectedCoeff_completeRange_eq_lcmHarmonic]
  simpa only [selbergShortCompleteRangeQuadrupleWeight,
    selbergShortCompleteRangePairWeight,
    selbergShortCompleteRangeLcm,
    selbergShortCompleteRangePairProduct] using
      (sum_completeRangeQuadrupleWeight_mul_kernel_eq_doubleCollected X
        (fun r s => (Nat.lcm r s : ℝ)⁻¹ *
          (harmonic (N / Nat.lcm r s) : ℝ)))

/-- Removing the constant `k = 1` mode subtracts exactly one from the complete
signed lcm-harmonic quadratic form. -/
theorem sum_normSq_selbergShortDirichletCollectedCoeff_nonconstantRange_eq_lcmHarmonic_sub_one
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    (∑ k ∈ Finset.Ioc 1 N,
        Complex.normSq (selbergShortDirichletCollectedCoeff N X k)) =
      (∑ q ∈ selbergShortCompleteRangeQuadrupleSupport X,
        selbergShortCompleteRangeQuadrupleWeight X q *
          ((selbergShortCompleteRangeLcm q : ℝ)⁻¹ *
            (harmonic (N / selbergShortCompleteRangeLcm q) : ℝ))) - 1 := by
  have hOneMem : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hsplit :
      (∑ k ∈ Finset.Icc 1 N,
          Complex.normSq (selbergShortDirichletCollectedCoeff N X k)) =
        Complex.normSq (selbergShortDirichletCollectedCoeff N X 1) +
          ∑ k ∈ Finset.Ioc 1 N,
            Complex.normSq (selbergShortDirichletCollectedCoeff N X k) := by
    rw [← Finset.Icc_erase_left]
    have hsum := Finset.sum_erase_add (Finset.Icc 1 N)
      (fun k : ℕ =>
        Complex.normSq (selbergShortDirichletCollectedCoeff N X k)) hOneMem
    simpa only [add_comm] using hsum.symm
  have hOne :
      Complex.normSq (selbergShortDirichletCollectedCoeff N X 1) = 1 := by
    rw [selbergShortDirichletCollectedCoeff_one hN hX]
    norm_num
  rw [sum_normSq_selbergShortDirichletCollectedCoeff_completeRange_eq_lcmHarmonic
    N X, hOne] at hsplit
  linarith

/-- The nonconstant complete-range energy in the collected two-index form.
The only removed term is the exact constant coefficient at `k = 1`. -/
theorem sum_normSq_selbergShortDirichletCollectedCoeff_nonconstantRange_eq_doubleLcmHarmonic_sub_one
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    (∑ k ∈ Finset.Ioc 1 N,
        Complex.normSq (selbergShortDirichletCollectedCoeff N X k)) =
      (∑ r ∈ Finset.Icc 1 (X * X),
        ∑ s ∈ Finset.Icc 1 (X * X),
          selbergShortDoubleMoebiusCoeff X r *
            selbergShortDoubleMoebiusCoeff X s *
              ((Nat.lcm r s : ℝ)⁻¹ *
                (harmonic (N / Nat.lcm r s) : ℝ))) - 1 := by
  rw [← sum_normSq_selbergShortDirichletCollectedCoeff_completeRange_eq_doubleLcmHarmonic
    N X]
  have hOneMem : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hsum := Finset.sum_erase_add (Finset.Icc 1 N)
    (fun k : ℕ =>
      Complex.normSq (selbergShortDirichletCollectedCoeff N X k)) hOneMem
  rw [Finset.Icc_erase_left] at hsum
  change (∑ k ∈ Finset.Ioc 1 N,
      Complex.normSq (selbergShortDirichletCollectedCoeff N X k)) +
        Complex.normSq (selbergShortDirichletCollectedCoeff N X 1) =
      ∑ k ∈ Finset.Icc 1 N,
        Complex.normSq (selbergShortDirichletCollectedCoeff N X k) at hsum
  rw [selbergShortDirichletCollectedCoeff_one hN hX] at hsum
  norm_num at hsum
  linarith

end HardyTheorem
