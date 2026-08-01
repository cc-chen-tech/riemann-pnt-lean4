import HardyTheorem.SelbergSqrtZetaLowRangeSliding
import HardyTheorem.SelbergShortCompleteRangeArithmetic

open Complex
open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# Finite collected coefficient for the square-root zeta mollifier

This is the coefficient layer belonging to the finite product

`(sum_{m <= N} m^{-s}) * M_X(s)^2`.

Unlike the unrestricted arithmetic convolution, it retains the zeta cutoff
`m <= N`.  The cutoff becomes automatic only in the complete range `k <= N`.
-/

/-- The coefficient of a triple `(m,d,l)` in the finite square-root-zeta
mollified Dirichlet polynomial on the critical line. -/
noncomputable def selbergSqrtZetaShortDirichletTripleCoeff
    (X : ℕ) (p : ℕ × (ℕ × ℕ)) : ℂ :=
  (selbergSqrtZetaTaperedCoeff X p.2.1 : ℂ) *
    (selbergSqrtZetaTaperedCoeff X p.2.2 : ℂ) *
    (Real.sqrt
      ((p.1 * p.2.1 * p.2.2 : ℕ) : ℝ) : ℂ)⁻¹

/-- The actual finite collected coefficient after grouping triples with
product `k`. -/
noncomputable def selbergSqrtZetaShortDirichletCollectedCoeff
    (N X k : ℕ) : ℂ :=
  ∑ p ∈ selbergShortDirichletTriples N X k,
    selbergSqrtZetaShortDirichletTripleCoeff X p

/-- The real pair sum left after the zeta cutoff becomes automatic. -/
noncomputable def selbergSqrtZetaShortCompleteRangePairSum
    (X k : ℕ) : ℝ :=
  ∑ p ∈ selbergShortCompleteRangePairs X k,
    selbergSqrtZetaTaperedCoeff X p.1 *
      selbergSqrtZetaTaperedCoeff X p.2

/-- In the complete zeta range `k <= N`, the finite collected coefficient is
the complete pair sum divided by `sqrt k`. -/
theorem selbergSqrtZetaShortDirichletCollectedCoeff_eq_pairSum
    {N X k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    selbergSqrtZetaShortDirichletCollectedCoeff N X k =
      (selbergSqrtZetaShortCompleteRangePairSum X k : ℂ) *
        (Real.sqrt (k : ℝ) : ℂ)⁻¹ := by
  classical
  let S := selbergShortCompleteRangePairs X k
  let g : ℕ × ℕ → ℕ × (ℕ × ℕ) := fun p =>
    (k / (p.1 * p.2), (p.1, p.2))
  have hgInj : ∀ a ∈ S, ∀ b ∈ S, g a = g b → a = b := by
    intro a _ha b _hb hab
    exact congrArg Prod.snd hab
  rw [selbergSqrtZetaShortDirichletCollectedCoeff,
    selbergShortDirichletTriples_eq_completeRangePairs_image hk hkN]
  change
    (∑ q ∈ S.image g,
      selbergSqrtZetaShortDirichletTripleCoeff X q) = _
  calc
    (∑ q ∈ S.image g,
        selbergSqrtZetaShortDirichletTripleCoeff X q) =
        ∑ p ∈ S,
          selbergSqrtZetaShortDirichletTripleCoeff X (g p) := by
      exact Finset.sum_image
        (f := fun q : ℕ × (ℕ × ℕ) =>
          selbergSqrtZetaShortDirichletTripleCoeff X q) hgInj
    _ = ∑ p ∈ S,
        ((selbergSqrtZetaTaperedCoeff X p.1 *
          selbergSqrtZetaTaperedCoeff X p.2 : ℝ) : ℂ) *
            (Real.sqrt (k : ℝ) : ℂ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpData : p ∈ selbergShortCompleteRangePairs X k := by
        simpa only [S] using hp
      have hdiv : p.1 * p.2 ∣ k :=
        (Finset.mem_filter.mp hpData).2
      have hprod : (k / (p.1 * p.2)) * p.1 * p.2 = k := by
        calc
          (k / (p.1 * p.2)) * p.1 * p.2 =
              (k / (p.1 * p.2)) * (p.1 * p.2) := by
                simp [Nat.mul_assoc]
          _ = k := Nat.div_mul_cancel hdiv
      unfold g selbergSqrtZetaShortDirichletTripleCoeff
      simp only
      rw [hprod]
      push_cast
      ring
    _ = (selbergSqrtZetaShortCompleteRangePairSum X k : ℂ) *
        (Real.sqrt (k : ℝ) : ℂ)⁻¹ := by
      rw [← Finset.sum_mul]
      unfold selbergSqrtZetaShortCompleteRangePairSum
      simp only [S]
      push_cast
      rfl

/-- In the complete mollifier range, the finite pair sum is the arithmetic
coefficient obtained by convolving the squared mollifier with zeta. -/
theorem selbergSqrtZetaShortCompleteRangePairSum_eq_arithmetic
    {X k : ℕ} (hk : 1 ≤ k) (hkX : k ≤ X) :
    selbergSqrtZetaShortCompleteRangePairSum X k =
      (((selbergShortTaperedSqrtZeta X *
          selbergShortTaperedSqrtZeta X) *
        (ArithmeticFunction.zeta :
          ArithmeticFunction ℝ)) k) := by
  classical
  have hk0 : k ≠ 0 := Nat.ne_of_gt (by omega)
  have hset :
      selbergShortCompleteRangePairs X k =
        k.divisors.biUnion (fun d => d.divisorsAntidiagonal) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpRange, hpDvd⟩
      rcases Finset.mem_product.mp hpRange with ⟨hp1X, hp2X⟩
      have hprod0 : p.1 * p.2 ≠ 0 :=
        Nat.mul_ne_zero
          (Nat.ne_of_gt (Finset.mem_Icc.mp hp1X).1)
          (Nat.ne_of_gt (Finset.mem_Icc.mp hp2X).1)
      apply Finset.mem_biUnion.mpr
      refine ⟨p.1 * p.2, ?_, ?_⟩
      · exact Nat.mem_divisors.mpr ⟨hpDvd, hk0⟩
      · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hprod0⟩
    · intro hp
      rcases Finset.mem_biUnion.mp hp with ⟨d, hd, hpd⟩
      rcases Nat.mem_divisors.mp hd with ⟨hdDvd, _hk0⟩
      rcases Nat.mem_divisorsAntidiagonal.mp hpd with
        ⟨hprod, hd0⟩
      have hpDvd : p.1 * p.2 ∣ k := by
        simpa [hprod] using hdDvd
      have hprod0 : p.1 * p.2 ≠ 0 := by
        simpa [hprod] using hd0
      have hp1pos : 1 ≤ p.1 :=
        Nat.one_le_iff_ne_zero.mpr (left_ne_zero_of_mul hprod0)
      have hp2pos : 1 ≤ p.2 :=
        Nat.one_le_iff_ne_zero.mpr (right_ne_zero_of_mul hprod0)
      have hp1Dvd : p.1 ∣ k :=
        dvd_trans (dvd_mul_right p.1 p.2) hpDvd
      have hp2Dvd : p.2 ∣ k := by
        apply dvd_trans (dvd_mul_left p.2 p.1)
        simpa [Nat.mul_comm] using hpDvd
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr
              ⟨hp1pos, (Nat.le_of_dvd hk hp1Dvd).trans hkX⟩,
            Finset.mem_Icc.mpr
              ⟨hp2pos, (Nat.le_of_dvd hk hp2Dvd).trans hkX⟩⟩,
          hpDvd⟩
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
  rw [hset, Finset.sum_biUnion hdisjoint,
    ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rcases Nat.mem_divisors.mp hd with ⟨hdDvd, _hk0⟩
  rcases Nat.mem_divisorsAntidiagonal.mp hp with
    ⟨hprod, hd0⟩
  have hprod0 : p.1 * p.2 ≠ 0 := by
    simpa [hprod] using hd0
  have hp1pos : 1 ≤ p.1 :=
    Nat.one_le_iff_ne_zero.mpr (left_ne_zero_of_mul hprod0)
  have hp2pos : 1 ≤ p.2 :=
    Nat.one_le_iff_ne_zero.mpr (right_ne_zero_of_mul hprod0)
  have hp1Dvd : p.1 ∣ k := by
    apply dvd_trans _ hdDvd
    exact ⟨p.2, hprod.symm⟩
  have hp2Dvd : p.2 ∣ k := by
    apply dvd_trans _ hdDvd
    exact ⟨p.1, by simpa [Nat.mul_comm] using hprod.symm⟩
  rw [selbergShortTaperedSqrtZeta_apply,
    if_pos (Finset.mem_Icc.mpr
      ⟨hp1pos, (Nat.le_of_dvd hk hp1Dvd).trans hkX⟩),
    selbergShortTaperedSqrtZeta_apply,
    if_pos (Finset.mem_Icc.mpr
      ⟨hp2pos, (Nat.le_of_dvd hk hp2Dvd).trans hkX⟩)]

/-- In the common complete range for the zeta truncation and mollifier
cutoff, the actual finite collected coefficient is the unrestricted
arithmetic coefficient. -/
theorem selbergSqrtZetaShortDirichletCollectedCoeff_eq_arithmetic
    {N X k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) (hkX : k ≤ X) :
    selbergSqrtZetaShortDirichletCollectedCoeff N X k =
      selbergSqrtZetaArithmeticDirichletCoeff X k := by
  rw [selbergSqrtZetaShortDirichletCollectedCoeff_eq_pairSum hk hkN,
    selbergSqrtZetaShortCompleteRangePairSum_eq_arithmetic hk hkX]
  rfl

/-- Consequently the actual finite collected coefficient has the explicit
low-range formula proved in the arithmetic layer. -/
theorem selbergSqrtZetaShortDirichletCollectedCoeff_eq_lowRange
    {N X k : ℕ} (hX : 1 < X) (hk : 1 < k)
    (hkN : k ≤ N) (hkX : k ≤ X) :
    selbergSqrtZetaShortDirichletCollectedCoeff N X k =
      selbergSqrtZetaLowRangeDirichletCoeff X k := by
  rw [selbergSqrtZetaShortDirichletCollectedCoeff_eq_arithmetic
      hk.le hkN hkX,
    selbergSqrtZetaArithmeticDirichletCoeff_eq_lowRange
      hX hk hkX]

/-- The actual finite collected coefficient has constant sliding energy
throughout the common complete range `k <= min N X`. -/
theorem sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_lowRange_le
    {N X : ℕ} (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (min N X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (15 : ℝ) / 4 * H ^ 2 := by
  calc
    (∑ k ∈ Finset.Ioc 1 (min N X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) =
        ∑ k ∈ Finset.Ioc 1 (min N X),
          Complex.normSq
            (MathlibAux.slidingExponentialCoefficient H
              (selbergSqrtZetaLowRangeDirichletCoeff X)
              selbergShortDirichletCollectedFrequency k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkData := Finset.mem_Ioc.mp hk
      have hcoeff :=
        selbergSqrtZetaShortDirichletCollectedCoeff_eq_lowRange
          hX hkData.1
          (hkData.2.trans (min_le_left N X))
          (hkData.2.trans (min_le_right N X))
      unfold MathlibAux.slidingExponentialCoefficient
      rw [hcoeff]
    _ ≤ ∑ k ∈ Finset.Ioc 1 X,
          Complex.normSq
            (MathlibAux.slidingExponentialCoefficient H
              (selbergSqrtZetaLowRangeDirichletCoeff X)
              selbergShortDirichletCollectedFrequency k) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact Finset.mem_Ioc.mpr
          ⟨(Finset.mem_Ioc.mp hk).1,
            (Finset.mem_Ioc.mp hk).2.trans (min_le_right N X)⟩
      · intro k _hk _hnot
        exact Complex.normSq_nonneg _
    _ ≤ (15 : ℝ) / 4 * H ^ 2 :=
      sum_normSq_sliding_selbergSqrtZetaLowRangeDirichletCoeff_le
        hX hlarge H

/-- The full sliding energy splits into the now-constant low range and one
remaining truncated high range. -/
theorem sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_highRange
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (15 : ℝ) / 4 * H ^ 2 +
        ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
          Complex.normSq
            (MathlibAux.slidingExponentialCoefficient H
              (selbergSqrtZetaShortDirichletCollectedCoeff N X)
              selbergShortDirichletCollectedFrequency k) := by
  have hXone : 1 ≤ X := hX.le
  have honeMin : 1 ≤ min N X := Nat.le_min.mpr ⟨hN, hXone⟩
  have hminSupport : min N X ≤ N * X * X := by
    calc
      min N X ≤ N := min_le_left N X
      _ = N * 1 * 1 := by simp
      _ ≤ N * X * X :=
        Nat.mul_le_mul (Nat.mul_le_mul_left N hXone) hXone
  have hsplit :
      Finset.Ioc 1 (min N X) ∪
          Finset.Ioc (min N X) (N * X * X) =
        Finset.Ioc 1 (N * X * X) :=
    Finset.Ioc_union_Ioc_eq_Ioc honeMin hminSupport
  have hdisjoint :
      Disjoint (Finset.Ioc 1 (min N X))
        (Finset.Ioc (min N X) (N * X * X)) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  rw [← hsplit, Finset.sum_union hdisjoint]
  exact add_le_add
    (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_lowRange_le
      hX hlarge H)
    (le_refl _)

end HardyTheorem
