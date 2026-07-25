import HardyTheorem.SelbergSqrtZetaHighRangeEnergy
import HardyTheorem.SelbergShortCompleteRangeEnergy
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds

open scoped BigOperators

namespace HardyTheorem

/-!
# Restricted divisor-pair moments for the square-root-zeta mollifier

This file studies the unsigned arithmetic majorant

`#{(d,l) : 1 ≤ d,l ≤ X, d*l ∣ k}`.

The pointwise divisor bound below is useful for comparison, but the exact
finite lcm-harmonic expansion retains substantially more averaging structure.
No asymptotic estimate is asserted here.
-/

/-- The number of pairs in the fixed box with a prescribed product. -/
noncomputable def selbergShortRestrictedPairProductMultiplicity
    (X r : ℕ) : ℕ :=
  ((selbergShortCompleteRangePairSupport X).filter
    (fun p => selbergShortCompleteRangePairProduct p = r)).card

/-- Every restricted pair whose product divides a nonzero `k` consists of
two divisors of `k`. -/
theorem selbergShortCompleteRangePairs_subset_divisors_product
    {X k : ℕ} (hk : k ≠ 0) :
    selbergShortCompleteRangePairs X k ⊆
      k.divisors.product k.divisors := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpBox, hpDvd⟩
  rcases Finset.mem_product.mp hpBox with ⟨hpLeft, hpRight⟩
  have hleftDvdProduct : p.1 ∣ p.1 * p.2 := ⟨p.2, rfl⟩
  have hrightDvdProduct : p.2 ∣ p.1 * p.2 := by
    exact ⟨p.1, Nat.mul_comm _ _⟩
  exact Finset.mem_product.mpr
    ⟨Nat.mem_divisors.mpr ⟨hleftDvdProduct.trans hpDvd, hk⟩,
      Nat.mem_divisors.mpr ⟨hrightDvdProduct.trans hpDvd, hk⟩⟩

/-- The restricted pair count is pointwise at most the square of the divisor
count.  This is deliberately only a pointwise comparison. -/
theorem card_selbergShortCompleteRangePairs_le_divisors_sq
    {X k : ℕ} (hk : k ≠ 0) :
    (selbergShortCompleteRangePairs X k).card ≤
      k.divisors.card ^ 2 := by
  calc
    (selbergShortCompleteRangePairs X k).card ≤
        (k.divisors.product k.divisors).card :=
      Finset.card_le_card
        (selbergShortCompleteRangePairs_subset_divisors_product hk)
    _ = k.divisors.card ^ 2 := by simp [pow_two]

/-- Collecting the restricted pair count by the represented product gives an
exact finite divisor sum. -/
theorem card_selbergShortCompleteRangePairs_eq_sum_productMultiplicity
    (X k : ℕ) :
    (selbergShortCompleteRangePairs X k).card =
      ∑ r ∈ (Finset.Icc 1 (X * X)).filter (fun r => r ∣ k),
        selbergShortRestrictedPairProductMultiplicity X r := by
  classical
  let P := selbergShortCompleteRangePairSupport X
  let R := Finset.Icc 1 (X * X)
  let g := selbergShortCompleteRangePairProduct
  have hmaps : ∀ p ∈ P, g p ∈ R := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hpLeft, hpRight⟩
    exact Finset.mem_Icc.mpr
      ⟨Nat.mul_pos (Finset.mem_Icc.mp hpLeft).1
          (Finset.mem_Icc.mp hpRight).1,
        Nat.mul_le_mul (Finset.mem_Icc.mp hpLeft).2
          (Finset.mem_Icc.mp hpRight).2⟩
  have hfiber :
      (∑ p ∈ P, if g p ∣ k then 1 else 0) =
        ∑ r ∈ R, ∑ p ∈ P.filter (fun p => g p = r),
          if g p ∣ k then 1 else 0 := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps
      (fun p => if g p ∣ k then 1 else 0)
  calc
    (selbergShortCompleteRangePairs X k).card =
        ∑ p ∈ P, if g p ∣ k then 1 else 0 := by
      change (P.filter (fun p => g p ∣ k)).card =
        ∑ p ∈ P, if g p ∣ k then 1 else 0
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ r ∈ R, ∑ p ∈ P.filter (fun p => g p = r),
          if g p ∣ k then 1 else 0 := hfiber
    _ = ∑ r ∈ R, if r ∣ k then
          selbergShortRestrictedPairProductMultiplicity X r else 0 := by
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hr : r ∣ k
      · simp only [hr, if_true]
        change (∑ p ∈ P.filter (fun p => g p = r),
            if g p ∣ k then 1 else 0) =
          (P.filter (fun p => g p = r)).card
        calc
          (∑ p ∈ P.filter (fun p => g p = r),
              if g p ∣ k then 1 else 0) =
              ∑ _p ∈ P.filter (fun p => g p = r), 1 := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [(Finset.mem_filter.mp hp).2, if_pos hr]
          _ = (P.filter (fun p => g p = r)).card := by simp
      · simp only [hr, if_false]
        apply Finset.sum_eq_zero
        intro p hp
        rw [(Finset.mem_filter.mp hp).2, if_neg hr]
    _ = ∑ r ∈ R.filter (fun r => r ∣ k),
          selbergShortRestrictedPairProductMultiplicity X r := by
      rw [Finset.sum_filter]

/-- A finite sum over the pair box can be collected exactly by the represented
product, with the unsigned product multiplicity as coefficient. -/
theorem sum_completeRangePair_kernel_eq_productMultiplicity
    (X : ℕ) (F : ℕ → ℝ) :
    (∑ p ∈ selbergShortCompleteRangePairSupport X,
        F (selbergShortCompleteRangePairProduct p)) =
      ∑ r ∈ Finset.Icc 1 (X * X),
        (selbergShortRestrictedPairProductMultiplicity X r : ℝ) * F r := by
  classical
  let P := selbergShortCompleteRangePairSupport X
  let R := Finset.Icc 1 (X * X)
  let g := selbergShortCompleteRangePairProduct
  have hmaps : ∀ p ∈ P, g p ∈ R := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hpLeft, hpRight⟩
    exact Finset.mem_Icc.mpr
      ⟨Nat.mul_pos (Finset.mem_Icc.mp hpLeft).1
          (Finset.mem_Icc.mp hpRight).1,
        Nat.mul_le_mul (Finset.mem_Icc.mp hpLeft).2
          (Finset.mem_Icc.mp hpRight).2⟩
  have hfiber :
      (∑ p ∈ P, F (g p)) =
        ∑ r ∈ R, ∑ p ∈ P.filter (fun p => g p = r), F (g p) := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps (fun p => F (g p))
  change (∑ p ∈ P, F (g p)) = _
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro r _hr
  calc
    (∑ p ∈ P.filter (fun p => g p = r), F (g p)) =
        ∑ _p ∈ P.filter (fun p => g p = r), F r := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = (selbergShortRestrictedPairProductMultiplicity X r : ℝ) * F r := by
      simp only [selbergShortRestrictedPairProductMultiplicity, P, g,
        selbergShortCompleteRangePairProduct, Finset.sum_const,
        nsmul_eq_mul]

/-- A kernel depending only on the products of two pairs is exactly the
corresponding quadratic form in the unsigned product multiplicities. -/
theorem sum_completeRangeQuadruple_kernel_eq_doubleProductMultiplicity
    (X : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ q ∈ selbergShortCompleteRangeQuadrupleSupport X,
        F (selbergShortCompleteRangePairProduct q.1)
          (selbergShortCompleteRangePairProduct q.2)) =
      ∑ r ∈ Finset.Icc 1 (X * X),
        ∑ s ∈ Finset.Icc 1 (X * X),
          (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
            (selbergShortRestrictedPairProductMultiplicity X s : ℝ) *
              F r s := by
  classical
  let P := selbergShortCompleteRangePairSupport X
  let g := selbergShortCompleteRangePairProduct
  have hsupport :
      selbergShortCompleteRangeQuadrupleSupport X = P.product P := by
    rfl
  rw [hsupport]
  change (∑ q ∈ P.product P, F (g q.1) (g q.2)) = _
  calc
    (∑ q ∈ P.product P, F (g q.1) (g q.2)) =
        ∑ p ∈ P, ∑ q ∈ P, F (g p) (g q) := by
      exact Finset.sum_product P P
        (fun q : (ℕ × ℕ) × (ℕ × ℕ) => F (g q.1) (g q.2))
    _ = ∑ p ∈ P,
        ∑ s ∈ Finset.Icc 1 (X * X),
          (selbergShortRestrictedPairProductMultiplicity X s : ℝ) *
            F (g p) s := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact sum_completeRangePair_kernel_eq_productMultiplicity X (F (g p))
    _ = ∑ r ∈ Finset.Icc 1 (X * X),
        (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
          (∑ s ∈ Finset.Icc 1 (X * X),
            (selbergShortRestrictedPairProductMultiplicity X s : ℝ) *
              F r s) := by
      simpa only [P, g] using
        (sum_completeRangePair_kernel_eq_productMultiplicity X
          (fun r => ∑ s ∈ Finset.Icc 1 (X * X),
            (selbergShortRestrictedPairProductMultiplicity X s : ℝ) *
              F r s))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _hs
      ring

/-- Squaring the restricted pair count is exactly the cardinality of the
corresponding lcm-divisibility quadruple fiber. -/
theorem card_selbergShortCompleteRangePairs_sq_eq_card_quadruples
    (X k : ℕ) :
    (selbergShortCompleteRangePairs X k).card ^ 2 =
      (selbergShortCompleteRangeQuadruples X k).card := by
  calc
    (selbergShortCompleteRangePairs X k).card ^ 2 =
        ((selbergShortCompleteRangePairs X k).product
          (selbergShortCompleteRangePairs X k)).card := by
      simp [pow_two]
    _ = (selbergShortCompleteRangeQuadruples X k).card :=
      congrArg Finset.card
        (selbergShortCompleteRangePairs_product_eq_quadruples X k)

/-- The complete harmonic square moment of the restricted pair count is an
exact finite lcm-harmonic quadruple sum. -/
theorem sum_card_sq_selbergShortCompleteRangePairs_mul_inv_eq_lcmHarmonic
    (X U : ℕ) :
    (∑ k ∈ Finset.Icc 1 U,
        ((selbergShortCompleteRangePairs X k).card : ℝ) ^ 2 *
          (k : ℝ)⁻¹) =
      ∑ q ∈ selbergShortCompleteRangeQuadrupleSupport X,
        (selbergShortCompleteRangeLcm q : ℝ)⁻¹ *
          (harmonic (U / selbergShortCompleteRangeLcm q) : ℝ) := by
  classical
  let K := Finset.Icc 1 U
  let Q := selbergShortCompleteRangeQuadrupleSupport X
  let m := selbergShortCompleteRangeLcm
  have hcard : ∀ k,
      ((selbergShortCompleteRangePairs X k).card : ℝ) ^ 2 =
        ∑ q ∈ Q.filter (fun q => m q ∣ k), (1 : ℝ) := by
    intro k
    have hnat :=
      card_selbergShortCompleteRangePairs_sq_eq_card_quadruples X k
    have hquad :
        selbergShortCompleteRangeQuadruples X k =
          Q.filter (fun q => m q ∣ k) := by
      rfl
    rw [hquad] at hnat
    calc
      ((selbergShortCompleteRangePairs X k).card : ℝ) ^ 2 =
          ((Q.filter (fun q => m q ∣ k)).card : ℝ) := by
        exact_mod_cast hnat
      _ = ∑ q ∈ Q.filter (fun q => m q ∣ k), (1 : ℝ) := by simp
  change (∑ k ∈ K,
      ((selbergShortCompleteRangePairs X k).card : ℝ) ^ 2 *
        (k : ℝ)⁻¹) = _
  calc
    (∑ k ∈ K,
        ((selbergShortCompleteRangePairs X k).card : ℝ) ^ 2 *
          (k : ℝ)⁻¹) =
        ∑ k ∈ K, (∑ q ∈ Q.filter (fun q => m q ∣ k), (1 : ℝ)) *
          (k : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [hcard]
    _ = ∑ k ∈ K, ∑ q ∈ Q.filter (fun q => m q ∣ k),
          (k : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_mul]
      simp
    _ = ∑ k ∈ K, ∑ q ∈ Q,
          if m q ∣ k then (k : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_filter]
    _ = ∑ q ∈ Q, ∑ k ∈ K,
          if m q ∣ k then (k : ℝ)⁻¹ else 0 :=
      Finset.sum_comm
    _ = ∑ q ∈ Q,
          selbergShortLcmHarmonicKernel 1 U (m q) := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [← Finset.sum_filter]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      rcases Finset.mem_product.mp hq with ⟨hqLeft, hqRight⟩
      rcases Finset.mem_product.mp hqLeft with ⟨hq11, hq12⟩
      rcases Finset.mem_product.mp hqRight with ⟨hq21, hq22⟩
      have hmPos : 0 < m q :=
        Nat.lcm_pos
          (Nat.mul_pos (Finset.mem_Icc.mp hq11).1
            (Finset.mem_Icc.mp hq12).1)
          (Nat.mul_pos (Finset.mem_Icc.mp hq21).1
            (Finset.mem_Icc.mp hq22).1)
      rw [selbergShortLcmHarmonicKernel_one_eq_inv_mul_harmonic hmPos]

/-- After collecting both pair products, the complete harmonic moment is an
exact two-index lcm form in the restricted divisor multiplicities. -/
theorem sum_card_sq_selbergShortCompleteRangePairs_mul_inv_eq_doubleLcmHarmonic
    (X U : ℕ) :
    (∑ k ∈ Finset.Icc 1 U,
        ((selbergShortCompleteRangePairs X k).card : ℝ) ^ 2 *
          (k : ℝ)⁻¹) =
      ∑ r ∈ Finset.Icc 1 (X * X),
        ∑ s ∈ Finset.Icc 1 (X * X),
          (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
            (selbergShortRestrictedPairProductMultiplicity X s : ℝ) *
              ((Nat.lcm r s : ℝ)⁻¹ *
                (harmonic (U / Nat.lcm r s) : ℝ)) := by
  rw [sum_card_sq_selbergShortCompleteRangePairs_mul_inv_eq_lcmHarmonic]
  simpa only [selbergShortCompleteRangeLcm,
    selbergShortCompleteRangePairProduct] using
      (sum_completeRangeQuadruple_kernel_eq_doubleProductMultiplicity X
        (fun r s => (Nat.lcm r s : ℝ)⁻¹ *
          (harmonic (U / Nat.lcm r s) : ℝ)))

/-- Harmonic numbers are monotone after coercion to the reals. -/
theorem harmonic_natCast_mono {m n : ℕ} (hmn : m ≤ n) :
    (harmonic m : ℝ) ≤ (harmonic n : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc le_rfl hmn
  · intro k _hk _hkNot
    positivity

/-- The exact lcm-harmonic moment is bounded by one harmonic factor times a
totient-weighted square sum.  This is a finite identity-driven reduction,
not an asymptotic estimate for that square sum. -/
theorem sum_card_sq_selbergShortCompleteRangePairs_mul_inv_le_totientSquares
    (X U : ℕ) :
    (∑ k ∈ Finset.Icc 1 U,
        ((selbergShortCompleteRangePairs X k).card : ℝ) ^ 2 *
          (k : ℝ)⁻¹) ≤
      (harmonic U : ℝ) *
        ∑ d ∈ Finset.Icc 1 (X * X), (Nat.totient d : ℝ) *
          (∑ r ∈ (Finset.Icc 1 (X * X)).filter (fun r => d ∣ r),
            (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
              (r : ℝ)⁻¹) ^ 2 := by
  rw [sum_card_sq_selbergShortCompleteRangePairs_mul_inv_eq_doubleLcmHarmonic]
  calc
    (∑ r ∈ Finset.Icc 1 (X * X),
        ∑ s ∈ Finset.Icc 1 (X * X),
          (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
            (selbergShortRestrictedPairProductMultiplicity X s : ℝ) *
              ((Nat.lcm r s : ℝ)⁻¹ *
                (harmonic (U / Nat.lcm r s) : ℝ))) ≤
        (harmonic U : ℝ) *
          (∑ r ∈ Finset.Icc 1 (X * X),
            ∑ s ∈ Finset.Icc 1 (X * X),
              (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
                (selbergShortRestrictedPairProductMultiplicity X s : ℝ) *
                  (Nat.lcm r s : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s hs
      have hrPos : 0 < r := (Finset.mem_Icc.mp hr).1
      have hsPos : 0 < s := (Finset.mem_Icc.mp hs).1
      have hlcmPos : 0 < Nat.lcm r s := Nat.lcm_pos hrPos hsPos
      have hharm :
          (harmonic (U / Nat.lcm r s) : ℝ) ≤ (harmonic U : ℝ) :=
        harmonic_natCast_mono (Nat.div_le_self U (Nat.lcm r s))
      have hcoeff :
          0 ≤
            (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
              (selbergShortRestrictedPairProductMultiplicity X s : ℝ) *
                (Nat.lcm r s : ℝ)⁻¹ := by positivity
      calc
        (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
              (selbergShortRestrictedPairProductMultiplicity X s : ℝ) *
                ((Nat.lcm r s : ℝ)⁻¹ *
                  (harmonic (U / Nat.lcm r s) : ℝ)) =
            ((selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
              (selbergShortRestrictedPairProductMultiplicity X s : ℝ) *
                (Nat.lcm r s : ℝ)⁻¹) *
                  (harmonic (U / Nat.lcm r s) : ℝ) := by ring
        _ ≤ ((selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
              (selbergShortRestrictedPairProductMultiplicity X s : ℝ) *
                (Nat.lcm r s : ℝ)⁻¹) * (harmonic U : ℝ) :=
          mul_le_mul_of_nonneg_left hharm hcoeff
        _ = (harmonic U : ℝ) *
            ((selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
              (selbergShortRestrictedPairProductMultiplicity X s : ℝ) *
                (Nat.lcm r s : ℝ)⁻¹) := by ring
    _ = _ := by
      rw [MathlibAux.sum_reciprocal_lcm_quadratic_eq_totient_squares
        (fun r =>
          (selbergShortRestrictedPairProductMultiplicity X r : ℝ))
        (X * X)]

/-- The actual minimum-envelope high-range square-cardinality sum is bounded
by `H^2` times the complete harmonic moment. -/
theorem weighted_highRange_selbergShortCompleteRangePairs_le_completeMoment
    {L U : ℕ} (hL : 1 ≤ L) (X : ℕ) (H : ℝ) :
    (∑ k ∈ Finset.Ioc L U,
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergShortCompleteRangePairs X k).card ^ 2 /
            (k : ℝ))) ≤
      H ^ 2 *
        ∑ q ∈ selbergShortCompleteRangeQuadrupleSupport X,
          (selbergShortCompleteRangeLcm q : ℝ)⁻¹ *
            (harmonic (U / selbergShortCompleteRangeLcm q) : ℝ) := by
  calc
    (∑ k ∈ Finset.Ioc L U,
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergShortCompleteRangePairs X k).card ^ 2 /
            (k : ℝ))) ≤
        ∑ k ∈ Finset.Ioc L U,
          H ^ 2 *
            (((selbergShortCompleteRangePairs X k).card : ℝ) ^ 2 *
              (k : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk1 : 1 < k := hL.trans_lt (Finset.mem_Ioc.mp hk).1
      have hlog : 0 < Real.log (k : ℝ) :=
        Real.log_pos (by exact_mod_cast hk1)
      have hminNonneg :
          0 ≤ min |H| (2 / Real.log (k : ℝ)) :=
        le_min (abs_nonneg H) (by positivity)
      have hminSq :
          (min |H| (2 / Real.log (k : ℝ))) ^ 2 ≤ H ^ 2 := by
        have := (sq_le_sq₀ hminNonneg (abs_nonneg H)).2
          (min_le_left |H| (2 / Real.log (k : ℝ)))
        simpa [sq_abs] using this
      have hmassNonneg :
          0 ≤ (((selbergShortCompleteRangePairs X k).card : ℝ) ^ 2 *
            (k : ℝ)⁻¹) := by positivity
      simpa [div_eq_mul_inv, Nat.cast_pow, mul_assoc] using
        mul_le_mul_of_nonneg_right hminSq hmassNonneg
    _ ≤ ∑ k ∈ Finset.Icc 1 U,
          H ^ 2 *
            (((selbergShortCompleteRangePairs X k).card : ℝ) ^ 2 *
              (k : ℝ)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact Finset.mem_Icc.mpr
          ⟨hL.trans (Nat.le_of_lt (Finset.mem_Ioc.mp hk).1),
            (Finset.mem_Ioc.mp hk).2⟩
      · intro k _hk _hkNot
        positivity
    _ = H ^ 2 *
        (∑ k ∈ Finset.Icc 1 U,
          ((selbergShortCompleteRangePairs X k).card : ℝ) ^ 2 *
            (k : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [sum_card_sq_selbergShortCompleteRangePairs_mul_inv_eq_lcmHarmonic]

/-- Combining the high-range envelope with the lcm/totient decomposition
reduces the unsigned square-cardinality budget to one explicit finite
totient-weighted square sum. -/
theorem weighted_highRange_selbergShortCompleteRangePairs_le_totientSquares
    {L U : ℕ} (hL : 1 ≤ L) (X : ℕ) (H : ℝ) :
    (∑ k ∈ Finset.Ioc L U,
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergShortCompleteRangePairs X k).card ^ 2 /
            (k : ℝ))) ≤
      H ^ 2 * (harmonic U : ℝ) *
        ∑ d ∈ Finset.Icc 1 (X * X), (Nat.totient d : ℝ) *
          (∑ r ∈ (Finset.Icc 1 (X * X)).filter (fun r => d ∣ r),
            (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
              (r : ℝ)⁻¹) ^ 2 := by
  calc
    (∑ k ∈ Finset.Ioc L U,
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergShortCompleteRangePairs X k).card ^ 2 /
            (k : ℝ))) ≤
        H ^ 2 *
          ∑ q ∈ selbergShortCompleteRangeQuadrupleSupport X,
            (selbergShortCompleteRangeLcm q : ℝ)⁻¹ *
              (harmonic (U / selbergShortCompleteRangeLcm q) : ℝ) :=
      weighted_highRange_selbergShortCompleteRangePairs_le_completeMoment
        hL X H
    _ = H ^ 2 *
        (∑ k ∈ Finset.Icc 1 U,
          ((selbergShortCompleteRangePairs X k).card : ℝ) ^ 2 *
            (k : ℝ)⁻¹) := by
      rw [sum_card_sq_selbergShortCompleteRangePairs_mul_inv_eq_lcmHarmonic]
    _ ≤ H ^ 2 *
        ((harmonic U : ℝ) *
          ∑ d ∈ Finset.Icc 1 (X * X), (Nat.totient d : ℝ) *
            (∑ r ∈ (Finset.Icc 1 (X * X)).filter (fun r => d ∣ r),
              (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
                (r : ℝ)⁻¹) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (sum_card_sq_selbergShortCompleteRangePairs_mul_inv_le_totientSquares
          X U)
        (sq_nonneg H)
    _ = _ := by ring

/-- Replacing the harmonic factor by its elementary logarithmic upper bound
makes the remaining finite arithmetic square sum completely explicit. -/
theorem weighted_highRange_selbergShortCompleteRangePairs_le_log_mul_totientSquares
    {L U : ℕ} (hL : 1 ≤ L) (X : ℕ) (H : ℝ) :
    (∑ k ∈ Finset.Ioc L U,
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergShortCompleteRangePairs X k).card ^ 2 /
            (k : ℝ))) ≤
      H ^ 2 * (1 + Real.log U) *
        ∑ d ∈ Finset.Icc 1 (X * X), (Nat.totient d : ℝ) *
          (∑ r ∈ (Finset.Icc 1 (X * X)).filter (fun r => d ∣ r),
            (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
              (r : ℝ)⁻¹) ^ 2 := by
  let Q : ℝ :=
    ∑ d ∈ Finset.Icc 1 (X * X), (Nat.totient d : ℝ) *
      (∑ r ∈ (Finset.Icc 1 (X * X)).filter (fun r => d ∣ r),
        (selbergShortRestrictedPairProductMultiplicity X r : ℝ) *
          (r : ℝ)⁻¹) ^ 2
  have hQ : 0 ≤ Q := by
    unfold Q
    positivity
  calc
    (∑ k ∈ Finset.Ioc L U,
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergShortCompleteRangePairs X k).card ^ 2 /
            (k : ℝ))) ≤
        H ^ 2 * (harmonic U : ℝ) * Q := by
      exact
        weighted_highRange_selbergShortCompleteRangePairs_le_totientSquares
          hL X H
    _ ≤ H ^ 2 * (1 + Real.log U) * Q := by
      gcongr
      exact harmonic_le_one_add_log U

end HardyTheorem
