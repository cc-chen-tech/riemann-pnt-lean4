import HardyTheorem.SelbergSqrtZetaShortCollected
import HardyTheorem.SelbergSqrtZetaCoeffBound
import MathlibAux.FiberwiseNormSq
import MathlibAux.SlidingExponentialCoefficientBound

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# High-range energy of the square-root-zeta short coefficients

The unresolved collected coefficient at product `k` is kept as its actual
finite triple fiber.  Finite Cauchy--Schwarz and the oscillatory interval
transform reduce the high range to a logarithmically weighted arithmetic
fiber energy.
-/

/-- The finite square mass retained inside the actual triple-product fiber
at `k`. -/
noncomputable def selbergSqrtZetaShortCollectedTripleFiberEnergy
    (N X k : ℕ) : ℝ :=
  (selbergShortDirichletTriples N X k).card *
    ∑ p ∈ selbergShortDirichletTriples N X k,
      Complex.normSq (selbergSqrtZetaShortDirichletTripleCoeff X p)

/-- Projection to the two mollifier indices embeds each triple-product fiber
into the complete restricted divisor-pair set. -/
theorem card_selbergShortDirichletTriples_le_completeRangePairs
    (N X k : ℕ) :
    (selbergShortDirichletTriples N X k).card ≤
      (selbergShortCompleteRangePairs X k).card := by
  classical
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpSupport, hprod⟩
    rcases Finset.mem_product.mp hpSupport with ⟨_hpm, hpdl⟩
    exact Finset.mem_filter.mpr
      ⟨hpdl, ⟨p.1, by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          hprod.symm⟩⟩
  · intro p hp q hq hsnd
    apply Prod.ext
    · rcases Finset.mem_filter.mp hp with ⟨hpSupport, hpProd⟩
      rcases Finset.mem_filter.mp hq with ⟨_hqSupport, hqProd⟩
      rcases Finset.mem_product.mp hpSupport with ⟨_hpm, hpdl⟩
      rcases Finset.mem_product.mp hpdl with ⟨hpd, hpl⟩
      have hdlpos : 0 < p.2.1 * p.2.2 :=
        Nat.mul_pos (Finset.mem_Icc.mp hpd).1
          (Finset.mem_Icc.mp hpl).1
      have hmul :
          p.1 * (p.2.1 * p.2.2) =
            q.1 * (p.2.1 * p.2.2) := by
        calc
          p.1 * (p.2.1 * p.2.2) = k := by
            simpa [Nat.mul_assoc] using hpProd
          _ = q.1 * (q.2.1 * q.2.2) := by
            simpa [Nat.mul_assoc] using hqProd.symm
          _ = q.1 * (p.2.1 * p.2.2) := by rw [hsnd]
      exact Nat.eq_of_mul_eq_mul_right hdlpos hmul
    · exact hsnd

/-- Fiberwise finite Cauchy--Schwarz for one collected square-root-zeta
coefficient. -/
theorem normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_tripleFiber
    (N X k : ℕ) :
    Complex.normSq
        (selbergSqrtZetaShortDirichletCollectedCoeff N X k) ≤
      selbergSqrtZetaShortCollectedTripleFiberEnergy N X k := by
  unfold selbergSqrtZetaShortDirichletCollectedCoeff
  unfold selbergSqrtZetaShortCollectedTripleFiberEnergy
  exact MathlibAux.normSq_finset_sum_le_card_mul_sum_normSq
    (selbergShortDirichletTriples N X k)
    (selbergSqrtZetaShortDirichletTripleCoeff X)

/-- Every summand in a nonempty product fiber has square norm at most `1/k`.
This uses only the coefficient bound `|b_X(n)| ≤ 1`. -/
theorem normSq_selbergSqrtZetaShortDirichletTripleCoeff_le_inv
    {N X k : ℕ} (hX : 2 ≤ X)
    {p : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergShortDirichletTriples N X k) :
    Complex.normSq (selbergSqrtZetaShortDirichletTripleCoeff X p) ≤
      (k : ℝ)⁻¹ := by
  rcases Finset.mem_filter.mp hp with ⟨hpSupport, hprod⟩
  rcases Finset.mem_product.mp hpSupport with ⟨hpm, hpdl⟩
  rcases Finset.mem_product.mp hpdl with ⟨hpd, hpl⟩
  have hpm1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hpm).1
  have hpd1 : 1 ≤ p.2.1 := (Finset.mem_Icc.mp hpd).1
  have hpl1 : 1 ≤ p.2.2 := (Finset.mem_Icc.mp hpl).1
  have hpdX : p.2.1 ≤ X := (Finset.mem_Icc.mp hpd).2
  have hplX : p.2.2 ≤ X := (Finset.mem_Icc.mp hpl).2
  have hkpos : 0 < k := by
    rw [← hprod]
    positivity
  have hd :=
    abs_selbergSqrtZetaTaperedCoeff_le_one hX hpd1 hpdX
  have hl :=
    abs_selbergSqrtZetaTaperedCoeff_le_one hX hpl1 hplX
  have hsqrt : 0 < Real.sqrt (k : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hkpos)
  have hnorm :
      ‖selbergSqrtZetaShortDirichletTripleCoeff X p‖ ≤
        (Real.sqrt (k : ℝ))⁻¹ := by
    unfold selbergSqrtZetaShortDirichletTripleCoeff
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      norm_inv, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hprod]
    calc
      |selbergSqrtZetaTaperedCoeff X p.2.1| *
            |selbergSqrtZetaTaperedCoeff X p.2.2| *
          (Real.sqrt (k : ℝ))⁻¹ ≤
        1 * 1 * (Real.sqrt (k : ℝ))⁻¹ := by
          gcongr
      _ = (Real.sqrt (k : ℝ))⁻¹ := by ring
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖selbergSqrtZetaShortDirichletTripleCoeff X p‖ ^ 2 ≤
        ((Real.sqrt (k : ℝ))⁻¹) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
    _ = (k : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (by positivity)]

/-- The retained triple-fiber energy is at most the square of the actual
fiber cardinality divided by its product index. -/
theorem selbergSqrtZetaShortCollectedTripleFiberEnergy_le_card_sq_div
    {N X k : ℕ} (hX : 2 ≤ X) :
    selbergSqrtZetaShortCollectedTripleFiberEnergy N X k ≤
      (selbergShortDirichletTriples N X k).card ^ 2 / (k : ℝ) := by
  let S := selbergShortDirichletTriples N X k
  have hsum :
      (∑ p ∈ S,
          Complex.normSq
            (selbergSqrtZetaShortDirichletTripleCoeff X p)) ≤
        S.card * (k : ℝ)⁻¹ := by
    calc
      (∑ p ∈ S,
          Complex.normSq
            (selbergSqrtZetaShortDirichletTripleCoeff X p)) ≤
          ∑ _p ∈ S, (k : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        exact normSq_selbergSqrtZetaShortDirichletTripleCoeff_le_inv
          hX (by simpa only [S] using hp)
      _ = S.card * (k : ℝ)⁻¹ := by simp
  unfold selbergSqrtZetaShortCollectedTripleFiberEnergy
  change (S.card : ℝ) *
      (∑ p ∈ S,
        Complex.normSq
          (selbergSqrtZetaShortDirichletTripleCoeff X p)) ≤ _
  calc
    (S.card : ℝ) *
        (∑ p ∈ S,
          Complex.normSq
            (selbergSqrtZetaShortDirichletTripleCoeff X p)) ≤
        S.card * (S.card * (k : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = S.card ^ 2 / (k : ℝ) := by
      simp only [S]
      ring

/-- Replacing the triple fiber by its injective divisor-pair projection gives
the standard restricted divisor-pair majorant. -/
theorem selbergSqrtZetaShortCollectedTripleFiberEnergy_le_completePair_card_sq_div
    {N X k : ℕ} (hX : 2 ≤ X) :
    selbergSqrtZetaShortCollectedTripleFiberEnergy N X k ≤
      (selbergShortCompleteRangePairs X k).card ^ 2 / (k : ℝ) := by
  apply
    (selbergSqrtZetaShortCollectedTripleFiberEnergy_le_card_sq_div
      (N := N) hX).trans
  have hcard :=
    card_selbergShortDirichletTriples_le_completeRangePairs N X k
  have hsquare :
      (selbergShortDirichletTriples N X k).card ^ 2 ≤
        (selbergShortCompleteRangePairs X k).card ^ 2 :=
    Nat.pow_le_pow_left hcard 2
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast hsquare) (Nat.cast_nonneg k)

/-- The strongest pointwise interval-transform envelope for a nonconstant
collected mode. -/
theorem normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_tripleFiber_mul_min_sq
    {N X k : ℕ} (hk : 1 < k) (H : ℝ) :
    Complex.normSq
        (MathlibAux.slidingExponentialCoefficient H
          (selbergSqrtZetaShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency k) ≤
      (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
        selbergSqrtZetaShortCollectedTripleFiberEnergy N X k := by
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
  have hcoeff :=
    normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_tripleFiber
      N X k
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
    _ ≤ (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
        selbergSqrtZetaShortCollectedTripleFiberEnergy N X k :=
      mul_le_mul_of_nonneg_left hcoeff (sq_nonneg _)

/-- The transformed high-range energy is bounded by the corresponding
minimum-envelope triple-fiber sum. -/
theorem sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_highRange_le_tripleFiberMin
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          selbergSqrtZetaShortCollectedTripleFiberEnergy N X k := by
  apply Finset.sum_le_sum
  intro k hk
  have honeMin : 1 ≤ min N X :=
    Nat.le_min.mpr ⟨hN, by omega⟩
  exact
    normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_tripleFiber_mul_min_sq
      (honeMin.trans_lt (Finset.mem_Ioc.mp hk).1) H

/-- After the elementary coefficient bound, the unresolved high range is a
purely arithmetic weighted square-fiber-cardinality sum. -/
theorem sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_highRange_le_cardSq
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergShortDirichletTriples N X k).card ^ 2 /
            (k : ℝ)) := by
  calc
    (∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          selbergSqrtZetaShortCollectedTripleFiberEnergy N X k :=
      sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_highRange_le_tripleFiberMin
        hN hX H
    _ ≤ ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergShortDirichletTriples N X k).card ^ 2 /
            (k : ℝ)) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact mul_le_mul_of_nonneg_left
        (selbergSqrtZetaShortCollectedTripleFiberEnergy_le_card_sq_div hX)
        (sq_nonneg _)

/-- The high range in the conventional restricted-divisor-pair form. -/
theorem sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_highRange_le_completePairCardSq
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergShortCompleteRangePairs X k).card ^ 2 /
            (k : ℝ)) := by
  calc
    (∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          selbergSqrtZetaShortCollectedTripleFiberEnergy N X k :=
      sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_highRange_le_tripleFiberMin
        hN hX H
    _ ≤ ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
        (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
          ((selbergShortCompleteRangePairs X k).card ^ 2 /
            (k : ℝ)) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact mul_le_mul_of_nonneg_left
        (selbergSqrtZetaShortCollectedTripleFiberEnergy_le_completePair_card_sq_div
          hX)
        (sq_nonneg _)

/-- The full transformed energy is the proved constant low range plus one
explicit minimum-envelope triple-fiber high-range sum. -/
theorem sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_tripleFiberMinHighRange
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (15 : ℝ) / 4 * H ^ 2 +
        ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
          (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
            selbergSqrtZetaShortCollectedTripleFiberEnergy N X k := by
  exact
    (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_highRange
      hN (by omega) hlarge H).trans
      (add_le_add (le_refl _)
        (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_highRange_le_tripleFiberMin
          hN hX H))

/-- The complete energy bound with only a weighted square-cardinality
arithmetic sum left unresolved. -/
theorem sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_cardSqHighRange
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (15 : ℝ) / 4 * H ^ 2 +
        ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
          (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
            ((selbergShortDirichletTriples N X k).card ^ 2 /
              (k : ℝ)) := by
  exact
    (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_highRange
      hN (by omega) hlarge H).trans
      (add_le_add (le_refl _)
        (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_highRange_le_cardSq
          hN hX H))

/-- The complete energy bound with a restricted divisor-pair square moment
as its only high-range input. -/
theorem sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_completePairCardSqHighRange
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaShortDirichletCollectedCoeff N X)
            selbergShortDirichletCollectedFrequency k)) ≤
      (15 : ℝ) / 4 * H ^ 2 +
        ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
          (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
            ((selbergShortCompleteRangePairs X k).card ^ 2 /
              (k : ℝ)) := by
  exact
    (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_highRange
      hN (by omega) hlarge H).trans
      (add_le_add (le_refl _)
        (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_highRange_le_completePairCardSq
          hN hX H))

end HardyTheorem
