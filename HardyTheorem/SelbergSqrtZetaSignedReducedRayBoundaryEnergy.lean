import HardyTheorem.SelbergSqrtZetaCoeffBound
import HardyTheorem.SelbergSqrtZetaSignedBoundaryScale
import HardyTheorem.SelbergSqrtZetaSignedReducedRayCompleteBoundary

/-!
# Weighted energy of one reduced Selberg boundary ray

The boundary defect is a harmonic scale sum.  Applying Cauchy--Schwarz with
weight `1 / d` retains that arithmetic weight and introduces no support
cardinality.  The numerator taper is then bounded by one, while the collected
denominator coefficient remains inside a square for later arithmetic
estimates.
-/

open scoped BigOperators

namespace HardyTheorem

private theorem harmonic_cast_nonneg (X : ℕ) :
    0 ≤ (harmonic X : ℝ) := by
  rw [show (harmonic X : ℝ) =
      ∑ r ∈ Finset.Icc 1 X, (r : ℝ)⁻¹ by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]]
  apply Finset.sum_nonneg
  intro r _hr
  positivity

private theorem sq_sum_inv_mul_le_sum_inv_mul_sum_inv_mul_sq
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℝ) (f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i) ^ 2 ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * (f i) ^ 2 := by
  have hrewrite :
      (∑ i ∈ s, w i * f i) =
        ∑ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i) * f i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  rw [hrewrite]
  calc
    (∑ i ∈ s, Real.sqrt (w i) *
        (Real.sqrt (w i) * f i)) ^ 2 ≤
        (∑ i ∈ s, (Real.sqrt (w i)) ^ 2) *
          ∑ i ∈ s, (Real.sqrt (w i) * f i) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s
        (fun i => Real.sqrt (w i))
        (fun i => Real.sqrt (w i) * f i)
    _ = (∑ i ∈ s, w i) * ∑ i ∈ s, w i * (f i) ^ 2 := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        exact Real.sq_sqrt (hw i hi)
      · apply Finset.sum_congr rfl
        intro i hi
        rw [mul_pow, Real.sq_sqrt (hw i hi)]

private theorem sq_sum_le_sum_inv_mul_sum_mul_sq
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (r : ι → ℕ) (f : ι → ℝ)
    (hr : ∀ i ∈ s, 0 < r i) :
    (∑ i ∈ s, f i) ^ 2 ≤
      (∑ i ∈ s, ((r i : ℕ) : ℝ)⁻¹) *
        ∑ i ∈ s, ((r i : ℕ) : ℝ) * (f i) ^ 2 := by
  calc
    (∑ i ∈ s, f i) ^ 2 =
        (∑ i ∈ s, ((r i : ℕ) : ℝ)⁻¹ *
          (((r i : ℕ) : ℝ) * f i)) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [Nat.cast_ne_zero.mpr (hr i hi).ne']
    _ ≤ (∑ i ∈ s, ((r i : ℕ) : ℝ)⁻¹) *
          ∑ i ∈ s, ((r i : ℕ) : ℝ)⁻¹ *
            ((((r i : ℕ) : ℝ) * f i) ^ 2) :=
      sq_sum_inv_mul_le_sum_inv_mul_sum_inv_mul_sq
        s (fun i => ((r i : ℕ) : ℝ)⁻¹)
        (fun i => ((r i : ℕ) : ℝ) * f i)
        (by
          intro i _hi
          positivity)
    _ = (∑ i ∈ s, ((r i : ℕ) : ℝ)⁻¹) *
          ∑ i ∈ s, ((r i : ℕ) : ℝ) * (f i) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [Nat.cast_ne_zero.mpr (hr i hi).ne']

/-- Reciprocal mass of the second coordinates in one denominator fiber.
Projection to the second coordinate is injective on a fixed product fiber,
so this is bounded by the `X`-th harmonic number without a fiber-cardinality
factor. -/
theorem
    sum_inv_snd_selbergSqrtZetaSignedDenominatorFiber_le_harmonic
    (N X k : ℕ) :
    (∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k,
        (p.2 : ℝ)⁻¹) ≤
      (harmonic X : ℝ) := by
  classical
  let S := selbergSqrtZetaSignedDenominatorFiber N X k
  have hinj :
      ∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p = q := by
    rintro ⟨m, r⟩ hp ⟨m', r'⟩ hq hrr
    simp only at hrr
    subst r'
    have hmr : m * r = k := (Finset.mem_filter.mp hp).2
    have hm'r : m' * r = k := (Finset.mem_filter.mp hq).2
    have hrRange :=
      (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
    have hrPos : 0 < r := (Finset.mem_Icc.mp hrRange).1
    have hmm' : m = m' :=
      Nat.mul_right_cancel hrPos (hmr.trans hm'r.symm)
    subst m'
    rfl
  have himage :
      S.image Prod.snd ⊆ Finset.Icc 1 X := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
    exact
      (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  calc
    (∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k,
        (p.2 : ℝ)⁻¹) =
        ∑ r ∈ S.image Prod.snd, (r : ℝ)⁻¹ := by
      simpa only [S] using
        (Finset.sum_image
          (f := fun r : ℕ => (r : ℝ)⁻¹)
          (g := Prod.snd) hinj).symm
    _ ≤ ∑ r ∈ Finset.Icc 1 X, (r : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro r _hr _hrNot
        positivity)
    _ = (harmonic X : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]

/-- Weighted Cauchy--Schwarz inside one denominator fiber.  The first factor
is harmonic and the second retains the tapered square energy with weight
equal to the denominator scale. -/
theorem
    sq_sum_selbergSqrtZetaSignedDenominatorFiber_taper_le_harmonic_mul_weightedEnergy
    (N X k : ℕ) :
    (∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k,
        selbergSqrtZetaTaperedCoeff X p.2) ^ 2 ≤
      (harmonic X : ℝ) *
        ∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k,
          (p.2 : ℝ) * (selbergSqrtZetaTaperedCoeff X p.2) ^ 2 := by
  let S := selbergSqrtZetaSignedDenominatorFiber N X k
  calc
    (∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k,
        selbergSqrtZetaTaperedCoeff X p.2) ^ 2 ≤
        (∑ p ∈ S, (p.2 : ℝ)⁻¹) *
          ∑ p ∈ S,
            (p.2 : ℝ) * (selbergSqrtZetaTaperedCoeff X p.2) ^ 2 := by
      apply sq_sum_le_sum_inv_mul_sum_mul_sq
      intro p hp
      have hpRange :=
        (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
      exact (Finset.mem_Icc.mp hpRange).1
    _ ≤ (harmonic X : ℝ) *
          ∑ p ∈ S,
            (p.2 : ℝ) * (selbergSqrtZetaTaperedCoeff X p.2) ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · simpa only [S] using
          sum_inv_snd_selbergSqrtZetaSignedDenominatorFiber_le_harmonic
            N X k
      · apply Finset.sum_nonneg
        intro p _hp
        positivity

/-- The weighted tapered square energy of one denominator fiber is bounded
by the corresponding global energy on `[1, X]`.  Projection to the second
coordinate is injective on a fixed product fiber, so this reindexing has no
fiber-cardinality loss. -/
theorem
    sum_weightedSq_selbergSqrtZetaSignedDenominatorFiber_le_globalTaperEnergy
    (N X k : ℕ) :
    (∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k,
        (p.2 : ℝ) * (selbergSqrtZetaTaperedCoeff X p.2) ^ 2) ≤
      ∑ r ∈ Finset.Icc 1 X,
        (r : ℝ) * (selbergSqrtZetaTaperedCoeff X r) ^ 2 := by
  classical
  let S := selbergSqrtZetaSignedDenominatorFiber N X k
  let f : ℕ → ℝ := fun r =>
    (r : ℝ) * (selbergSqrtZetaTaperedCoeff X r) ^ 2
  have hinj :
      ∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p = q := by
    rintro ⟨m, r⟩ hp ⟨m', r'⟩ hq hrr
    simp only at hrr
    subst r'
    have hmr : m * r = k := (Finset.mem_filter.mp hp).2
    have hm'r : m' * r = k := (Finset.mem_filter.mp hq).2
    have hrRange :=
      (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
    have hrPos : 0 < r := (Finset.mem_Icc.mp hrRange).1
    have hmm' : m = m' :=
      Nat.mul_right_cancel hrPos (hmr.trans hm'r.symm)
    subst m'
    rfl
  have himage :
      S.image Prod.snd ⊆ Finset.Icc 1 X := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
    exact
      (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  calc
    (∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k,
        (p.2 : ℝ) * (selbergSqrtZetaTaperedCoeff X p.2) ^ 2) =
        ∑ r ∈ S.image Prod.snd, f r := by
      simpa only [S, f] using
        (Finset.sum_image
          (f := f) (g := Prod.snd) hinj).symm
    _ ≤ ∑ r ∈ Finset.Icc 1 X, f r :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro r _hr _hrNot
        dsimp only [f]
        positivity)
    _ = _ := by rfl

/-- The arithmetic coefficient has absolute value at most one, so the
global tapered square energy is bounded by the explicit linear-taper energy.
This keeps the full taper weight instead of replacing it by a support count. -/
theorem
    sum_weightedSq_selbergSqrtZetaSignedDenominatorFiber_le_globalLinearTaperEnergy
    (N X k : ℕ) :
    (∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k,
        (p.2 : ℝ) * (selbergSqrtZetaTaperedCoeff X p.2) ^ 2) ≤
      ∑ r ∈ Finset.Icc 1 X,
        (r : ℝ) * (selbergMoebiusWeight X r) ^ 2 := by
  calc
    (∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k,
        (p.2 : ℝ) * (selbergSqrtZetaTaperedCoeff X p.2) ^ 2) ≤
        ∑ r ∈ Finset.Icc 1 X,
          (r : ℝ) * (selbergSqrtZetaTaperedCoeff X r) ^ 2 :=
      sum_weightedSq_selbergSqrtZetaSignedDenominatorFiber_le_globalTaperEnergy
        N X k
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r _hr
      have hcoeff := abs_selbergSqrtZetaCoeff_le_one r
      have hcoeff2 : (selbergSqrtZetaCoeff r) ^ 2 ≤ 1 := by
        simpa only [sq_abs, one_pow] using
          (sq_le_sq₀ (abs_nonneg (selbergSqrtZetaCoeff r)) zero_le_one).2
            hcoeff
      rw [selbergSqrtZetaTaperedCoeff, mul_pow]
      apply mul_le_mul_of_nonneg_left
      · simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hcoeff2
            (sq_nonneg (selbergMoebiusWeight X r))
      · positivity

/-- Uniform denominator-fiber signed-square bound.  Its right-hand side
depends only on `X`: one harmonic factor from weighted Cauchy--Schwarz and
one explicit weighted linear-taper energy. -/
theorem
    sq_sum_selbergSqrtZetaSignedDenominatorFiber_taper_le_uniformLinearTaperEnergy
    (N X k : ℕ) :
    (∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k,
        selbergSqrtZetaTaperedCoeff X p.2) ^ 2 ≤
      (harmonic X : ℝ) *
        ∑ r ∈ Finset.Icc 1 X,
          (r : ℝ) * (selbergMoebiusWeight X r) ^ 2 := by
  calc
    (∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k,
        selbergSqrtZetaTaperedCoeff X p.2) ^ 2 ≤
        (harmonic X : ℝ) *
          ∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k,
            (p.2 : ℝ) * (selbergSqrtZetaTaperedCoeff X p.2) ^ 2 :=
      sq_sum_selbergSqrtZetaSignedDenominatorFiber_taper_le_harmonic_mul_weightedEnergy
        N X k
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left
        (sum_weightedSq_selbergSqrtZetaSignedDenominatorFiber_le_globalLinearTaperEnergy
          N X k)
        (harmonic_cast_nonneg X)

/-- Weighted Cauchy--Schwarz for the exact boundary defect.  The factor
`sum (1 / d)` is the genuine harmonic mass of the boundary support, and the
second factor retains the full signed numerator and denominator arithmetic
inside its scale energy. -/
theorem
    selbergSqrtZetaSignedReducedRayBoundaryTerm_sq_le_harmonicEnergy
    (N X a b : ℕ) :
    (selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b) ^ 2 ≤
      (∑ d ∈
          selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
          (d : ℝ)⁻¹) *
        ∑ d ∈
            selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
          (d : ℝ)⁻¹ *
            (selbergSqrtZetaTaperedCoeff X (a * d) *
              ∑ p ∈
                  selbergSqrtZetaSignedDenominatorFiber N X (b * d),
                selbergSqrtZetaTaperedCoeff X p.2) ^ 2 := by
  unfold selbergSqrtZetaSignedReducedRayBoundaryTerm
  simpa only [mul_assoc] using
    sq_sum_inv_mul_le_sum_inv_mul_sum_inv_mul_sq
      (selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b)
      (fun d => (d : ℝ)⁻¹)
      (fun d =>
        selbergSqrtZetaTaperedCoeff X (a * d) *
          ∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X (b * d),
            selbergSqrtZetaTaperedCoeff X p.2)
      (by
        intro d _hd
        positivity)

/-- Removing the numerator taper costs no cardinality: on every boundary
scale it has absolute value at most one.  The denominator fiber is still a
signed square, ready for a later arithmetic estimate. -/
theorem
    selbergSqrtZetaSignedReducedRayBoundaryTerm_sq_le_harmonicMass_mul_denominatorEnergy
    {N X a b : ℕ} (hX : 2 ≤ X) :
    (selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b) ^ 2 ≤
      (∑ d ∈
          selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
          (d : ℝ)⁻¹) *
        ∑ d ∈
            selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
          (d : ℝ)⁻¹ *
            (∑ p ∈
                selbergSqrtZetaSignedDenominatorFiber N X (b * d),
              selbergSqrtZetaTaperedCoeff X p.2) ^ 2 := by
  calc
    (selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b) ^ 2 ≤
        (∑ d ∈
            selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
            (d : ℝ)⁻¹) *
          ∑ d ∈
              selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
            (d : ℝ)⁻¹ *
              (selbergSqrtZetaTaperedCoeff X (a * d) *
                ∑ p ∈
                    selbergSqrtZetaSignedDenominatorFiber N X (b * d),
                  selbergSqrtZetaTaperedCoeff X p.2) ^ 2 :=
      selbergSqrtZetaSignedReducedRayBoundaryTerm_sq_le_harmonicEnergy
        N X a b
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro d hd
        have hdFacts :=
          selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_facts hd
        have hdPos : 0 < d := hdFacts.1
        have haPos : 0 < a := hdFacts.2.1
        have hadOne : 1 ≤ a * d :=
          Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero haPos.ne' hdPos.ne')
        have hA :=
          abs_selbergSqrtZetaTaperedCoeff_le_one
            hX hadOne hdFacts.2.2.2.1
        have hA2 :
            (selbergSqrtZetaTaperedCoeff X (a * d)) ^ 2 ≤ 1 := by
          simpa only [sq_abs, one_pow] using
            (sq_le_sq₀
              (abs_nonneg (selbergSqrtZetaTaperedCoeff X (a * d)))
              zero_le_one).2 hA
        have hinner_nonneg :
            0 ≤
              (∑ p ∈
                  selbergSqrtZetaSignedDenominatorFiber N X (b * d),
                selbergSqrtZetaTaperedCoeff X p.2) ^ 2 :=
          sq_nonneg _
        apply mul_le_mul_of_nonneg_left
        calc
          (selbergSqrtZetaTaperedCoeff X (a * d) *
              ∑ p ∈
                  selbergSqrtZetaSignedDenominatorFiber N X (b * d),
                selbergSqrtZetaTaperedCoeff X p.2) ^ 2 =
              (selbergSqrtZetaTaperedCoeff X (a * d)) ^ 2 *
                (∑ p ∈
                    selbergSqrtZetaSignedDenominatorFiber N X (b * d),
                  selbergSqrtZetaTaperedCoeff X p.2) ^ 2 := by
            rw [mul_pow]
          _ ≤ 1 *
                (∑ p ∈
                    selbergSqrtZetaSignedDenominatorFiber N X (b * d),
                  selbergSqrtZetaTaperedCoeff X p.2) ^ 2 :=
            mul_le_mul_of_nonneg_right hA2 hinner_nonneg
          _ = _ := one_mul _
        · positivity
      · positivity

/-- Fully explicit pointwise boundary estimate.  The first factor is the
exact containing harmonic tail from `min N X / b` to the smaller of the two
ray cutoffs.  No `card * sum` estimate and no global `N * X^2` spacing bound
is used. -/
theorem
    selbergSqrtZetaSignedReducedRayBoundaryTerm_sq_le_harmonicTail_mul_denominatorEnergy
    {N X a b : ℕ} (hX : 2 ≤ X) :
    (selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b) ^ 2 ≤
      (∑ d ∈ Finset.Ioc
          (min N X / b)
          (min (X / a) (N * X / b)),
          (d : ℝ)⁻¹) *
        ∑ d ∈
            selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
          (d : ℝ)⁻¹ *
            (∑ p ∈
                selbergSqrtZetaSignedDenominatorFiber N X (b * d),
              selbergSqrtZetaTaperedCoeff X p.2) ^ 2 := by
  calc
    (selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b) ^ 2 ≤
        (∑ d ∈
            selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
            (d : ℝ)⁻¹) *
          ∑ d ∈
              selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
            (d : ℝ)⁻¹ *
              (∑ p ∈
                  selbergSqrtZetaSignedDenominatorFiber N X (b * d),
                selbergSqrtZetaTaperedCoeff X p.2) ^ 2 :=
      selbergSqrtZetaSignedReducedRayBoundaryTerm_sq_le_harmonicMass_mul_denominatorEnergy
        hX
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right
        (selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_sum_inv_le
          N X a b)
      apply Finset.sum_nonneg
      intro d _hd
      positivity

/-- The boundary defect is bounded uniformly by the square of its exact
containing harmonic tail, the harmonic factor from the denominator fiber,
and the explicit global linear-taper energy.  Both Cauchy--Schwarz steps keep
their natural reciprocal weights; no boundary or fiber cardinality occurs. -/
theorem
    selbergSqrtZetaSignedReducedRayBoundaryTerm_sq_le_harmonicTail_sq_mul_uniformLinearTaperEnergy
    {N X a b : ℕ} (hX : 2 ≤ X) :
    (selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b) ^ 2 ≤
      (∑ d ∈ Finset.Ioc
          (min N X / b)
          (min (X / a) (N * X / b)),
          (d : ℝ)⁻¹) ^ 2 *
        (harmonic X : ℝ) *
        ∑ r ∈ Finset.Icc 1 X,
          (r : ℝ) * (selbergMoebiusWeight X r) ^ 2 := by
  let tail : ℝ :=
    ∑ d ∈ Finset.Ioc
      (min N X / b)
      (min (X / a) (N * X / b)),
      (d : ℝ)⁻¹
  let energy : ℝ :=
    ∑ r ∈ Finset.Icc 1 X,
      (r : ℝ) * (selbergMoebiusWeight X r) ^ 2
  have htail_nonneg : 0 ≤ tail := by
    dsimp only [tail]
    apply Finset.sum_nonneg
    intro d _hd
    positivity
  have henergy_nonneg : 0 ≤ energy := by
    dsimp only [energy]
    apply Finset.sum_nonneg
    intro r _hr
    positivity
  have hconstant_nonneg :
      0 ≤ (harmonic X : ℝ) * energy :=
    mul_nonneg (harmonic_cast_nonneg X) henergy_nonneg
  have hdenominator :
      (∑ d ∈
          selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
          (d : ℝ)⁻¹ *
            (∑ p ∈
                selbergSqrtZetaSignedDenominatorFiber N X (b * d),
              selbergSqrtZetaTaperedCoeff X p.2) ^ 2) ≤
        tail * ((harmonic X : ℝ) * energy) := by
    calc
      (∑ d ∈
          selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
          (d : ℝ)⁻¹ *
            (∑ p ∈
                selbergSqrtZetaSignedDenominatorFiber N X (b * d),
              selbergSqrtZetaTaperedCoeff X p.2) ^ 2) ≤
          ∑ d ∈
            selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
            (d : ℝ)⁻¹ * ((harmonic X : ℝ) * energy) := by
        apply Finset.sum_le_sum
        intro d _hd
        apply mul_le_mul_of_nonneg_left
        · simpa only [energy] using
            sq_sum_selbergSqrtZetaSignedDenominatorFiber_taper_le_uniformLinearTaperEnergy
              N X (b * d)
        · positivity
      _ = (∑ d ∈
            selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
            (d : ℝ)⁻¹) * ((harmonic X : ℝ) * energy) := by
        rw [Finset.sum_mul]
      _ ≤ tail * ((harmonic X : ℝ) * energy) := by
        apply mul_le_mul_of_nonneg_right
        · simpa only [tail] using
            selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_sum_inv_le
              N X a b
        · exact hconstant_nonneg
  calc
    (selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b) ^ 2 ≤
        tail *
          ∑ d ∈
            selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
            (d : ℝ)⁻¹ *
              (∑ p ∈
                  selbergSqrtZetaSignedDenominatorFiber N X (b * d),
                selbergSqrtZetaTaperedCoeff X p.2) ^ 2 := by
      simpa only [tail] using
        selbergSqrtZetaSignedReducedRayBoundaryTerm_sq_le_harmonicTail_mul_denominatorEnergy
          hX
    _ ≤ tail * (tail * ((harmonic X : ℝ) * energy)) :=
      mul_le_mul_of_nonneg_left hdenominator htail_nonneg
    _ = tail ^ 2 * (harmonic X : ℝ) * energy := by ring
    _ = _ := by rfl

end HardyTheorem
