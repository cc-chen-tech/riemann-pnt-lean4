import MathlibAux.RectangleResidue

open Complex Set
open scoped BigOperators Interval

namespace MathlibAux

/-- Boundary-rectangle integrals agree when the integrands agree on all four
edges of an ordered axis-parallel rectangle. -/
lemma boundaryRectIntegral_congr_of_eqOn_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : ℂ → E} {x0 x1 y0 y1 : ℝ}
    (hfg : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ),
      ¬(x0 < z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) → f z = g z) :
    boundaryRectIntegral f x0 x1 y0 y1 =
      boundaryRectIntegral g x0 x1 y0 y1 := by
  have hbottom :
      (∫ x : ℝ in x0..x1, f (x + y0 * I)) =
        ∫ x : ℝ in x0..x1, g (x + y0 * I) := by
    apply intervalIntegral.integral_congr
    intro x hxmem
    apply hfg
    · simpa [mem_reProdIm] using
        And.intro hxmem (left_mem_uIcc : y0 ∈ [[y0, y1]])
    · simp
  have htop :
      (∫ x : ℝ in x0..x1, f (x + y1 * I)) =
        ∫ x : ℝ in x0..x1, g (x + y1 * I) := by
    apply intervalIntegral.integral_congr
    intro x hxmem
    apply hfg
    · simpa [mem_reProdIm] using
        And.intro hxmem (right_mem_uIcc : y1 ∈ [[y0, y1]])
    · simp
  have hright :
      (∫ y : ℝ in y0..y1, f ((x1 : ℂ) + y * I)) =
        ∫ y : ℝ in y0..y1, g ((x1 : ℂ) + y * I) := by
    apply intervalIntegral.integral_congr
    intro y hymem
    apply hfg
    · simpa [mem_reProdIm] using
        And.intro (right_mem_uIcc : x1 ∈ [[x0, x1]]) hymem
    · simp
  have hleft :
      (∫ y : ℝ in y0..y1, f ((x0 : ℂ) + y * I)) =
        ∫ y : ℝ in y0..y1, g ((x0 : ℂ) + y * I) := by
    apply intervalIntegral.integral_congr
    intro y hymem
    apply hfg
    · simpa [mem_reProdIm] using
        And.intro (left_mem_uIcc : x0 ∈ [[x0, x1]]) hymem
    · simp
  unfold boundaryRectIntegral
  rw [hbottom, htop, hright, hleft]

/-- The boundary integral of `1 / (z-p)` on an arbitrary axis-parallel
rectangle is `2πi` when `p` is strictly inside. -/
theorem boundaryRectIntegral_sub_inv_of_mem
    (p : ℂ) {x0 x1 y0 y1 : ℝ}
    (hx0p : x0 < p.re) (hpx1 : p.re < x1)
    (hy0p : y0 < p.im) (hpy1 : p.im < y1) :
    boundaryRectIntegral (fun z : ℂ => (z - p)⁻¹) x0 x1 y0 y1 =
      2 * Real.pi * I := by
  let margin := min (min (p.re - x0) (x1 - p.re))
    (min (p.im - y0) (y1 - p.im))
  have hmargin : 0 < margin := by
    dsimp [margin]
    exact lt_min (lt_min (sub_pos.mpr hx0p) (sub_pos.mpr hpx1))
      (lt_min (sub_pos.mpr hy0p) (sub_pos.mpr hpy1))
  let r := margin / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hr_x0 : r < p.re - x0 := by
    have hm : margin ≤ p.re - x0 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    dsimp [r]
    linarith
  have hr_x1 : r < x1 - p.re := by
    have hm : margin ≤ x1 - p.re :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    dsimp [r]
    linarith
  have hr_y0 : r < p.im - y0 := by
    have hm : margin ≤ p.im - y0 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    dsimp [r]
    linarith
  have hr_y1 : r < y1 - p.im := by
    have hm : margin ≤ y1 - p.im :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    dsimp [r]
    linarith
  let u := p.re - r
  let v := p.re + r
  let w := p.im - r
  let q := p.im + r
  have hx0u : x0 < u := by dsimp [u]; linarith
  have huv : u < v := by dsimp [u, v]; linarith
  have hvx1 : v < x1 := by dsimp [v]; linarith
  have hy0w : y0 < w := by dsimp [w]; linarith
  have hwq : w < q := by dsimp [w, q]; linarith
  have hqy1 : q < y1 := by dsimp [q]; linarith
  let kernel : ℂ → ℂ := fun z => (z - p)⁻¹
  have horizontal_continuous : ∀ y : ℝ, y ≠ p.im →
      Continuous (fun x : ℝ => kernel (x + y * I)) := by
    intro y hy
    apply ((Complex.continuous_ofReal.add
      (continuous_const.mul continuous_const)).sub continuous_const).inv₀
    intro x hx
    apply hy
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have vertical_continuous : ∀ x : ℝ, x ≠ p.re →
      Continuous (fun y : ℝ => kernel (x + y * I)) := by
    intro x hx
    apply ((continuous_const.add
      (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const).inv₀
    intro y hy
    apply hx
    have hr' := congrArg Complex.re hy
    simp at hr'
    linarith
  have hbottom : boundaryRectIntegral kernel x0 x1 y0 w = 0 := by
    apply boundaryRectIntegral_eq_zero_of_differentiableOn
    intro z hz
    apply ((differentiableAt_id.sub_const p).inv ?_).differentiableWithinAt
    intro hzp
    have hz_eq : z = p := sub_eq_zero.mp hzp
    subst z
    rw [mem_reProdIm] at hz
    have hzim := hz.2
    rw [uIcc_of_le hy0w.le] at hzim
    linarith [hzim.2]
  have htop : boundaryRectIntegral kernel x0 x1 q y1 = 0 := by
    apply boundaryRectIntegral_eq_zero_of_differentiableOn
    intro z hz
    apply ((differentiableAt_id.sub_const p).inv ?_).differentiableWithinAt
    intro hzp
    have hz_eq : z = p := sub_eq_zero.mp hzp
    subst z
    rw [mem_reProdIm] at hz
    have hzim := hz.2
    rw [uIcc_of_le hqy1.le] at hzim
    linarith [hzim.1]
  have hleft : boundaryRectIntegral kernel x0 u w q = 0 := by
    apply boundaryRectIntegral_eq_zero_of_differentiableOn
    intro z hz
    apply ((differentiableAt_id.sub_const p).inv ?_).differentiableWithinAt
    intro hzp
    have hz_eq : z = p := sub_eq_zero.mp hzp
    subst z
    rw [mem_reProdIm] at hz
    have hzre := hz.1
    rw [uIcc_of_le hx0u.le] at hzre
    linarith [hzre.2]
  have hright : boundaryRectIntegral kernel v x1 w q = 0 := by
    apply boundaryRectIntegral_eq_zero_of_differentiableOn
    intro z hz
    apply ((differentiableAt_id.sub_const p).inv ?_).differentiableWithinAt
    intro hzp
    have hz_eq : z = p := sub_eq_zero.mp hzp
    subst z
    rw [mem_reProdIm] at hz
    have hzre := hz.1
    rw [uIcc_of_le hvx1.le] at hzre
    linarith [hzre.1]
  have houter_inner :
      boundaryRectIntegral kernel x0 x1 y0 y1 =
        boundaryRectIntegral kernel u v w q :=
    boundaryRectIntegral_eq_inner_of_four_rectangles kernel
      x0 u v x1 y0 w q y1
      (horizontal_continuous w (by dsimp [w]; linarith))
      (horizontal_continuous q (by dsimp [q]; linarith))
      (vertical_continuous x0 (by linarith))
      (vertical_continuous x1 (by linarith))
      hbottom htop hleft hright
  have hinner : boundaryRectIntegral kernel u v w q =
      rectangleBoundaryIntegral kernel p r := by
    simpa [u, v, w, q] using
      (rectangleBoundaryIntegral_eq_boundaryRectIntegral kernel p r).symm
  rw [houter_inner, hinner]
  exact rectangleBoundaryIntegral_sub_inv_center p hr

lemma boundaryRectIntegral_mul_const
    (f : ℂ → ℂ) (a : ℂ) (x0 x1 y0 y1 : ℝ) :
    boundaryRectIntegral (fun z => f z * a) x0 x1 y0 y1 =
      boundaryRectIntegral f x0 x1 y0 y1 * a := by
  have hbottom :
      (∫ x : ℝ in x0..x1, f (x + y0 * I) * a) =
        (∫ x : ℝ in x0..x1, f (x + y0 * I)) * a :=
    intervalIntegral.integral_mul_const a _
  have htop :
      (∫ x : ℝ in x0..x1, f (x + y1 * I) * a) =
        (∫ x : ℝ in x0..x1, f (x + y1 * I)) * a :=
    intervalIntegral.integral_mul_const a _
  have hright :
      (∫ y : ℝ in y0..y1, f ((x1 : ℂ) + y * I) * a) =
        (∫ y : ℝ in y0..y1, f ((x1 : ℂ) + y * I)) * a :=
    intervalIntegral.integral_mul_const a _
  have hleft :
      (∫ y : ℝ in y0..y1, f ((x0 : ℂ) + y * I) * a) =
        (∫ y : ℝ in y0..y1, f ((x0 : ℂ) + y * I)) * a :=
    intervalIntegral.integral_mul_const a _
  unfold boundaryRectIntegral
  dsimp only
  rw [hbottom, htop, hright, hleft]
  simp only [smul_eq_mul]
  ring

private lemma simplePoleTerm_boundaryRectIntervalIntegrable
    (p a : ℂ) {x0 x1 y0 y1 : ℝ}
    (hx0p : x0 < p.re) (hpx1 : p.re < x1)
    (hy0p : y0 < p.im) (hpy1 : p.im < y1) :
    IntervalIntegrable (fun x : ℝ => ((x + y0 * I) - p)⁻¹ * a)
        MeasureTheory.volume x0 x1 ∧
      IntervalIntegrable (fun x : ℝ => ((x + y1 * I) - p)⁻¹ * a)
        MeasureTheory.volume x0 x1 ∧
      IntervalIntegrable (fun y : ℝ => ((x1 : ℂ) + y * I - p)⁻¹ * a)
        MeasureTheory.volume y0 y1 ∧
      IntervalIntegrable (fun y : ℝ => ((x0 : ℂ) + y * I - p)⁻¹ * a)
        MeasureTheory.volume y0 y1 := by
  have horizontal_continuous : ∀ y : ℝ, y ≠ p.im →
      Continuous (fun x : ℝ => ((x + y * I) - p)⁻¹ * a) := by
    intro y hy
    apply (((Complex.continuous_ofReal.add
      (continuous_const.mul continuous_const)).sub continuous_const).inv₀ ?_).mul
      continuous_const
    intro x hx
    apply hy
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have vertical_continuous : ∀ x : ℝ, x ≠ p.re →
      Continuous (fun y : ℝ => (((x : ℂ) + y * I) - p)⁻¹ * a) := by
    intro x hx
    apply (((continuous_const.add
      (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const).inv₀ ?_).mul
      continuous_const
    intro y hy
    apply hx
    have hr' := congrArg Complex.re hy
    simp at hr'
    linarith
  exact ⟨
    (horizontal_continuous y0 (by linarith)).intervalIntegrable x0 x1,
    (horizontal_continuous y1 (by linarith)).intervalIntegrable x0 x1,
    (vertical_continuous x1 (by linarith)).intervalIntegrable y0 y1,
    (vertical_continuous x0 (by linarith)).intervalIntegrable y0 y1⟩

lemma boundaryRectIntegral_finset_sum
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset ι) (f : ι → ℂ → E) (x0 x1 y0 y1 : ℝ)
    (hbottom : ∀ i ∈ s, IntervalIntegrable
      (fun x : ℝ => f i (x + y0 * I)) MeasureTheory.volume x0 x1)
    (htop : ∀ i ∈ s, IntervalIntegrable
      (fun x : ℝ => f i (x + y1 * I)) MeasureTheory.volume x0 x1)
    (hright : ∀ i ∈ s, IntervalIntegrable
      (fun y : ℝ => f i ((x1 : ℂ) + y * I)) MeasureTheory.volume y0 y1)
    (hleft : ∀ i ∈ s, IntervalIntegrable
      (fun y : ℝ => f i ((x0 : ℂ) + y * I)) MeasureTheory.volume y0 y1) :
    boundaryRectIntegral (fun z => ∑ i ∈ s, f i z) x0 x1 y0 y1 =
      ∑ i ∈ s, boundaryRectIntegral (f i) x0 x1 y0 y1 := by
  unfold boundaryRectIntegral
  dsimp only
  rw [intervalIntegral.integral_finset_sum hbottom,
    intervalIntegral.integral_finset_sum htop,
    intervalIntegral.integral_finset_sum hright,
    intervalIntegral.integral_finset_sum hleft]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.smul_sum]

/-- Finite simple principal parts satisfy the residue formula on an arbitrary
axis-parallel rectangle containing all poles in its interior. -/
theorem boundaryRectIntegral_eq_finite_simple_pole_residue_sum
    {x0 x1 y0 y1 : ℝ} (poles : Finset ℂ) (residue : ℂ → ℂ)
    (hpoles : ∀ p ∈ poles,
      x0 < p.re ∧ p.re < x1 ∧ y0 < p.im ∧ p.im < y1) :
    boundaryRectIntegral
        (fun z : ℂ => ∑ p ∈ poles, (z - p)⁻¹ * residue p)
        x0 x1 y0 y1 =
      (2 * Real.pi * I) * ∑ p ∈ poles, residue p := by
  let term : ℂ → ℂ → ℂ := fun p z => (z - p)⁻¹ * residue p
  have hedges : ∀ p ∈ poles,
      IntervalIntegrable (fun x : ℝ => term p (x + y0 * I))
          MeasureTheory.volume x0 x1 ∧
        IntervalIntegrable (fun x : ℝ => term p (x + y1 * I))
          MeasureTheory.volume x0 x1 ∧
        IntervalIntegrable (fun y : ℝ => term p ((x1 : ℂ) + y * I))
          MeasureTheory.volume y0 y1 ∧
        IntervalIntegrable (fun y : ℝ => term p ((x0 : ℂ) + y * I))
          MeasureTheory.volume y0 y1 := by
    intro p hp
    have h := hpoles p hp
    simpa [term] using simplePoleTerm_boundaryRectIntervalIntegrable
      p (residue p) h.1 h.2.1 h.2.2.1 h.2.2.2
  have hlinear :
      boundaryRectIntegral (fun z : ℂ => ∑ p ∈ poles, term p z)
          x0 x1 y0 y1 =
        ∑ p ∈ poles, boundaryRectIntegral (term p) x0 x1 y0 y1 :=
    boundaryRectIntegral_finset_sum poles term x0 x1 y0 y1
      (fun p hp => (hedges p hp).1)
      (fun p hp => (hedges p hp).2.1)
      (fun p hp => (hedges p hp).2.2.1)
      (fun p hp => (hedges p hp).2.2.2)
  change boundaryRectIntegral (fun z : ℂ => ∑ p ∈ poles, term p z)
      x0 x1 y0 y1 = _
  rw [hlinear]
  calc
    (∑ p ∈ poles, boundaryRectIntegral (term p) x0 x1 y0 y1) =
        ∑ p ∈ poles, (2 * Real.pi * I) * residue p := by
      apply Finset.sum_congr rfl
      intro p hp
      have h := hpoles p hp
      rw [show term p = fun z : ℂ => (z - p)⁻¹ * residue p by rfl,
        boundaryRectIntegral_mul_const,
        boundaryRectIntegral_sub_inv_of_mem p h.1 h.2.1 h.2.2.1 h.2.2.2]
    _ = (2 * Real.pi * I) * ∑ p ∈ poles, residue p := by
      rw [Finset.mul_sum]

lemma boundaryRectIntervalIntegrable_of_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {x0 x1 y0 y1 : ℝ}
    (hf : ContinuousOn f ([[x0, x1]] ×ℂ [[y0, y1]])) :
    IntervalIntegrable (fun x : ℝ => f (x + y0 * I))
        MeasureTheory.volume x0 x1 ∧
      IntervalIntegrable (fun x : ℝ => f (x + y1 * I))
        MeasureTheory.volume x0 x1 ∧
      IntervalIntegrable (fun y : ℝ => f ((x1 : ℂ) + y * I))
        MeasureTheory.volume y0 y1 ∧
      IntervalIntegrable (fun y : ℝ => f ((x0 : ℂ) + y * I))
        MeasureTheory.volume y0 y1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (hf.comp
      (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const)).continuousOn ?_).intervalIntegrable
    intro x hx
    simpa [mem_reProdIm] using
      And.intro hx (left_mem_uIcc : y0 ∈ [[y0, y1]])
  · apply (hf.comp
      (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const)).continuousOn ?_).intervalIntegrable
    intro x hx
    simpa [mem_reProdIm] using
      And.intro hx (right_mem_uIcc : y1 ∈ [[y0, y1]])
  · apply (hf.comp
      (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const)).continuousOn ?_).intervalIntegrable
    intro y hy
    simpa [mem_reProdIm] using
      And.intro (right_mem_uIcc : x1 ∈ [[x0, x1]]) hy
  · apply (hf.comp
      (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const)).continuousOn ?_).intervalIntegrable
    intro y hy
    simpa [mem_reProdIm] using
      And.intro (left_mem_uIcc : x0 ∈ [[x0, x1]]) hy

lemma boundaryRectIntegral_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : ℂ → E) (x0 x1 y0 y1 : ℝ)
    (hfb : IntervalIntegrable (fun x : ℝ => f (x + y0 * I))
      MeasureTheory.volume x0 x1)
    (hgb : IntervalIntegrable (fun x : ℝ => g (x + y0 * I))
      MeasureTheory.volume x0 x1)
    (hft : IntervalIntegrable (fun x : ℝ => f (x + y1 * I))
      MeasureTheory.volume x0 x1)
    (hgt : IntervalIntegrable (fun x : ℝ => g (x + y1 * I))
      MeasureTheory.volume x0 x1)
    (hfr : IntervalIntegrable (fun y : ℝ => f ((x1 : ℂ) + y * I))
      MeasureTheory.volume y0 y1)
    (hgr : IntervalIntegrable (fun y : ℝ => g ((x1 : ℂ) + y * I))
      MeasureTheory.volume y0 y1)
    (hfl : IntervalIntegrable (fun y : ℝ => f ((x0 : ℂ) + y * I))
      MeasureTheory.volume y0 y1)
    (hgl : IntervalIntegrable (fun y : ℝ => g ((x0 : ℂ) + y * I))
      MeasureTheory.volume y0 y1) :
    boundaryRectIntegral (fun z => f z + g z) x0 x1 y0 y1 =
      boundaryRectIntegral f x0 x1 y0 y1 +
        boundaryRectIntegral g x0 x1 y0 y1 := by
  unfold boundaryRectIntegral
  dsimp only
  rw [intervalIntegral.integral_add hfb hgb,
    intervalIntegral.integral_add hft hgt,
    intervalIntegral.integral_add hfr hgr,
    intervalIntegral.integral_add hfl hgl]
  module

/-- A holomorphic remainder plus finitely many simple principal parts satisfies
the residue formula on an arbitrary axis-parallel rectangle. -/
theorem boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
    {g : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (poles : Finset ℂ) (residue : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hpoles : ∀ p ∈ poles,
      x0 < p.re ∧ p.re < x1 ∧ y0 < p.im ∧ p.im < y1) :
    boundaryRectIntegral
        (fun z : ℂ => g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p)
        x0 x1 y0 y1 =
      (2 * Real.pi * I) * ∑ p ∈ poles, residue p := by
  let term : ℂ → ℂ → ℂ := fun p z => (z - p)⁻¹ * residue p
  let principal : ℂ → ℂ := fun z => ∑ p ∈ poles, term p z
  have hg_edges := boundaryRectIntervalIntegrable_of_continuousOn hg.continuousOn
  have hterm_edges : ∀ p ∈ poles,
      IntervalIntegrable (fun x : ℝ => term p (x + y0 * I))
          MeasureTheory.volume x0 x1 ∧
        IntervalIntegrable (fun x : ℝ => term p (x + y1 * I))
          MeasureTheory.volume x0 x1 ∧
        IntervalIntegrable (fun y : ℝ => term p ((x1 : ℂ) + y * I))
          MeasureTheory.volume y0 y1 ∧
        IntervalIntegrable (fun y : ℝ => term p ((x0 : ℂ) + y * I))
          MeasureTheory.volume y0 y1 := by
    intro p hp
    have h := hpoles p hp
    simpa [term] using simplePoleTerm_boundaryRectIntervalIntegrable
      p (residue p) h.1 h.2.1 h.2.2.1 h.2.2.2
  have hprincipal_bottom : IntervalIntegrable
      (fun x : ℝ => principal (x + y0 * I))
      MeasureTheory.volume x0 x1 := by
    have h := IntervalIntegrable.sum poles (fun p hp => (hterm_edges p hp).1)
    have heq : (∑ p ∈ poles, fun x : ℝ => term p (x + y0 * I)) =
        fun x : ℝ => principal (x + y0 * I) := by
      funext x
      simp [principal]
    rw [← heq]
    exact h
  have hprincipal_top : IntervalIntegrable
      (fun x : ℝ => principal (x + y1 * I))
      MeasureTheory.volume x0 x1 := by
    have h := IntervalIntegrable.sum poles (fun p hp => (hterm_edges p hp).2.1)
    have heq : (∑ p ∈ poles, fun x : ℝ => term p (x + y1 * I)) =
        fun x : ℝ => principal (x + y1 * I) := by
      funext x
      simp [principal]
    rw [← heq]
    exact h
  have hprincipal_right : IntervalIntegrable
      (fun y : ℝ => principal ((x1 : ℂ) + y * I))
      MeasureTheory.volume y0 y1 := by
    have h := IntervalIntegrable.sum poles (fun p hp => (hterm_edges p hp).2.2.1)
    have heq : (∑ p ∈ poles, fun y : ℝ => term p ((x1 : ℂ) + y * I)) =
        fun y : ℝ => principal ((x1 : ℂ) + y * I) := by
      funext y
      simp [principal]
    rw [← heq]
    exact h
  have hprincipal_left : IntervalIntegrable
      (fun y : ℝ => principal ((x0 : ℂ) + y * I))
      MeasureTheory.volume y0 y1 := by
    have h := IntervalIntegrable.sum poles (fun p hp => (hterm_edges p hp).2.2.2)
    have heq : (∑ p ∈ poles, fun y : ℝ => term p ((x0 : ℂ) + y * I)) =
        fun y : ℝ => principal ((x0 : ℂ) + y * I) := by
      funext y
      simp [principal]
    rw [← heq]
    exact h
  have hadd :
      boundaryRectIntegral (fun z => g z + principal z) x0 x1 y0 y1 =
        boundaryRectIntegral g x0 x1 y0 y1 +
          boundaryRectIntegral principal x0 x1 y0 y1 :=
    boundaryRectIntegral_add g principal x0 x1 y0 y1
      hg_edges.1 hprincipal_bottom
      hg_edges.2.1 hprincipal_top
      hg_edges.2.2.1 hprincipal_right
      hg_edges.2.2.2 hprincipal_left
  have hg_zero : boundaryRectIntegral g x0 x1 y0 y1 = 0 :=
    boundaryRectIntegral_eq_zero_of_differentiableOn g x0 x1 y0 y1 hg
  change boundaryRectIntegral (fun z => g z + principal z) x0 x1 y0 y1 = _
  rw [hadd, hg_zero, zero_add]
  simpa [principal, term] using
    boundaryRectIntegral_eq_finite_simple_pole_residue_sum
      poles residue hpoles

end MathlibAux
