import HardyTheorem.ConreyHorizontalArgument

/-!
Uniform unweighted V1 argument control at an already selected nonzero height.
The cutoff two is used only for this auxiliary estimate, never for the long
mollified mean square. The scalar principal parts include every multiplicity.
-/

open Complex Set MeasureTheory MeromorphicOn
open PrimeNumberTheorem.CarlsonZeroDensity

namespace HardyTheorem

private theorem exists_conreyHorizontalArgument_explicit :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Y : ℕ} {R L U J t : ℝ}, 2 ≤ Y →
      (Y : ℝ) ≤ Real.exp L → 0 ≤ R → R ≤ 6 / 5 → 40000 ≤ L →
      conreyHorizontalRightEdge L + 1 ≤ U → U + 1 ≤ Real.exp L →
      conreyHorizontalJensenFactorZeroMass Y R L U ≤ J →
      t ∈ Icc U (U + 1) →
      (∀ x ∈ Icc (conreyHorizontalLeftEdge R L) (conreyHorizontalRightEdge L),
        conreyHorizontalJensenProduct Y R L ((x : ℂ) + I * t) ≠ 0) →
      |∫ x in conreyHorizontalLeftEdge R L..conreyHorizontalRightEdge L,
        (logDeriv (conreyHorizontalJensenProduct Y R L) ((x : ℂ) + I * t)).im| ≤
        (conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L) *
          (128 * max (conreyHorizontalJensenFactorLogVariationMajorant C Y R L U J) 1 *
            conreyHorizontalJensenOuterRadius L / conreyHorizontalJensenRadiusGap R L ^ 2) +
          Real.pi * J := by
  obtain ⟨C, hC, hfactor⟩ := exists_conreyHorizontalJensenGoodFactor_logDeriv_le_explicit
  refine ⟨C, hC, ?_⟩
  intro Y R L U J t hY hYtop hR0 hRmax hL hU hUtop hmass ht hne
  obtain ⟨q, g, _, hg, hgne, hdecomp, hregular⟩ :=
    hfactor hY hYtop hR0 hRmax hL hU hUtop hmass
  classical
  let a := conreyHorizontalLeftEdge R L
  let b := conreyHorizontalRightEdge L
  let c := conreyHorizontalJensenCenter L U
  let r := conreyHorizontalJensenFactorRadius R L
  let f := conreyHorizontalJensenProduct Y R L
  let z : ℝ → ℂ := fun x => (x : ℂ) + I * t
  let D := MeromorphicOn.divisor f (Metric.closedBall c r)
  have hfinite : D.support.Finite := D.finiteSupport (isCompact_closedBall c r)
  let P := hfinite.toFinset
  let principal : ℝ → ℝ := fun x => ∑ rho ∈ P, (D rho : ℝ) * ((z x - rho)⁻¹).im
  let regular : ℝ → ℝ := fun x => (logDeriv g (z x)).im
  let K := 128 * max (conreyHorizontalJensenFactorLogVariationMajorant C Y R L U J) 1 *
    conreyHorizontalJensenOuterRadius L / conreyHorizontalJensenRadiusGap R L ^ 2
  have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
  have hfactorA : AnalyticOnNhd ℂ f (Metric.closedBall c r) := by
    exact (analyticOnNhd_conreyExplicitMollifiedV1_horizontalJensenOuterClosedBall
      Y (conreyHorizontalLeftEdge R L) L U hL hU).mono
        (Metric.closedBall_subset_closedBall hbuffer.2.2.2.le)
  have hD0 : 0 ≤ D := hfactorA.divisor_nonneg
  have hab : a ≤ b := by
    have hLpos : 0 < L := by linarith
    have hq := div_nonneg hR0 hLpos.le
    have hlog := two_le_log_of_forty_thousand_le hL
    dsimp [a, b, conreyHorizontalLeftEdge, conreyHorizontalRightEdge]
    linarith
  have hzinner : ∀ x ∈ Icc a b, z x ∈ Metric.closedBall c
      (conreyHorizontalJensenInnerRadius R L) := by
    intro x hx
    apply conreyHorizontalJensenRectangle_subset_innerClosedBall R L U
    change (z x).re ∈ Icc a b ∧ (z x).im ∈ Icc U (U + 1)
    simpa [z] using And.intro hx ht
  have hzball : ∀ x ∈ Icc a b, z x ∈ Metric.ball c r := by
    intro x hx
    exact Metric.closedBall_subset_ball
      (hbuffer.1.trans (hbuffer.2.1.trans hbuffer.2.2.1)) (hzinner x hx)
  have hcomplex : ∀ x : ℝ,
      (∑ᶠ rho, (D rho : ℂ) * (z x - rho)⁻¹) =
        ∑ rho ∈ P, (D rho : ℂ) * (z x - rho)⁻¹ := by
    intro x
    apply finsum_eq_sum_of_support_subset
    intro rho hrho
    change rho ∈ hfinite.toFinset
    rw [hfinite.mem_toFinset]
    by_contra hn
    have hzero : D rho = 0 := by simpa [Function.mem_support] using hn
    simp [hzero] at hrho
  have hmassEq : (∑ rho ∈ P, (D rho : ℝ)) =
      conreyHorizontalJensenFactorZeroMass Y R L U := by
    symm
    apply finsum_eq_sum_of_support_subset
    intro rho hrho
    change rho ∈ hfinite.toFinset
    rw [hfinite.mem_toFinset]
    simpa [Function.mem_support] using hrho
  have hsplit : ∀ x ∈ Icc a b, (logDeriv f (z x)).im = principal x + regular x := by
    intro x hx
    have hh := congrArg Complex.im (hdecomp (z x) (hzball x hx) (hne x hx))
    rw [hcomplex] at hh
    simpa [principal, regular] using hh
  have hprincipalInt : IntervalIntegrable principal volume a b := by
    have hsum : ∀ Q : Finset ℂ, IntervalIntegrable
        (fun x : ℝ => ∑ rho ∈ Q, (D rho : ℝ) * ((z x - rho)⁻¹).im) volume a b := by
      intro Q
      induction Q using Finset.induction_on with
      | empty => simp
      | @insert rho Q hnot ih =>
        simpa only [Finset.sum_insert hnot] using
          ((intervalIntegrable_im_inv_horizontal_sub (rho := rho) (t := t)
            (a := a) (b := b)).const_mul (D rho : ℝ)).add ih
    exact hsum P
  have hregularCont : ContinuousOn regular (uIcc a b) := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hzclosed := Metric.ball_subset_closedBall (hzball x hx)
    have hlog := ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero
      (hg (z x) hzclosed) (hgne ⟨z x, hzclosed⟩)
    exact (Complex.continuous_im.continuousAt.comp
      (hlog.continuousAt.comp (by fun_prop : ContinuousAt z x))).continuousWithinAt
  have hregularInt : IntervalIntegrable regular volume a b := hregularCont.intervalIntegrable
  have hintegral : (∫ x in a..b, (logDeriv f (z x)).im) =
      (∫ x in a..b, principal x) + ∫ x in a..b, regular x := by
    rw [← intervalIntegral.integral_add hprincipalInt hregularInt]
    apply intervalIntegral.integral_congr
    intro x hx
    exact hsplit x (by simpa [uIcc_of_le hab] using hx)
  have hprincipalBound : |∫ x in a..b, principal x| ≤ Real.pi * J := by
    have h := abs_integral_finset_principalParts_le P (fun rho => (D rho : ℝ)) hab
      (fun rho _ => by exact_mod_cast hD0 rho) (t := t)
    rw [hmassEq] at h
    exact h.trans (mul_le_mul_of_nonneg_left hmass Real.pi_pos.le)
  have hregularBound : |∫ x in a..b, regular x| ≤ (b - a) * K := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := regular) (C := K) (a := a) (b := b) (by
        intro x hx
        rw [uIoc_of_le hab] at hx
        exact (Complex.abs_im_le_norm _).trans (hregular _ (hzinner x ⟨hx.1.le, hx.2⟩)))
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab), mul_comm] using h
  change |∫ x in a..b, (logDeriv f (z x)).im| ≤ (b - a) * K + Real.pi * J
  rw [hintegral]
  exact (abs_add_le _ _).trans
    ((add_le_add hprincipalBound hregularBound).trans_eq (by ring))

/-- A single absolute threshold controls the actual V1 argument on every
nonzero horizontal segment in the permitted unit windows. No new height is
chosen and no moment assumption is used. -/
theorem exists_conreyV1_horizontalArgument_le_coarse :
    ∃ L0 : ℝ, 40000 ≤ L0 ∧ ∀ {L U t : ℝ}, L0 ≤ L →
      2 * Real.log L + 1 ≤ U → U + 1 ≤ Real.exp L → t ∈ Icc U (U + 1) →
      (∀ x ∈ Icc (1 / 2 : ℝ) (2 * Real.log L),
        conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L ((x : ℂ) + I * t) ≠ 0) →
      |∫ x in (1 / 2 : ℝ)..2 * Real.log L,
        (logDeriv (conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L)
          ((x : ℂ) + I * t)).im| ≤ 1100000000000 * L ^ 7 := by
  obtain ⟨Creg, hCreg, hbound⟩ := exists_conreyHorizontalArgument_explicit
  obtain ⟨Cmass, hCmass, hmass⟩ := exists_conreyHorizontalJensenFactorZeroMassMajorant_bounds
  refine ⟨40000 + Creg + Cmass, by linarith, ?_⟩
  intro L U t hlarge hU hUtop ht hne
  have hL : 40000 ≤ L := by linarith
  have hYtop : ((2 : ℕ) : ℝ) ≤ Real.exp L := by norm_cast; linarith [Real.add_one_le_exp L]
  have hCregTop : Creg ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hCmassTop : Cmass ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hR0 : (0 : ℝ) ≤ 0 := le_rfl
  have hRmax : (0 : ℝ) ≤ 6 / 5 := by norm_num
  have hY : 2 ≤ (2 : ℕ) := le_rfl
  have hmassBounds := hmass hY hYtop hR0 hRmax hL hU hUtop hCmassTop
  let J := conreyHorizontalJensenFactorZeroMassMajorant Cmass 2 0 L U
  let w := conreyHorizontalRightEdge L - conreyHorizontalLeftEdge 0 L
  let outer := conreyHorizontalJensenOuterRadius L
  let gap := conreyHorizontalJensenRadiusGap 0 L
  let V := conreyHorizontalJensenFactorLogVariationMajorant Creg 2 0 L U J
  let K := 128 * max V 1 * outer / gap ^ 2
  have hVtop : V ≤ 81000000 * L ^ 4 :=
    conreyHorizontalJensenFactorLogVariationMajorant_le_eightyOneMillion
      hCreg hCregTop hCmass hCmassTop hY hYtop hR0 hRmax hL hU hUtop
  have hgeometry := conreyHorizontalJensenCoarseGeometry hR0 hRmax hL
  have houter0 : 0 ≤ outer := by
    have hlog := two_le_log_of_forty_thousand_le hL
    dsimp [outer, conreyHorizontalJensenOuterRadius, conreyHorizontalRightEdge]
    linarith
  have hgapPos : 0 < gap := by
    have h := one_fifth_lt_conreyHorizontalJensenRadiusGap hR0 hRmax hL
    dsimp [gap]
    linarith
  have hJ0 : 0 ≤ J := hmassBounds.2.1
  have hJtop : J ≤ 1000 * L ^ 2 := hmassBounds.2.2
  have hw2 : 2 ≤ w := by
    have hlog := two_le_log_of_forty_thousand_le hL
    dsimp [w, conreyHorizontalRightEdge, conreyHorizontalLeftEdge]
    simp only [zero_div, sub_zero]
    linarith
  have hK0 : 0 ≤ K := by
    have hmax0 : 0 ≤ max V 1 := (le_max_right V 1).trans' (by norm_num)
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hmax0) houter0) (sq_nonneg gap)
  have hrhs : w * K + Real.pi * J ≤ 1100000000000 * L ^ 7 := by
    calc
      _ ≤ (w ^ 2 / 2) * K + w * Real.pi * J := by
        have hfirst := mul_le_mul_of_nonneg_right (show w ≤ w ^ 2 / 2 by nlinarith) hK0
        have hsecond := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ w by linarith)
          (mul_nonneg Real.pi_pos.le hJ0)
        nlinarith only [hfirst, hsecond]
      _ ≤ _ := conreyHorizontalJensenExplicitHorizontalRhs_le_coarse
        hL hgeometry.1 hgeometry.2.1 hgapPos houter0 hgeometry.2.2 hVtop hJ0 hJtop
  have hproduct : conreyHorizontalJensenProduct 2 0 L =
      conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L := by
    funext s
    change conreyDegreeOneV1 _ _ _ _ s * conreyMollifier 2 _ conreyExplicitP s = _
    rw [conreyMollifier_two (by norm_num [conreyExplicitP])
      (by norm_num [conreyExplicitP]), mul_one]
  have hline : ∀ x ∈ Icc (conreyHorizontalLeftEdge 0 L) (conreyHorizontalRightEdge L),
      conreyHorizontalJensenProduct 2 0 L ((x : ℂ) + I * t) ≠ 0 := by
    simpa [hproduct, conreyHorizontalLeftEdge, conreyHorizontalRightEdge] using hne
  have hactual := hbound hY hYtop hR0 hRmax hL hU hUtop hmassBounds.1 ht hline
  rw [hproduct] at hactual
  have hfinal := hactual.trans hrhs
  simpa [conreyHorizontalLeftEdge, conreyHorizontalRightEdge] using hfinal

end HardyTheorem
