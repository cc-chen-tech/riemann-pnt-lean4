import HardyTheorem.ConreyHorizontalJensenIntegral

/-!
# Coarse asymptotics for Conrey's selected horizontal edge

This module deliberately keeps the growth constant used by the regular
factor separate from the one used by the Jensen mass estimate.  The bounds
are coarse fixed polynomials in `L = log T`; no new analytic cancellation is
introduced here.
-/

open Complex Set MeasureTheory MeromorphicOn Filter

namespace HardyTheorem

/-- The moving height base is bounded by three copies of `exp (2L)`. -/
theorem conreyHorizontalJensenHeightBase_le_three_mul_exp_two
    {L U : ℝ} (hL : 40000 ≤ L) (hUtop : U + 1 ≤ Real.exp L) :
    conreyHorizontalJensenHeightBase L U ≤ 3 * Real.exp (2 * L) := by
  have hL0 : 0 ≤ L := by linarith
  have hlogL : Real.log L ≤ L := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < L)
    linarith
  have hU : U ≤ Real.exp L := by linarith
  have hexpMono : Real.exp L ≤ Real.exp (2 * L) :=
    Real.exp_le_exp.mpr (by linarith)
  have hlinearExp : 2 * L ≤ Real.exp (2 * L) := by
    linarith [Real.add_one_le_exp (2 * L)]
  have htenExp : 10 ≤ Real.exp (2 * L) :=
    (by linarith : (10 : ℝ) ≤ 2 * L).trans hlinearExp
  dsimp [conreyHorizontalJensenHeightBase,
    conreyHorizontalRightEdge]
  linarith

/-- The logarithm entering both Jensen numerators is at most `25L` once its
fixed growth constant is below `exp L`. -/
theorem conreyHorizontalJensenGrowthLog_le_twentyFive_mul
    {C L U : ℝ} {Y : ℕ} (hC : 1 ≤ C) (hCtop : C ≤ Real.exp L)
    (hY : 2 ≤ Y) (hYtop : (Y : ℝ) ≤ Real.exp L)
    (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U)
    (hUtop : U + 1 ≤ Real.exp L) :
    Real.log (C * (Y : ℝ) *
        conreyHorizontalJensenHeightBase L U ^ 6 * (L + 2) ^ 2) +
      Real.log 6 ≤ 25 * L := by
  let H := conreyHorizontalJensenHeightBase L U
  have hLpos : 0 < L := by linarith
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hYpos : 0 < (Y : ℝ) := by positivity
  have hHone : 1 ≤ H := by
    simpa [H] using one_le_conreyHorizontalJensenHeightBase hL hU
  have hHpos : 0 < H := zero_lt_one.trans_le hHone
  have hLtwoPos : 0 < L + 2 := by linarith
  have hlogC : Real.log C ≤ L := by
    simpa only [Real.log_exp] using Real.log_le_log hCpos hCtop
  have hlogY : Real.log (Y : ℝ) ≤ L := by
    simpa only [Real.log_exp] using Real.log_le_log hYpos hYtop
  have hHtop : H ≤ 3 * Real.exp (2 * L) := by
    simpa [H] using
      conreyHorizontalJensenHeightBase_le_three_mul_exp_two hL hUtop
  have hlogThree : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have hlogH : Real.log H ≤ 3 * L := by
    have h := Real.log_le_log hHpos hHtop
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
      (Real.exp_ne_zero (2 * L)), Real.log_exp] at h
    linarith
  have hLtwoTop : L + 2 ≤ 2 * Real.exp L := by
    have honeExp : 1 ≤ Real.exp L := Real.one_le_exp (by linarith)
    linarith [Real.add_one_le_exp L]
  have hlogTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogLtwo : Real.log (L + 2) ≤ 2 * L := by
    have h := Real.log_le_log hLtwoPos hLtwoTop
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (Real.exp_ne_zero L), Real.log_exp] at h
    linarith
  have hlogSix : Real.log 6 ≤ L := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
    norm_num at h
    linarith
  rw [Real.log_mul
      (mul_ne_zero (mul_ne_zero hCpos.ne' hYpos.ne')
        (pow_ne_zero 6 hHpos.ne'))
      (pow_ne_zero 2 hLtwoPos.ne'),
    Real.log_mul (mul_ne_zero hCpos.ne' hYpos.ne')
      (pow_ne_zero 6 hHpos.ne'),
    Real.log_mul hCpos.ne' hYpos.ne', Real.log_pow, Real.log_pow]
  norm_num
  linarith

/-- The moving Jensen denominator loses at most one factor of `L`. -/
theorem conreyHorizontalJensenFactorLogDenominator_lower
    {R L : ℝ} (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5)
    (hL : 40000 ≤ L) :
    1 / (40 * L) ≤
      Real.log (conreyHorizontalJensenOuterRadius L /
        conreyHorizontalJensenFactorRadius R L) := by
  let outer := conreyHorizontalJensenOuterRadius L
  let b := conreyHorizontalJensenFactorRadius R L
  let gap := conreyHorizontalJensenRadiusGap R L
  have hLpos : 0 < L := by linarith
  have hlogL : Real.log L ≤ L := by
    have h := Real.log_le_sub_one_of_pos hLpos
    linarith
  have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
  have hbpos : 0 < b := by
    have hr := conreyHorizontalJensenInnerRadius_pos R L
    simpa [b] using hr.trans
      (hbuffer.1.trans (hbuffer.2.1.trans hbuffer.2.2.1))
  have hbOuter : b < outer := by simpa [b, outer] using hbuffer.2.2.2
  have houterPos : 0 < outer := hbpos.trans hbOuter
  have houterTop : outer ≤ 2 * L := by
    dsimp [outer, conreyHorizontalJensenOuterRadius,
      conreyHorizontalRightEdge]
    linarith
  have hgap : (1 / 5 : ℝ) < gap := by
    simpa [gap] using
      one_fifth_lt_conreyHorizontalJensenRadiusGap hR0 hRmax hL
  have hgapEq : outer - b = gap / 4 := by
    dsimp [outer, b, gap, conreyHorizontalJensenFactorRadius,
      conreyHorizontalJensenRadiusGap]
    ring
  have hratioPos : 0 < outer / b := div_pos houterPos hbpos
  have hlog := Real.one_sub_inv_le_log_of_pos hratioPos
  have hrewrite : 1 - (outer / b)⁻¹ = (outer - b) / outer := by
    field_simp [hbpos.ne', houterPos.ne']
  rw [hrewrite, hgapEq] at hlog
  have hlower : 1 / (40 * L) ≤ gap / 4 / outer := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hLpos)
      houterPos).2
    nlinarith
  exact hlower.trans hlog

/-- The exact Jensen quotient used as a zero-mass majorant on the buffered
factorization disk. -/
noncomputable def conreyHorizontalJensenFactorZeroMassMajorant
    (C : ℝ) (Y : ℕ) (R L U : ℝ) : ℝ :=
  (Real.log (C * (Y : ℝ) *
      conreyHorizontalJensenHeightBase L U ^ 6 * (L + 2) ^ 2) +
    Real.log 6) /
      Real.log (conreyHorizontalJensenOuterRadius L /
        conreyHorizontalJensenFactorRadius R L)

/-- The exact buffered Jensen quotient is nonnegative and at most
`1000 * L^2`. -/
theorem conreyHorizontalJensenFactorZeroMassMajorant_bounds
    {C L U : ℝ} {Y : ℕ} {R : ℝ}
    (hC : 1 ≤ C) (hCtop : C ≤ Real.exp L)
    (hY : 2 ≤ Y) (hYtop : (Y : ℝ) ≤ Real.exp L)
    (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U)
    (hUtop : U + 1 ≤ Real.exp L) :
    0 ≤ conreyHorizontalJensenFactorZeroMassMajorant C Y R L U ∧
      conreyHorizontalJensenFactorZeroMassMajorant C Y R L U ≤
        1000 * L ^ 2 := by
  let H := conreyHorizontalJensenHeightBase L U
  let numerator := Real.log (C * (Y : ℝ) * H ^ 6 * (L + 2) ^ 2) +
    Real.log 6
  let denominator := Real.log (conreyHorizontalJensenOuterRadius L /
    conreyHorizontalJensenFactorRadius R L)
  have hLpos : 0 < L := by linarith
  have hYreal : 1 ≤ (Y : ℝ) := by exact_mod_cast (show 1 ≤ Y by omega)
  have hHone : 1 ≤ H := by
    simpa [H] using one_le_conreyHorizontalJensenHeightBase hL hU
  have hMone : 1 ≤ C * (Y : ℝ) * H ^ 6 * (L + 2) ^ 2 := by
    have hCY : 1 ≤ C * (Y : ℝ) :=
      one_le_mul_of_one_le_of_one_le hC hYreal
    have hHpow : 1 ≤ H ^ 6 := one_le_pow₀ hHone
    have hLpow : 1 ≤ (L + 2) ^ 2 := one_le_pow₀ (by linarith)
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hCY hHpow) hLpow
  have hnumNonneg : 0 ≤ numerator := by
    dsimp [numerator]
    exact add_nonneg (Real.log_nonneg hMone)
      (Real.log_nonneg (by norm_num))
  have hnumTop : numerator ≤ 25 * L := by
    simpa [numerator, H] using
      conreyHorizontalJensenGrowthLog_le_twentyFive_mul
        hC hCtop hY hYtop hL hU hUtop
  have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
  have hbpos : 0 < conreyHorizontalJensenFactorRadius R L := by
    have hr := conreyHorizontalJensenInnerRadius_pos R L
    exact hr.trans
      (hbuffer.1.trans (hbuffer.2.1.trans hbuffer.2.2.1))
  have hdenPos : 0 < denominator := by
    dsimp [denominator]
    exact Real.log_pos ((one_lt_div hbpos).2 hbuffer.2.2.2)
  have hdenLower : 1 / (40 * L) ≤ denominator := by
    simpa [denominator] using
      conreyHorizontalJensenFactorLogDenominator_lower hR0 hRmax hL
  have hscaleNonneg : 0 ≤ 1000 * L ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hdenLower hscaleNonneg
  have hnormalize : (1000 * L ^ 2) * (1 / (40 * L)) = 25 * L := by
    field_simp [hLpos.ne']
    ring
  constructor
  · dsimp [conreyHorizontalJensenFactorZeroMassMajorant, numerator,
      denominator, H]
    exact div_nonneg hnumNonneg hdenPos.le
  · dsimp [conreyHorizontalJensenFactorZeroMassMajorant, numerator,
      denominator, H]
    apply (div_le_iff₀ hdenPos).2
    calc
      numerator ≤ 25 * L := hnumTop
      _ = (1000 * L ^ 2) * (1 / (40 * L)) := hnormalize.symm
      _ ≤ (1000 * L ^ 2) * denominator := hscaled

/-- The actual buffered divisor mass has an exact Jensen majorant which is
simultaneously bounded by `1000 * L^2`. -/
theorem exists_conreyHorizontalJensenFactorZeroMassMajorant_bounds :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Y : ℕ} {R L U : ℝ}, 2 ≤ Y →
      (Y : ℝ) ≤ Real.exp L → 0 ≤ R → R ≤ 6 / 5 → 40000 ≤ L →
      conreyHorizontalRightEdge L + 1 ≤ U → U + 1 ≤ Real.exp L →
      C ≤ Real.exp L →
      conreyHorizontalJensenFactorZeroMass Y R L U ≤
          conreyHorizontalJensenFactorZeroMassMajorant C Y R L U ∧
        0 ≤ conreyHorizontalJensenFactorZeroMassMajorant C Y R L U ∧
        conreyHorizontalJensenFactorZeroMassMajorant C Y R L U ≤
          1000 * L ^ 2 := by
  rcases exists_conreyHorizontalJensenFactorZeroMass_le with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro Y R L U hY hYtop hR0 hRmax hL hU hUtop hCtop
  have hactual := hmass hY hYtop hR0 hRmax hL hU hUtop
  have hbounds := conreyHorizontalJensenFactorZeroMassMajorant_bounds
    hC hCtop hY hYtop hR0 hRmax hL hU hUtop
  exact ⟨by
    simpa [conreyHorizontalJensenFactorZeroMassMajorant] using hactual,
    hbounds⟩

/-- After inserting the exact Jensen mass majorant, the logarithmic variation
is bounded by a fixed fourth power of `L`.  The two growth constants remain
independent. -/
theorem conreyHorizontalJensenFactorLogVariationMajorant_le_eightyOneMillion
    {Creg Cmass L U : ℝ} {Y : ℕ} {R : ℝ}
    (hCreg : 1 ≤ Creg) (hCregTop : Creg ≤ Real.exp L)
    (hCmass : 1 ≤ Cmass) (hCmassTop : Cmass ≤ Real.exp L)
    (hY : 2 ≤ Y) (hYtop : (Y : ℝ) ≤ Real.exp L)
    (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5) (hL : 40000 ≤ L)
    (hU : conreyHorizontalRightEdge L + 1 ≤ U)
    (hUtop : U + 1 ≤ Real.exp L) :
    conreyHorizontalJensenFactorLogVariationMajorant Creg Y R L U
        (conreyHorizontalJensenFactorZeroMassMajorant Cmass Y R L U) ≤
      81000000 * L ^ 4 := by
  let J := conreyHorizontalJensenFactorZeroMassMajorant Cmass Y R L U
  let gap := conreyHorizontalJensenRadiusGap R L
  let b := conreyHorizontalJensenFactorRadius R L
  let delta := gap / (16 * (J + 1))
  have hLpos : 0 < L := by linarith
  have hJbounds := conreyHorizontalJensenFactorZeroMassMajorant_bounds
    hCmass hCmassTop hY hYtop hR0 hRmax hL hU hUtop
  have hJ0 : 0 ≤ J := by simpa [J] using hJbounds.1
  have hJtop : J ≤ 1000 * L ^ 2 := by simpa [J] using hJbounds.2
  have hgapPos : 0 < gap := by
    have h := one_fifth_lt_conreyHorizontalJensenRadiusGap hR0 hRmax hL
    simpa [gap] using (show 0 < conreyHorizontalJensenRadiusGap R L by linarith)
  have hgapLower : (1 / 5 : ℝ) < gap := by
    simpa [gap] using
      one_fifth_lt_conreyHorizontalJensenRadiusGap hR0 hRmax hL
  have hdenPos : 0 < 16 * (J + 1) := by positivity
  have hdeltaPos : 0 < delta := div_pos hgapPos hdenPos
  have hdeltaInv : delta⁻¹ = 16 * (J + 1) / gap := by
    dsimp [delta]
    field_simp [hgapPos.ne', hdenPos.ne']
  have hInvTop : delta⁻¹ ≤ 80 * (J + 1) := by
    rw [hdeltaInv]
    apply (div_le_iff₀ hgapPos).2
    nlinarith
  have hnegLogDelta : -Real.log delta ≤ 80 * (J + 1) := by
    rw [← Real.log_inv]
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hdeltaPos)
    linarith
  have hbuffer := conreyHorizontalJensenBufferGeometry hR0 hRmax hL
  have hbOne : 1 ≤ b := by
    simpa [b] using one_le_conreyHorizontalJensenFactorRadius hR0 hRmax hL
  have hlogL : Real.log L ≤ L := by
    have h := Real.log_le_sub_one_of_pos hLpos
    linarith
  have hbTop : b ≤ 2 * L := by
    have hbOuter : b ≤ conreyHorizontalJensenOuterRadius L := by
      simpa [b] using hbuffer.2.2.2.le
    have houterTop : conreyHorizontalJensenOuterRadius L ≤ 2 * L := by
      dsimp [conreyHorizontalJensenOuterRadius,
        conreyHorizontalRightEdge]
      linarith
    exact hbOuter.trans houterTop
  have hlogB : Real.log b ≤ 2 * L := by
    have h := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hbOne)
    linarith
  have hgrowth :
      Real.log (Creg * (Y : ℝ) *
          conreyHorizontalJensenHeightBase L U ^ 6 * (L + 2) ^ 2) +
        Real.log 6 ≤ 25 * L :=
    conreyHorizontalJensenGrowthLog_le_twentyFive_mul
      hCreg hCregTop hY hYtop hL hU hUtop
  have hLsqOne : 1 ≤ L ^ 2 := by nlinarith
  have hJone : J + 1 ≤ 1001 * L ^ 2 := by nlinarith
  have hcoeff : Real.log b - Real.log delta ≤ 80082 * L ^ 2 := by
    nlinarith
  have hweighted :
      (Real.log b - Real.log delta) * J ≤ 80082000 * L ^ 4 := by
    have hcoeffNonneg : 0 ≤ 80082 * L ^ 2 := by positivity
    exact (mul_le_mul_of_nonneg_right hcoeff hJ0).trans (by
      have := mul_le_mul_of_nonneg_left hJtop hcoeffNonneg
      nlinarith [sq_nonneg (L ^ 2)])
  dsimp [conreyHorizontalJensenFactorLogVariationMajorant, J, gap, b,
    delta] at *
  nlinarith [mul_nonneg (sq_nonneg L) (sq_nonneg L)]

/-- The three coarse geometric inequalities used when the exact horizontal
bound is collapsed to a polynomial in `L`. -/
theorem conreyHorizontalJensenCoarseGeometry
    {R L : ℝ} (hR0 : 0 ≤ R) (hRmax : R ≤ 6 / 5)
    (hL : 40000 ≤ L) :
    0 ≤ conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L ∧
      conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L ≤ 2 * L ∧
      conreyHorizontalJensenOuterRadius L /
          conreyHorizontalJensenRadiusGap R L ^ 2 ≤ 50 * L := by
  let w := conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L
  let outer := conreyHorizontalJensenOuterRadius L
  let gap := conreyHorizontalJensenRadiusGap R L
  have hLpos : 0 < L := by linarith
  have hlogLower := two_le_log_of_forty_thousand_le hL
  have hlogTop : Real.log L ≤ L := by
    have h := Real.log_le_sub_one_of_pos hLpos
    linarith
  have hquot0 : 0 ≤ R / L := div_nonneg hR0 hLpos.le
  have hquotTop : R / L ≤ 3 / 100000 := by
    rw [div_le_iff₀ hLpos]
    nlinarith
  have hw0 : 0 ≤ w := by
    dsimp [w, conreyHorizontalRightEdge, conreyHorizontalLeftEdge]
    nlinarith
  have hwTop : w ≤ 2 * L := by
    dsimp [w, conreyHorizontalRightEdge, conreyHorizontalLeftEdge]
    nlinarith
  have houterTop : outer ≤ 2 * L := by
    dsimp [outer, conreyHorizontalJensenOuterRadius,
      conreyHorizontalRightEdge]
    linarith
  have hgapLower : (1 / 5 : ℝ) < gap := by
    simpa [gap] using
      one_fifth_lt_conreyHorizontalJensenRadiusGap hR0 hRmax hL
  have hgapPos : 0 < gap := by linarith
  have hgapSqLower : (1 / 25 : ℝ) < gap ^ 2 := by
    nlinarith [sq_nonneg (gap - 1 / 5)]
  have honeGap : 1 ≤ 25 * gap ^ 2 := by linarith
  have htwoL : 2 * L ≤ 50 * L * gap ^ 2 := by
    have h := mul_le_mul_of_nonneg_left honeGap (by positivity : 0 ≤ 2 * L)
    nlinarith
  have houterScaled : outer ≤ 50 * L * gap ^ 2 :=
    houterTop.trans htwoL
  have hquotient : outer / gap ^ 2 ≤ 50 * L := by
    apply (div_le_iff₀ (sq_pos_of_pos hgapPos)).2
    nlinarith
  exact ⟨by simpa [w] using hw0, by simpa [w] using hwTop,
    by simpa [outer, gap] using hquotient⟩

/-- Purely algebraic collapse of the exact regular-plus-principal horizontal
bound.  The deliberately rounded constant leaves a visible safety margin. -/
theorem conreyHorizontalJensenExplicitHorizontalRhs_le_coarse
    {L w outer gap V J : ℝ} (hL : 40000 ≤ L)
    (hw0 : 0 ≤ w) (hwTop : w ≤ 2 * L)
    (hgapPos : 0 < gap) (houter0 : 0 ≤ outer)
    (houterGapTop : outer / gap ^ 2 ≤ 50 * L)
    (hVtop : V ≤ 81000000 * L ^ 4)
    (hJ0 : 0 ≤ J) (hJtop : J ≤ 1000 * L ^ 2) :
    (w ^ 2 / 2) * (128 * max V 1 * outer / gap ^ 2) +
        w * Real.pi * J ≤ 1100000000000 * L ^ 7 := by
  have hL0 : 0 ≤ L := by linarith
  have hLsqOne : 1 ≤ L ^ 2 := by
    nlinarith [sq_nonneg (L - 1)]
  have hLpow4One : 1 ≤ L ^ 4 := by
    nlinarith [sq_nonneg (L ^ 2 - 1)]
  have hmaxTop : max V 1 ≤ 81000001 * L ^ 4 := by
    apply max_le
    · nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 81000000)
        (sq_nonneg (L ^ 2))]
    · nlinarith
  have hmax0 : 0 ≤ max V 1 := (le_max_right V 1).trans' (by norm_num)
  have houterGap0 : 0 ≤ outer / gap ^ 2 :=
    div_nonneg houter0 (sq_nonneg gap)
  have hkernelTop :
      128 * max V 1 * outer / gap ^ 2 ≤
        518400006400 * L ^ 5 := by
    have hrewrite :
        128 * max V 1 * outer / gap ^ 2 =
          128 * (max V 1 * (outer / gap ^ 2)) := by ring
    rw [hrewrite]
    have hprod := mul_le_mul hmaxTop houterGapTop houterGap0
      (by positivity : 0 ≤ 81000001 * L ^ 4)
    have hscale := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 128)
    nlinarith [mul_nonneg (sq_nonneg (L ^ 2)) hL0]
  have hkernel0 : 0 ≤ 128 * max V 1 * outer / gap ^ 2 := by positivity
  have hwSquareTop : w ^ 2 / 2 ≤ 2 * L ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hwTop)
      (add_nonneg hw0 (by positivity : 0 ≤ 2 * L))]
  have hregular :
      (w ^ 2 / 2) * (128 * max V 1 * outer / gap ^ 2) ≤
        1036800012800 * L ^ 7 := by
    have hprod := mul_le_mul hwSquareTop hkernelTop hkernel0
      (by positivity : 0 ≤ 2 * L ^ 2)
    nlinarith [mul_nonneg (sq_nonneg L)
      (mul_nonneg (sq_nonneg (L ^ 2)) hL0)]
  have hprincipal : w * Real.pi * J ≤ 8000 * L ^ 3 := by
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    have hwpi := mul_le_mul hwTop hpi Real.pi_pos.le
      (by positivity : 0 ≤ 2 * L)
    have hwpi0 : 0 ≤ w * Real.pi := mul_nonneg hw0 Real.pi_pos.le
    have hprod := mul_le_mul hwpi hJtop hJ0
      (by positivity : 0 ≤ 2 * L * 4)
    nlinarith [sq_nonneg L]
  have hLthreeSeven : L ^ 3 ≤ L ^ 7 := by
    nlinarith [mul_nonneg (sq_nonneg (L ^ 2))
      (by nlinarith : 0 ≤ L ^ 3)]
  nlinarith

/-- At one selected height, the actual weighted logarithmic derivative on
the whole horizontal segment is bounded by a fixed seventh power of `L`.
The constants controlling the regular factor and the Jensen mass are kept
independent all the way to the endpoint. -/
theorem exists_conreyHorizontalJensenHeight_weightedLogDeriv_le_coarse :
    ∃ Creg Cmass : ℝ, 1 ≤ Creg ∧ 1 ≤ Cmass ∧
      ∀ {Y : ℕ} {R L U : ℝ}, 2 ≤ Y →
        (Y : ℝ) ≤ Real.exp L → 0 ≤ R → R ≤ 6 / 5 → 40000 ≤ L →
        conreyHorizontalRightEdge L + 1 ≤ U → U + 1 ≤ Real.exp L →
        Creg ≤ Real.exp L → Cmass ≤ Real.exp L →
        ∃ t ∈ Set.Icc U (U + 1),
          (∀ x ∈ Set.Icc (conreyHorizontalLeftEdge R L)
              (conreyHorizontalRightEdge L),
            conreyHorizontalJensenProduct Y R L
              ((x : ℂ) + I * (t : ℂ)) ≠ 0) ∧
          |∫ x in conreyHorizontalLeftEdge R L..conreyHorizontalRightEdge L,
              (x - conreyHorizontalLeftEdge R L) *
                (logDeriv (conreyHorizontalJensenProduct Y R L)
                  ((x : ℂ) + I * (t : ℂ))).im| ≤
            1100000000000 * L ^ 7 := by
  rcases exists_conreyHorizontalJensenHeight_weightedLogDeriv_le with
    ⟨Creg, hCreg, hhorizontal⟩
  rcases exists_conreyHorizontalJensenFactorZeroMassMajorant_bounds with
    ⟨Cmass, hCmass, hmass⟩
  refine ⟨Creg, Cmass, hCreg, hCmass, ?_⟩
  intro Y R L U hY hYtop hR0 hRmax hL hU hUtop hCregTop hCmassTop
  let J := conreyHorizontalJensenFactorZeroMassMajorant Cmass Y R L U
  let w := conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L
  let outer := conreyHorizontalJensenOuterRadius L
  let gap := conreyHorizontalJensenRadiusGap R L
  let V := conreyHorizontalJensenFactorLogVariationMajorant
    Creg Y R L U J
  have hmassBounds := hmass hY hYtop hR0 hRmax hL hU hUtop hCmassTop
  have hVtop : V ≤ 81000000 * L ^ 4 := by
    simpa [V, J] using
      conreyHorizontalJensenFactorLogVariationMajorant_le_eightyOneMillion
        hCreg hCregTop hCmass hCmassTop hY hYtop hR0 hRmax hL hU hUtop
  have hgeometry := conreyHorizontalJensenCoarseGeometry hR0 hRmax hL
  have hw0 : 0 ≤ w := by simpa [w] using hgeometry.1
  have hwTop : w ≤ 2 * L := by simpa [w] using hgeometry.2.1
  have houterGapTop : outer / gap ^ 2 ≤ 50 * L := by
    simpa [outer, gap] using hgeometry.2.2
  have houter0 : 0 ≤ outer := by
    have hlogLower := two_le_log_of_forty_thousand_le hL
    dsimp [outer, conreyHorizontalJensenOuterRadius,
      conreyHorizontalRightEdge]
    linarith
  have hgapPos : 0 < gap := by
    have h := one_fifth_lt_conreyHorizontalJensenRadiusGap hR0 hRmax hL
    simpa [gap] using (show 0 < conreyHorizontalJensenRadiusGap R L by
      linarith)
  have hJ0 : 0 ≤ J := by simpa [J] using hmassBounds.2.1
  have hJtop : J ≤ 1000 * L ^ 2 := by simpa [J] using hmassBounds.2.2
  have hrhs :
      (w ^ 2 / 2) * (128 * max V 1 * outer / gap ^ 2) +
          w * Real.pi * J ≤ 1100000000000 * L ^ 7 :=
    conreyHorizontalJensenExplicitHorizontalRhs_le_coarse hL hw0 hwTop
      hgapPos houter0 houterGapTop hVtop hJ0 hJtop
  rcases hhorizontal hY hYtop hR0 hRmax hL hU hUtop hmassBounds.1 with
    ⟨t, ht, hnonzero, hintegral⟩
  refine ⟨t, ht, hnonzero, hintegral.trans ?_⟩
  simpa [w, outer, gap, V, J] using hrhs

/-- The coarse seventh-power horizontal bound is negligible compared with
the `exp L / L` scale in Littlewood's contour identity. -/
theorem tendsto_conreyHorizontalJensen_coarse_div_exp_div_zero :
    Tendsto
      (fun L : ℝ =>
        (1100000000000 * L ^ 7) / (Real.exp L / L))
      atTop (nhds 0) := by
  have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (8 : ℝ) 1 (by norm_num : (0 : ℝ) < 1)
  have hnat :
      Tendsto (fun L : ℝ => L ^ 8 * Real.exp (-L)) atTop (nhds 0) := by
    convert hbase using 1
    funext L
    congr 1
    · exact (Real.rpow_natCast L 8).symm
    · congr 1
      ring
  have hscaled := hnat.const_mul (1100000000000 : ℝ)
  have hscaled0 :
      Tendsto
        (fun L : ℝ => 1100000000000 * (L ^ 8 * Real.exp (-L)))
        atTop (nhds 0) := by
    simpa only [mul_zero] using hscaled
  convert hscaled0 using 1
  funext L
  by_cases hL : L = 0
  · simp [hL]
  · rw [Real.exp_neg]
    field_simp [hL, Real.exp_ne_zero]

end HardyTheorem
