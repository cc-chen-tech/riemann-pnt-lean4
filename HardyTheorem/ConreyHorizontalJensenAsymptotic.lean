import HardyTheorem.ConreyHorizontalJensenIntegral

/-!
# Coarse asymptotics for Conrey's selected horizontal edge

This module deliberately keeps the growth constant used by the regular
factor separate from the one used by the Jensen mass estimate.  The bounds
are coarse fixed polynomials in `L = log T`; no new analytic cancellation is
introduced here.
-/

open Complex Set MeasureTheory MeromorphicOn

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

end HardyTheorem
