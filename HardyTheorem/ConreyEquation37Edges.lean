import HardyTheorem.ConreyHorizontalJensenAsymptotic
import HardyTheorem.ConreyRightArgument

/-!
# The selected non-left edges in Conrey's equation (37)

This module simultaneously selects a bottom and a top horizontal edge for
the actual mollified product and combines their weighted logarithmic-
derivative bounds with the global moving-right-edge logarithmic and argument
bounds.  It deliberately stops before applying Littlewood's lemma: the
current exact rectangle theorem requires a zero-free left edge, whereas the
classical equation-(37) argument must permit zeros on that edge by a limiting
convention.
-/

open Complex Set
open scoped Interval

namespace HardyTheorem

/-- At the explicit large-`L` threshold, the two unit windows used for the
bottom and top selected heights are disjoint and lie below `exp L`. -/
theorem conreyHorizontalRightEdge_add_three_lt_exp
    {L : ℝ} (hL : 40000 ≤ L) :
    conreyHorizontalRightEdge L + 3 < Real.exp L := by
  have hlog := log_le_div_hundred_of_ge_forty_thousand hL
  have hlinear : conreyHorizontalRightEdge L + 3 < L + 1 := by
    dsimp [conreyHorizontalRightEdge]
    linarith
  exact hlinear.trans_le (Real.add_one_le_exp L)

/-- The weighted horizontal logarithmic-derivative term occurring in
Littlewood's rectangle identity. -/
noncomputable def conreyEquation37HorizontalTerm
    (Y : ℕ) (R L t : ℝ) : ℝ :=
  ∫ x in conreyHorizontalLeftEdge R L..conreyHorizontalRightEdge L,
    (x - conreyHorizontalLeftEdge R L) *
      (logDeriv (conreyHorizontalJensenProduct Y R L)
        ((x : ℂ) + I * (t : ℂ))).im

/-- The right-vertical logarithmic term, before the minus sign in
Littlewood's identity. -/
noncomputable def conreyEquation37RightLogTerm
    (Y : ℕ) (R L t0 t1 : ℝ) : ℝ :=
  ∫ t in t0..t1,
    Real.log ‖conreyExplicitRightVerticalProduct Y
      (conreyHorizontalLeftEdge R L) L t‖

/-- The right-vertical argument-variation integral. -/
noncomputable def conreyEquation37RightArgumentTerm
    (Y : ℕ) (R L t0 t1 : ℝ) : ℝ :=
  ∫ t in t0..t1,
    (logDeriv
      (conreyExplicitRightVerticalFunction Y
        (conreyHorizontalLeftEdge R L) L)
      (((conreyHorizontalRightEdge L : ℝ) : ℂ) + I * t)).re

/-- All terms in the exact Littlewood identity except its left-vertical
`log ‖F‖` integral. -/
noncomputable def conreyEquation37BoundaryRemainder
    (Y : ℕ) (R L t0 t1 : ℝ) : ℝ :=
  -conreyEquation37RightLogTerm Y R L t0 t1 +
    conreyEquation37HorizontalTerm Y R L t0 -
    conreyEquation37HorizontalTerm Y R L t1 +
    (conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L) *
      conreyEquation37RightArgumentTerm Y R L t0 t1

/-- Two admissible horizontal heights can be selected simultaneously, and
the complete non-left boundary remainder is bounded at the `exp L / L`
scale plus the already proved polynomial horizontal error.

The constants `Creg` and `Cmass` are the fixed absolute constants produced by
the Jensen/Borel--Caratheodory construction.  Their absorption into `exp L`
is intentionally kept explicit here. -/
theorem exists_conreyEquation37SelectedHeights_boundaryRemainder_le :
    ∃ Creg Cmass : ℝ, 1 ≤ Creg ∧ 1 ≤ Cmass ∧
      ∀ {Y : ℕ} {R L : ℝ}, 2 ≤ Y →
        (Y : ℝ) ≤ Real.exp L → 0 ≤ R → R ≤ 6 / 5 → 40000 ≤ L →
        Creg ≤ Real.exp L → Cmass ≤ Real.exp L →
        ∃ t0 t1 : ℝ,
          t0 ∈ Set.Icc (conreyHorizontalRightEdge L + 1)
              (conreyHorizontalRightEdge L + 2) ∧
          t1 ∈ Set.Icc (Real.exp L - 1) (Real.exp L) ∧
          t0 < t1 ∧
          (∀ x ∈ Set.Icc (conreyHorizontalLeftEdge R L)
              (conreyHorizontalRightEdge L),
            conreyHorizontalJensenProduct Y R L
              ((x : ℂ) + I * (t0 : ℂ)) ≠ 0) ∧
          (∀ x ∈ Set.Icc (conreyHorizontalLeftEdge R L)
              (conreyHorizontalRightEdge L),
            conreyHorizontalJensenProduct Y R L
              ((x : ℂ) + I * (t1 : ℂ)) ≠ 0) ∧
          |conreyEquation37HorizontalTerm Y R L t0| ≤
              1100000000000 * L ^ 7 ∧
          |conreyEquation37HorizontalTerm Y R L t1| ≤
              1100000000000 * L ^ 7 ∧
          |conreyEquation37BoundaryRemainder Y R L t0 t1| ≤
            507 * Real.exp L / L + 2200000000000 * L ^ 7 +
              (conreyHorizontalRightEdge L -
                conreyHorizontalLeftEdge R L) * Real.pi := by
  rcases exists_conreyHorizontalJensenHeight_weightedLogDeriv_le_coarse with
    ⟨Creg, Cmass, hCreg, hCmass, hselect⟩
  refine ⟨Creg, Cmass, hCreg, hCmass, ?_⟩
  intro Y R L hY hYtop hR0 hRmax hL hCregTop hCmassTop
  have hwindow := conreyHorizontalRightEdge_add_three_lt_exp hL
  have hbottomTop : conreyHorizontalRightEdge L + 2 ≤ Real.exp L := by
    linarith
  have htopBottom : conreyHorizontalRightEdge L + 1 ≤ Real.exp L - 1 := by
    linarith
  rcases hselect hY hYtop hR0 hRmax hL
      (show conreyHorizontalRightEdge L + 1 ≤
        conreyHorizontalRightEdge L + 1 by rfl)
      (by linarith) hCregTop hCmassTop with
    ⟨t0, ht0, hnonzero0, hhorizontal0⟩
  rcases hselect hY hYtop hR0 hRmax hL htopBottom
      (by linarith) hCregTop hCmassTop with
    ⟨t1, ht1, hnonzero1, hhorizontal1⟩
  have ht0' : t0 ∈ Set.Icc (conreyHorizontalRightEdge L + 1)
      (conreyHorizontalRightEdge L + 2) := by
    simpa only [add_assoc, one_add_one_eq_two] using ht0
  have ht1' : t1 ∈ Set.Icc (Real.exp L - 1) (Real.exp L) := by
    simpa only [sub_add_cancel] using ht1
  have ht01 : t0 < t1 := by
    linarith [ht0'.2, ht1'.1, hwindow]
  have ht0one : (1 : ℝ) ≤ t0 := by
    have hlog := two_le_log_of_forty_thousand_le hL
    dsimp [conreyHorizontalRightEdge] at ht0' ⊢
    linarith [ht0'.1]
  have ht1exp : t1 ≤ Real.exp L := ht1'.2
  have hsigma0 : conreyHorizontalLeftEdge R L ≤ 1 / 2 := by
    have hLpos : 0 < L := by linarith
    dsimp [conreyHorizontalLeftEdge]
    exact sub_le_self _ (div_nonneg hR0 hLpos.le)
  have hrightLog :
      |conreyEquation37RightLogTerm Y R L t0 t1| ≤
        507 * Real.exp L / L := by
    let q : ℝ → ℝ := fun t =>
      |Real.log ‖conreyExplicitRightVerticalProduct Y
        (conreyHorizontalLeftEdge R L) L t‖|
    have hfullInt :=
      intervalIntegrable_abs_log_norm_conreyExplicitRightVerticalProduct_global
        hY hsigma0 hL
    have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict
        (Set.Ioc 1 (Real.exp L))] q :=
      Filter.Eventually.of_forall (fun t => abs_nonneg _)
    have hrestrict : (∫ t in t0..t1, q t) ≤
        ∫ t in 1..Real.exp L, q t :=
      intervalIntegral.integral_mono_interval ht0one ht01.le ht1exp
        hnonneg hfullInt
    have habs :
        |∫ t in t0..t1,
          Real.log ‖conreyExplicitRightVerticalProduct Y
            (conreyHorizontalLeftEdge R L) L t‖| ≤
          ∫ t in t0..t1, q t := by
      exact intervalIntegral.abs_integral_le_integral_abs ht01.le
    calc
      |conreyEquation37RightLogTerm Y R L t0 t1| ≤
          ∫ t in t0..t1, q t := by
            simpa only [conreyEquation37RightLogTerm, q] using habs
      _ ≤ ∫ t in 1..Real.exp L, q t := hrestrict
      _ ≤ 507 * Real.exp L / L := by
        simpa only [q] using
          integral_abs_log_norm_conreyExplicitRightVerticalProduct_global_le
            hY hsigma0 hL
  have hrightArgument :
      |conreyEquation37RightArgumentTerm Y R L t0 t1| ≤ Real.pi := by
    simpa only [conreyEquation37RightArgumentTerm,
      conreyHorizontalRightEdge] using
      abs_intervalIntegral_re_logDeriv_conreyExplicitRightVertical_le_pi
        hY hsigma0 hL ht0one ht01.le ht1exp
  have hwidth0 :
      0 ≤ conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L :=
    (conreyHorizontalJensenCoarseGeometry hR0 hRmax hL).1
  have hwidthArgument :
      |(conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L) *
          conreyEquation37RightArgumentTerm Y R L t0 t1| ≤
        (conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L) *
          Real.pi := by
    rw [abs_mul, abs_of_nonneg hwidth0]
    exact mul_le_mul_of_nonneg_left hrightArgument hwidth0
  have hhorizontal0' :
      |conreyEquation37HorizontalTerm Y R L t0| ≤
        1100000000000 * L ^ 7 := by
    simpa only [conreyEquation37HorizontalTerm] using hhorizontal0
  have hhorizontal1' :
      |conreyEquation37HorizontalTerm Y R L t1| ≤
        1100000000000 * L ^ 7 := by
    simpa only [conreyEquation37HorizontalTerm] using hhorizontal1
  have htriangle :
      |conreyEquation37BoundaryRemainder Y R L t0 t1| ≤
        |conreyEquation37RightLogTerm Y R L t0 t1| +
        |conreyEquation37HorizontalTerm Y R L t0| +
        |conreyEquation37HorizontalTerm Y R L t1| +
        |(conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L) *
          conreyEquation37RightArgumentTerm Y R L t0 t1| := by
    let rlog := conreyEquation37RightLogTerm Y R L t0 t1
    let h0 := conreyEquation37HorizontalTerm Y R L t0
    let h1 := conreyEquation37HorizontalTerm Y R L t1
    let wa := (conreyHorizontalRightEdge L -
      conreyHorizontalLeftEdge R L) *
        conreyEquation37RightArgumentTerm Y R L t0 t1
    have houter := abs_add_le (-rlog + h0 - h1) wa
    have hmiddle := abs_sub (-rlog + h0) h1
    have hinner := abs_add_le (-rlog) h0
    rw [abs_neg] at hinner
    dsimp only [conreyEquation37BoundaryRemainder, rlog, h0, h1, wa]
    linarith
  have hremainder :
      |conreyEquation37BoundaryRemainder Y R L t0 t1| ≤
        507 * Real.exp L / L + 2200000000000 * L ^ 7 +
          (conreyHorizontalRightEdge L -
            conreyHorizontalLeftEdge R L) * Real.pi := by
    calc
      |conreyEquation37BoundaryRemainder Y R L t0 t1| ≤
          |conreyEquation37RightLogTerm Y R L t0 t1| +
          |conreyEquation37HorizontalTerm Y R L t0| +
          |conreyEquation37HorizontalTerm Y R L t1| +
          |(conreyHorizontalRightEdge L - conreyHorizontalLeftEdge R L) *
            conreyEquation37RightArgumentTerm Y R L t0 t1| := htriangle
      _ ≤ 507 * Real.exp L / L + 2200000000000 * L ^ 7 +
          (conreyHorizontalRightEdge L -
            conreyHorizontalLeftEdge R L) * Real.pi := by
        linarith
  refine ⟨t0, t1, ht0', ht1', ht01, hnonzero0, hnonzero1, ?_, ?_,
    hremainder⟩
  · exact hhorizontal0'
  · exact hhorizontal1'

end HardyTheorem
