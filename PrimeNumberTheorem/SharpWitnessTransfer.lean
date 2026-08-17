import Mathlib

/-!
# Triangle-window energy transfer (the deterministic L2 → pointwise bridge)

Formalizes the quantitative transfer of
`docs/research/2026-08-10-actual-l2-tail-to-sharp-witness-transfer.md` on the
main-based line:

- the triangle probability weight `W_L(v) = (1/L)·max(1 − |v|/L, 0)` on the
  logarithmic interval `[-L, L]` with `∫ W ≤ 2`;
- the weighted energy `triangleEnergy L F = ∫ W_L·F²`;
- a lower bound `cMain²/2 − cRes² ≤ triangleEnergy L F` from a decomposition
  `F = Main + Residual` with `cMain² ≤ triangleEnergy L Main` (the sharp
  lower bound input) and `triangleEnergy L Residual ≤ cRes²` (the residual
  upper bound input) — via the elementary pointwise identity
  `(a+b)² ≥ a²/2 − b² = (a/√2 + √2·b)² − 2b²…` and monotone integration;
- the sup extraction: positive energy on the compact window gives a point
  `v ∈ [-L,L]` with `c/2 ≤ |F v|` (extreme value theorem + `∫W ≤ 2`).

The sharp lower bound `cMain` and the residual majorants (`cRes` built from
the dyadic Carlson capacity, the contour, the `s = 0` residue and the trivial
zeros) remain explicit inputs supplied by the half-isolated and cubic lines;
this module is their deterministic consumer.  All constants are explicit and
audit-clean.

Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PrimeNumberTheorem

open Filter
open MeasureTheory
open scoped Interval

noncomputable section

/-- Triangle probability weight on the logarithmic window `[-L, L]`. -/
def triangleWeight (L v : ℝ) : ℝ := (1 / L) * max (1 - |v| / L) 0

/-- Weighted energy of `F` on `[-L, L]` with the triangle weight. -/
def triangleEnergy (L : ℝ) (F : ℝ → ℝ) : ℝ :=
  ∫ v in (-L)..L, triangleWeight L v * (F v) ^ 2

/-- The triangle weight is nonnegative for positive window half-length. -/
theorem triangleWeight_nonneg {L v : ℝ} (hL : 0 < L) : 0 ≤ triangleWeight L v := by
  unfold triangleWeight
  exact mul_nonneg (div_nonneg zero_le_one hL.le) (le_max_right _ _)

/-- The triangle weight is pointwise bounded by `1/L`. -/
theorem triangleWeight_le_invL {L v : ℝ} (hL : 0 < L) : triangleWeight L v ≤ 1 / L := by
  unfold triangleWeight
  have hmax : max (1 - |v| / L) 0 ≤ 1 := by
    exact max_le (by nlinarith [div_nonneg (abs_nonneg v) hL.le]) zero_le_one
  simpa using mul_le_mul_of_nonneg_left hmax (div_nonneg zero_le_one hL.le)

/-- The triangle weight is continuous. -/
theorem continuous_triangleWeight (L : ℝ) : Continuous fun v : ℝ => triangleWeight L v := by
  unfold triangleWeight
  exact continuous_const.mul ((continuous_const.sub (continuous_abs.div_const L)).max continuous_const)

/-- The triangle window's total weight is at most `2` (the sharp unit-mass
normalization is irrelevant for the forcing constants). -/
theorem integral_triangleWeight_le_two {L : ℝ} (hL : 0 < L) :
    ∫ v in (-L)..L, triangleWeight L v ≤ 2 := by
  have hmono : ∫ v in (-L)..L, triangleWeight L v ≤ ∫ v in (-L)..L, (1 / L : ℝ) := by
    refine intervalIntegral.integral_mono_on (μ := volume) (by linarith : -L ≤ L) ?_ ?_ ?_
    · exact (show IntervalIntegrable (fun v => triangleWeight L v) volume (-L) L from
        (continuous_triangleWeight L).intervalIntegrable (-L) L)
    · exact (show IntervalIntegrable (fun _ : ℝ => (1 / L)) volume (-L) L from
        continuous_const.intervalIntegrable (-L) L)
    · intro v hv
      exact triangleWeight_le_invL hL
  have hconst : ∫ v in (-L)..L, (1 / L : ℝ) = 2 := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
    field_simp [hL.ne']
    ring
  rwa [hconst] at hmono

/-- Positive weighted energy with a uniform pointwise square bound forces the
energy to sit below `2` times the bound. -/
theorem triangleEnergy_le_two_mul_supSq {L : ℝ} {F : ℝ → ℝ} {S : ℝ}
    (hL : 0 < L)
    (hFcont : ContinuousOn F (Set.uIcc (-L) L))
    (hFle : ∀ v ∈ Set.Icc (-L) L, (F v) ^ 2 ≤ S) :
    triangleEnergy L F ≤ 2 * S := by
  unfold triangleEnergy
  have hstep1 : ∫ v in (-L)..L, triangleWeight L v * (F v) ^ 2 ≤
      ∫ v in (-L)..L, (1 / L) * (F v) ^ 2 := by
    refine intervalIntegral.integral_mono_on (μ := volume) (by linarith : -L ≤ L) ?_ ?_ ?_
    · exact (((continuous_triangleWeight L).continuousOn.mono (Set.subset_univ _)).mul (hFcont.pow 2)).intervalIntegrable
    · exact (((continuous_const : Continuous fun _ : ℝ => (1 / L)).continuousOn.mono (Set.subset_univ _)).mul (hFcont.pow 2)).intervalIntegrable
    · intro v hv
      exact mul_le_mul_of_nonneg_right (triangleWeight_le_invL hL) (sq_nonneg (F v))
  have hstep2 : ∫ v in (-L)..L, (1 / L) * (F v) ^ 2 ≤ ∫ v in (-L)..L, (1 / L) * S := by
    refine intervalIntegral.integral_mono_on (μ := volume) (by linarith : -L ≤ L) ?_ ?_ ?_
    · exact (((continuous_const : Continuous fun _ : ℝ => (1 / L)).continuousOn.mono (Set.subset_univ _)).mul (hFcont.pow 2)).intervalIntegrable
    · exact continuous_const.intervalIntegrable _ _
    · intro v hv
      exact mul_le_mul_of_nonneg_left (hFle v hv) (div_nonneg zero_le_one hL.le)
  have hconst : ∫ v in (-L)..L, (1 / L) * S = 2 * S := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp [smul_eq_mul]
    field_simp [hL.ne']
    ring
  calc
    triangleEnergy L F = ∫ v in (-L)..L, triangleWeight L v * (F v) ^ 2 := rfl
    _ ≤ ∫ v in (-L)..L, (1 / L) * (F v) ^ 2 := hstep1
    _ ≤ ∫ v in (-L)..L, (1 / L) * S := hstep2
    _ = 2 * S := hconst

/-- The sup extraction: positive weighted energy gives a point in the window
where `|F|` exceeds half the energy threshold. -/
theorem exists_pointwise_witness_of_triangleEnergy {L : ℝ} {F : ℝ → ℝ} {c : ℝ}
    (hL : 0 < L) (hc : 0 ≤ c)
    (hFcont : ContinuousOn F (Set.uIcc (-L) L))
    (hE : c ^ 2 ≤ triangleEnergy L F) :
    ∃ v ∈ Set.Icc (-L) L, c / 2 ≤ |F v| := by
  have hcompact : IsCompact (Set.Icc (-L) L : Set ℝ) := isCompact_Icc
  have hFcont' : ContinuousOn F (Set.Icc (-L) L) := by
    simpa [Set.uIcc_of_le (by linarith : -L ≤ L)] using hFcont
  rcases hcompact.exists_isMaxOn (⟨-L, by constructor <;> linarith⟩ : (Set.Icc (-L) L : Set ℝ).Nonempty)
      (continuous_abs.comp_continuousOn hFcont') with ⟨v, hv, hvmax⟩
  have hsup : ∀ x ∈ Set.Icc (-L) L, (F x) ^ 2 ≤ (F v) ^ 2 := by
    intro x hx
    have hle : |F x| ≤ |F v| := hvmax hx
    exact sq_le_sq.mpr hle
  have hE2 : c ^ 2 ≤ 2 * (F v) ^ 2 := by
    calc
      c ^ 2 ≤ triangleEnergy L F := hE
      _ ≤ 2 * (F v) ^ 2 := triangleEnergy_le_two_mul_supSq hL hFcont hsup
  have hsq : (c / Real.sqrt 2) ^ 2 ≤ (|F v|) ^ 2 := by
    have h2 : (c / Real.sqrt 2) ^ 2 = c ^ 2 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    have h3 : c ^ 2 / 2 ≤ (|F v|) ^ 2 := by
      have h4 : (F v) ^ 2 = (|F v|) ^ 2 := (sq_abs (F v)).symm
      nlinarith [hE2, h4]
    rwa [h2]
  have hsqrt : c / Real.sqrt 2 ≤ |F v| := by
    have hsq' : |c / Real.sqrt 2| ≤ |(|F v|)| := sq_le_sq.mp hsq
    simpa [abs_of_nonneg (div_nonneg hc (Real.sqrt_nonneg 2)), abs_of_nonneg (abs_nonneg (F v))]
      using hsq'
  have hdiv : c / 2 ≤ c / Real.sqrt 2 := by
    have hsq2 : Real.sqrt 2 ≤ 2 := by
      have h := (sq_le_sq.mp (show (Real.sqrt 2) ^ 2 ≤ (2 : ℝ) ^ 2 by norm_num [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]))
      simpa [abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))] using h
    by_cases hc0 : c = 0
    · simp [hc0]
    · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      exact (div_le_div_iff₀ (by norm_num : 0 < (2 : ℝ)) (Real.sqrt_pos.2 (by norm_num : 0 < (2 : ℝ)))).mpr
        (mul_le_mul_of_nonneg_left hsq2 hc)
  exact ⟨v, hv, le_trans hdiv hsqrt⟩

/-- The deterministic transfer: a decomposition `F = Main + Residual` with a
lower bound on the main energy and an upper bound on the residual energy
forces the total energy to exceed `cMain²/2 − cRes²`. -/
theorem triangleEnergy_transfer_lower {L : ℝ} {F Main Residual : ℝ → ℝ} {cMain cRes : ℝ}
    (hL : 0 < L) (hcMain : 0 ≤ cMain) (hcRes : 0 ≤ cRes)
    (hFcont : ContinuousOn F (Set.uIcc (-L) L))
    (hMainCont : ContinuousOn Main (Set.uIcc (-L) L))
    (hResCont : ContinuousOn Residual (Set.uIcc (-L) L))
    (hdec : ∀ v ∈ Set.Icc (-L) L, F v = Main v + Residual v)
    (hMain : cMain ^ 2 ≤ triangleEnergy L Main)
    (hRes : triangleEnergy L Residual ≤ cRes ^ 2) :
    cMain ^ 2 / 2 - cRes ^ 2 ≤ triangleEnergy L F := by
  have hpoint : ∀ v ∈ Set.Icc (-L) L,
      (Main v) ^ 2 / 2 - (Residual v) ^ 2 ≤ (F v) ^ 2 := by
    intro v hv
    have hsq : 0 ≤ (Main v + 2 * Residual v) ^ 2 := sq_nonneg _
    rw [hdec v hv]
    nlinarith [hsq]
  have hw : ∀ v ∈ Set.Icc (-L) L,
      triangleWeight L v * ((Main v) ^ 2 / 2 - (Residual v) ^ 2) ≤
        triangleWeight L v * (F v) ^ 2 := by
    intro v hv
    exact mul_le_mul_of_nonneg_left (hpoint v hv) (triangleWeight_nonneg hL)
  have hint : ∫ v in (-L)..L, triangleWeight L v * ((Main v) ^ 2 / 2 - (Residual v) ^ 2) ≤
      triangleEnergy L F := by
    unfold triangleEnergy
    refine intervalIntegral.integral_mono_on (μ := volume) (by linarith : -L ≤ L) ?_ ?_ hw
    · exact (((continuous_triangleWeight L).continuousOn.mono (Set.subset_univ _)).mul
        (((hMainCont.pow 2).div_const 2).sub (hResCont.pow 2))).intervalIntegrable
    · exact (((continuous_triangleWeight L).continuousOn.mono (Set.subset_univ _)).mul (hFcont.pow 2)).intervalIntegrable
  have hdec_int : ∫ v in (-L)..L, triangleWeight L v * ((Main v) ^ 2 / 2 - (Residual v) ^ 2) =
      (∫ v in (-L)..L, triangleWeight L v * ((Main v) ^ 2 / 2)) -
        ∫ v in (-L)..L, triangleWeight L v * (Residual v) ^ 2 := by
    have hf : IntervalIntegrable (fun v => triangleWeight L v * ((Main v) ^ 2 / 2)) volume (-L) L :=
      (((continuous_triangleWeight L).continuousOn.mono (Set.subset_univ _)).mul ((hMainCont.pow 2).div_const 2)).intervalIntegrable
    have hg : IntervalIntegrable (fun v => triangleWeight L v * (Residual v) ^ 2) volume (-L) L :=
      (((continuous_triangleWeight L).continuousOn.mono (Set.subset_univ _)).mul (hResCont.pow 2)).intervalIntegrable
    calc
      ∫ v in (-L)..L, triangleWeight L v * ((Main v) ^ 2 / 2 - (Residual v) ^ 2)
          = ∫ v in (-L)..L,
              (triangleWeight L v * ((Main v) ^ 2 / 2) - triangleWeight L v * (Residual v) ^ 2) := by
        apply intervalIntegral.integral_congr
        intro v hv
        ring
      _ = (∫ v in (-L)..L, triangleWeight L v * ((Main v) ^ 2 / 2)) -
          ∫ v in (-L)..L, triangleWeight L v * (Residual v) ^ 2 :=
        intervalIntegral.integral_sub hf hg
  have hhalf : ∫ v in (-L)..L, triangleWeight L v * ((Main v) ^ 2 / 2) =
      (1 / 2 : ℝ) * triangleEnergy L Main := by
    unfold triangleEnergy
    rw [← intervalIntegral.integral_const_mul (1 / 2 : ℝ) (fun v => triangleWeight L v * (Main v) ^ 2)]
    apply intervalIntegral.integral_congr
    intro v hv
    ring
  have hbound : cMain ^ 2 / 2 - cRes ^ 2 ≤
      (1 / 2 : ℝ) * triangleEnergy L Main - triangleEnergy L Residual := by
    nlinarith [hMain, hRes]
  have hfin : (1 / 2 : ℝ) * triangleEnergy L Main - triangleEnergy L Residual ≤
      ∫ v in (-L)..L, triangleWeight L v * ((Main v) ^ 2 / 2 - (Residual v) ^ 2) := by
    have hrhs : ∫ v in (-L)..L, triangleWeight L v * ((Main v) ^ 2 / 2 - (Residual v) ^ 2) =
        (1 / 2 : ℝ) * triangleEnergy L Main - triangleEnergy L Residual := by
      rw [hdec_int, hhalf]
      rfl
    rw [hrhs]
  exact hbound.trans (hfin.trans hint)


/-- The elementary upper transfer: for `F = Main + Residual` on the window,
`energy(F) ≤ 2·energy(Main) + 2·energy(Residual)` (pointwise
`(a+b)² ≤ 2a² + 2b²`, no Minkowski). -/
theorem triangleEnergy_le_two_add_two {L : ℝ} {F Main Residual : ℝ → ℝ}
    (hL : 0 < L)
    (hFcont : ContinuousOn F (Set.uIcc (-L) L))
    (hMainCont : ContinuousOn Main (Set.uIcc (-L) L))
    (hResCont : ContinuousOn Residual (Set.uIcc (-L) L))
    (hdec : ∀ v ∈ Set.Icc (-L) L, F v = Main v + Residual v) :
    triangleEnergy L F ≤ 2 * triangleEnergy L Main + 2 * triangleEnergy L Residual := by
  unfold triangleEnergy
  have hpt : ∀ v ∈ Set.Icc (-L) L, (F v) ^ 2 ≤ 2 * (Main v) ^ 2 + 2 * (Residual v) ^ 2 := by
    intro v hv
    rw [hdec v hv]
    nlinarith [sq_nonneg (Main v - Residual v)]
  have hw : ∀ v ∈ Set.Icc (-L) L,
      triangleWeight L v * (F v) ^ 2 ≤
        triangleWeight L v * (2 * (Main v) ^ 2 + 2 * (Residual v) ^ 2) := by
    intro v hv
    exact mul_le_mul_of_nonneg_left (hpt v hv) (triangleWeight_nonneg hL)
  have hW : ContinuousOn (fun v => triangleWeight L v) (Set.uIcc (-L) L) :=
    (continuous_triangleWeight L).continuousOn.mono (Set.subset_univ _)
  have hf : IntervalIntegrable (fun v => triangleWeight L v * (F v) ^ 2) volume (-L) L :=
    (show ContinuousOn (fun v => triangleWeight L v * (F v) ^ 2) (Set.uIcc (-L) L) from
      hW.mul (hFcont.pow 2)).intervalIntegrable
  have hlinI : IntervalIntegrable (fun v => triangleWeight L v * (2 * (Main v) ^ 2 + 2 * (Residual v) ^ 2)) volume (-L) L :=
    (show ContinuousOn (fun v => triangleWeight L v * (2 * (Main v) ^ 2 + 2 * (Residual v) ^ 2)) (Set.uIcc (-L) L) from
      hW.mul (show ContinuousOn (fun v => 2 * (Main v) ^ 2 + 2 * (Residual v) ^ 2) (Set.uIcc (-L) L) from by
        fun_prop)).intervalIntegrable
  have hint : ∫ v in (-L)..L, triangleWeight L v * (F v) ^ 2 ≤
      ∫ v in (-L)..L, triangleWeight L v * (2 * (Main v) ^ 2 + 2 * (Residual v) ^ 2) :=
    intervalIntegral.integral_mono_on (μ := volume) (by linarith : -L ≤ L) hf hlinI hw
  have hlin : ∫ v in (-L)..L, triangleWeight L v * (2 * (Main v) ^ 2 + 2 * (Residual v) ^ 2) =
      2 * triangleEnergy L Main + 2 * triangleEnergy L Residual := by
    unfold triangleEnergy
    have hcong : ∫ v in (-L)..L, triangleWeight L v * (2 * (Main v) ^ 2 + 2 * (Residual v) ^ 2) =
        ∫ v in (-L)..L,
          (triangleWeight L v * (2 * (Main v) ^ 2) + triangleWeight L v * (2 * (Residual v) ^ 2)) := by
      apply intervalIntegral.integral_congr
      intro v hv
      ring
    rw [hcong, intervalIntegral.integral_add
      (show IntervalIntegrable (fun v => triangleWeight L v * (2 * (Main v) ^ 2)) volume (-L) L from
        (show ContinuousOn (fun v => triangleWeight L v * (2 * (Main v) ^ 2)) (Set.uIcc (-L) L) from
          hW.mul (show ContinuousOn (fun v => 2 * (Main v) ^ 2) (Set.uIcc (-L) L) from by
            fun_prop)).intervalIntegrable)
      (show IntervalIntegrable (fun v => triangleWeight L v * (2 * (Residual v) ^ 2)) volume (-L) L from
        (show ContinuousOn (fun v => triangleWeight L v * (2 * (Residual v) ^ 2)) (Set.uIcc (-L) L) from
          hW.mul (show ContinuousOn (fun v => 2 * (Residual v) ^ 2) (Set.uIcc (-L) L) from by
            fun_prop)).intervalIntegrable)]
    have h1 : ∫ v in (-L)..L, triangleWeight L v * (2 * (Main v) ^ 2) =
        2 * ∫ v in (-L)..L, triangleWeight L v * (Main v) ^ 2 := by
      rw [← intervalIntegral.integral_const_mul 2 (fun v => triangleWeight L v * (Main v) ^ 2)]
      apply intervalIntegral.integral_congr
      intro v hv
      ring
    have h2 : ∫ v in (-L)..L, triangleWeight L v * (2 * (Residual v) ^ 2) =
        2 * ∫ v in (-L)..L, triangleWeight L v * (Residual v) ^ 2 := by
      rw [← intervalIntegral.integral_const_mul 2 (fun v => triangleWeight L v * (Residual v) ^ 2)]
      apply intervalIntegral.integral_congr
      intro v hv
      ring
    rw [h1, h2]
  exact hint.trans_eq hlin

/-- The count forcing: an energy lower bound for `Main` (the sharp input), an
energy upper bound `cap·M` for the same package (the capacity input) and a
residual upper bound force the count `M` from below — the contrapositive
form of the tail majorant.  All constants are explicit. -/
theorem forcingLowerCount_of_energyTransfer
    {L cMain cRes cap M : ℝ} {F Main Residual : ℝ → ℝ}
    (hL : 0 < L) (hcMain : 0 ≤ cMain) (hcRes : 0 ≤ cRes) (hcap_pos : 0 < cap)
    (hFcont : ContinuousOn F (Set.uIcc (-L) L))
    (hMainCont : ContinuousOn Main (Set.uIcc (-L) L))
    (hResCont : ContinuousOn Residual (Set.uIcc (-L) L))
    (hdec : ∀ v ∈ Set.Icc (-L) L, F v = Main v + Residual v)
    (hMain_lower : cMain ^ 2 ≤ triangleEnergy L Main)
    (hRes_upper : triangleEnergy L Residual ≤ cRes ^ 2)
    (hcap : triangleEnergy L Main ≤ cap * M) :
    (cMain ^ 2 / 4 - 3 * cRes ^ 2 / 2) / cap ≤ M := by
  have htrans : cMain ^ 2 / 2 - cRes ^ 2 ≤ triangleEnergy L F :=
    triangleEnergy_transfer_lower hL hcMain hcRes hFcont hMainCont hResCont hdec hMain_lower hRes_upper
  have hupperF : triangleEnergy L F ≤ 2 * triangleEnergy L Main + 2 * triangleEnergy L Residual :=
    triangleEnergy_le_two_add_two hL hFcont hMainCont hResCont hdec
  have h1 : cMain ^ 2 / 2 - cRes ^ 2 ≤ 2 * triangleEnergy L Main + 2 * cRes ^ 2 := by
    exact htrans.trans (hupperF.trans (by nlinarith [hRes_upper]))
  have h2 : cMain ^ 2 / 4 - 3 * cRes ^ 2 / 2 ≤ triangleEnergy L Main := by
    nlinarith [h1]
  have h3 : cMain ^ 2 / 4 - 3 * cRes ^ 2 / 2 ≤ cap * M := le_trans h2 hcap
  exact (div_le_iff₀' hcap_pos).mpr h3


/-- The clean count forcing: when the residual energy is dominated by the
seed energy (`6·cRes² ≤ cMain²`), the forced count takes the clean form
`cMain²/(8·cap) ≤ M` — the residual only affects the constant, not the
exponent (under the domination `12·cRes² ≤ cMain²`). -/
theorem forcingLowerCount_clean_of_residualDominated
    {L cMain cRes cap M : ℝ} {F Main Residual : ℝ → ℝ}
    (hL : 0 < L) (hcMain : 0 ≤ cMain) (hcRes : 0 ≤ cRes) (hcap_pos : 0 < cap)
    (hFcont : ContinuousOn F (Set.uIcc (-L) L))
    (hMainCont : ContinuousOn Main (Set.uIcc (-L) L))
    (hResCont : ContinuousOn Residual (Set.uIcc (-L) L))
    (hdec : ∀ v ∈ Set.Icc (-L) L, F v = Main v + Residual v)
    (hMain_lower : cMain ^ 2 ≤ triangleEnergy L Main)
    (hRes_upper : triangleEnergy L Residual ≤ cRes ^ 2)
    (hcap : triangleEnergy L Main ≤ cap * M)
    (hdom : 12 * cRes ^ 2 ≤ cMain ^ 2) :
    cMain ^ 2 / (8 * cap) ≤ M := by
  have h := forcingLowerCount_of_energyTransfer
    hL hcMain hcRes hcap_pos hFcont hMainCont hResCont hdec hMain_lower hRes_upper hcap
  have hle : cMain ^ 2 / (8 * cap) ≤ (cMain ^ 2 / 4 - 3 * cRes ^ 2 / 2) / cap := by
    have hnum : cMain ^ 2 / 8 ≤ cMain ^ 2 / 4 - 3 * cRes ^ 2 / 2 := by
      nlinarith [hdom]
    have hdiv : cMain ^ 2 / (8 * cap) = (cMain ^ 2 / 8) / cap := by
      field_simp [hcap_pos.ne']
    rw [hdiv]
    exact div_le_div_of_nonneg_right hnum hcap_pos.le
  exact hle.trans h

end

end PrimeNumberTheorem
