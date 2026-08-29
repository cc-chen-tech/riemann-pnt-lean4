import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# An explicit quantitative plateau for the critical AFE

Unlike a `ContDiffBump` obtained through the nonconstructive
`someContDiffBumpBase`, this plateau is a product of two translates of the
fixed function `Real.smoothTransition`.  Its transition widths are exactly
one, so its derivative bounds can be chosen independently of the endpoints.
-/

noncomputable section

open Set

namespace HardyTheorem
namespace AFE

/-- A smooth plateau equal to one on `[x,N]`, with unit-width transition
strips `[x-1,x]` and `[N,N+1]`. -/
noncomputable def explicitIntervalPlateau (x N u : ℝ) : ℝ :=
  Real.smoothTransition (u - (x - 1)) *
    Real.smoothTransition ((N + 1) - u)

/-- The exact first derivative of the explicit plateau. -/
noncomputable def explicitIntervalPlateauDeriv (x N u : ℝ) : ℝ :=
  deriv Real.smoothTransition (u - (x - 1)) *
      Real.smoothTransition ((N + 1) - u) -
    Real.smoothTransition (u - (x - 1)) *
      deriv Real.smoothTransition ((N + 1) - u)

/-- The exact second derivative of the explicit plateau. -/
noncomputable def explicitIntervalPlateauSecondDeriv (x N u : ℝ) : ℝ :=
  deriv (deriv Real.smoothTransition) (u - (x - 1)) *
      Real.smoothTransition ((N + 1) - u) -
    2 * deriv Real.smoothTransition (u - (x - 1)) *
      deriv Real.smoothTransition ((N + 1) - u) +
    Real.smoothTransition (u - (x - 1)) *
      deriv (deriv Real.smoothTransition) ((N + 1) - u)

theorem explicitIntervalPlateau_contDiff (x N : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (explicitIntervalPlateau x N) := by
  exact (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

theorem explicitIntervalPlateau_hasDerivAt (x N u : ℝ) :
    HasDerivAt (explicitIntervalPlateau x N)
      (explicitIntervalPlateauDeriv x N u) u := by
  have hdiff : Differentiable ℝ Real.smoothTransition :=
    (@Real.smoothTransition.contDiff 1).differentiable one_ne_zero
  have hL := (hdiff (u - (x - 1))).hasDerivAt.comp u
    (hasDerivAt_id u |>.sub_const (x - 1))
  have hR := (hdiff ((N + 1) - u)).hasDerivAt.comp u
    (hasDerivAt_const u (N + 1) |>.sub (hasDerivAt_id u))
  convert! hL.mul hR using 1
  simp [explicitIntervalPlateauDeriv, Function.comp_apply]
  ring

theorem explicitIntervalPlateauDeriv_hasDerivAt (x N u : ℝ) :
    HasDerivAt (explicitIntervalPlateauDeriv x N)
      (explicitIntervalPlateauSecondDeriv x N u) u := by
  have hdiff : Differentiable ℝ Real.smoothTransition :=
    (@Real.smoothTransition.contDiff 1).differentiable one_ne_zero
  have hdiff' : Differentiable ℝ (deriv Real.smoothTransition) :=
    (@Real.smoothTransition.contDiff 2).differentiable_deriv_two
  have hL := (hdiff (u - (x - 1))).hasDerivAt.comp u
    (hasDerivAt_id u |>.sub_const (x - 1))
  have hR := (hdiff ((N + 1) - u)).hasDerivAt.comp u
    (hasDerivAt_const u (N + 1) |>.sub (hasDerivAt_id u))
  have hL' := (hdiff' (u - (x - 1))).hasDerivAt.comp u
    (hasDerivAt_id u |>.sub_const (x - 1))
  have hR' := (hdiff' ((N + 1) - u)).hasDerivAt.comp u
    (hasDerivAt_const u (N + 1) |>.sub (hasDerivAt_id u))
  convert! (hL'.mul hR).sub (hL.mul hR') using 1
  simp [explicitIntervalPlateauSecondDeriv, Function.comp_apply]
  ring

theorem explicitIntervalPlateau_eq_one {x N u : ℝ} (hu : u ∈ Icc x N) :
    explicitIntervalPlateau x N u = 1 := by
  rw [explicitIntervalPlateau,
    Real.smoothTransition.one_of_one_le (by linarith [hu.1]),
    Real.smoothTransition.one_of_one_le (by linarith [hu.2]), one_mul]

theorem explicitIntervalPlateau_eq_zero_of_le {x N u : ℝ}
    (hu : u ≤ x - 1) :
    explicitIntervalPlateau x N u = 0 := by
  rw [explicitIntervalPlateau,
    Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem explicitIntervalPlateau_eq_zero_of_ge {x N u : ℝ}
    (hu : N + 1 ≤ u) :
    explicitIntervalPlateau x N u = 0 := by
  have hR : Real.smoothTransition ((N + 1) - u) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  rw [explicitIntervalPlateau, hR, mul_zero]

theorem explicitIntervalPlateau_nonneg (x N u : ℝ) :
    0 ≤ explicitIntervalPlateau x N u := by
  exact mul_nonneg (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.nonneg _)

theorem explicitIntervalPlateau_le_one (x N u : ℝ) :
    explicitIntervalPlateau x N u ≤ 1 := by
  have hL0 := Real.smoothTransition.nonneg (u - (x - 1))
  have hL1 := Real.smoothTransition.le_one (u - (x - 1))
  have hR0 := Real.smoothTransition.nonneg ((N + 1) - u)
  have hR1 := Real.smoothTransition.le_one ((N + 1) - u)
  rw [explicitIntervalPlateau]
  nlinarith

theorem explicitIntervalPlateau_hasCompactSupport (x N : ℝ) :
    HasCompactSupport (explicitIntervalPlateau x N) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (x - 1) (N + 1)))
  intro u hu
  rw [mem_Icc, not_and_or] at hu
  rcases hu with hu | hu
  · exact explicitIntervalPlateau_eq_zero_of_le (le_of_lt (lt_of_not_ge hu))
  · exact explicitIntervalPlateau_eq_zero_of_ge (le_of_lt (lt_of_not_ge hu))

theorem deriv_smoothTransition_eq_zero_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    deriv Real.smoothTransition u = 0 := by
  have hmin : IsLocalMin Real.smoothTransition u := by
    filter_upwards [] with y
    rw [Real.smoothTransition.zero_of_nonpos hu]
    exact Real.smoothTransition.nonneg y
  exact hmin.deriv_eq_zero

theorem deriv_smoothTransition_eq_zero_of_one_le {u : ℝ} (hu : 1 ≤ u) :
    deriv Real.smoothTransition u = 0 := by
  have hmax : IsLocalMax Real.smoothTransition u := by
    filter_upwards [] with y
    rw [Real.smoothTransition.one_of_one_le hu]
    exact Real.smoothTransition.le_one y
  exact hmax.deriv_eq_zero

theorem secondDeriv_smoothTransition_eq_zero_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    deriv (deriv Real.smoothTransition) u = 0 := by
  have hmin : IsLocalMin (deriv Real.smoothTransition) u := by
    filter_upwards [] with y
    rw [deriv_smoothTransition_eq_zero_of_nonpos hu]
    exact Real.smoothTransition.monotone.deriv_nonneg
  exact hmin.deriv_eq_zero

theorem secondDeriv_smoothTransition_eq_zero_of_one_le {u : ℝ} (hu : 1 ≤ u) :
    deriv (deriv Real.smoothTransition) u = 0 := by
  have hmin : IsLocalMin (deriv Real.smoothTransition) u := by
    filter_upwards [] with y
    rw [deriv_smoothTransition_eq_zero_of_one_le hu]
    exact Real.smoothTransition.monotone.deriv_nonneg
  exact hmin.deriv_eq_zero

theorem explicitIntervalPlateauDeriv_eq_zero_of_le {x N u : ℝ}
    (hu : u ≤ x - 1) :
    explicitIntervalPlateauDeriv x N u = 0 := by
  have harg : u - (x - 1) ≤ 0 := by linarith
  rw [explicitIntervalPlateauDeriv,
    Real.smoothTransition.zero_of_nonpos harg,
    deriv_smoothTransition_eq_zero_of_nonpos harg]
  ring

theorem explicitIntervalPlateauDeriv_eq_zero_of_ge {x N u : ℝ}
    (hu : N + 1 ≤ u) :
    explicitIntervalPlateauDeriv x N u = 0 := by
  have harg : (N + 1) - u ≤ 0 := by linarith
  rw [explicitIntervalPlateauDeriv,
    Real.smoothTransition.zero_of_nonpos harg,
    deriv_smoothTransition_eq_zero_of_nonpos harg]
  ring

theorem explicitIntervalPlateauDeriv_eq_zero_of_mem_Icc
    {x N u : ℝ} (hu : u ∈ Icc x N) :
    explicitIntervalPlateauDeriv x N u = 0 := by
  have hL : 1 ≤ u - (x - 1) := by linarith [hu.1]
  have hR : 1 ≤ (N + 1) - u := by linarith [hu.2]
  rw [explicitIntervalPlateauDeriv,
    deriv_smoothTransition_eq_zero_of_one_le hL,
    deriv_smoothTransition_eq_zero_of_one_le hR]
  ring

theorem explicitIntervalPlateauSecondDeriv_eq_zero_of_le {x N u : ℝ}
    (hu : u ≤ x - 1) :
    explicitIntervalPlateauSecondDeriv x N u = 0 := by
  have harg : u - (x - 1) ≤ 0 := by linarith
  rw [explicitIntervalPlateauSecondDeriv,
    Real.smoothTransition.zero_of_nonpos harg,
    deriv_smoothTransition_eq_zero_of_nonpos harg,
    secondDeriv_smoothTransition_eq_zero_of_nonpos harg]
  ring

theorem explicitIntervalPlateauSecondDeriv_eq_zero_of_ge {x N u : ℝ}
    (hu : N + 1 ≤ u) :
    explicitIntervalPlateauSecondDeriv x N u = 0 := by
  have harg : (N + 1) - u ≤ 0 := by linarith
  rw [explicitIntervalPlateauSecondDeriv,
    Real.smoothTransition.zero_of_nonpos harg,
    deriv_smoothTransition_eq_zero_of_nonpos harg,
    secondDeriv_smoothTransition_eq_zero_of_nonpos harg]
  ring

theorem explicitIntervalPlateauSecondDeriv_eq_zero_of_mem_Icc
    {x N u : ℝ} (hu : u ∈ Icc x N) :
    explicitIntervalPlateauSecondDeriv x N u = 0 := by
  have hL : 1 ≤ u - (x - 1) := by linarith [hu.1]
  have hR : 1 ≤ (N + 1) - u := by linarith [hu.2]
  rw [explicitIntervalPlateauSecondDeriv,
    deriv_smoothTransition_eq_zero_of_one_le hL,
    deriv_smoothTransition_eq_zero_of_one_le hR,
    secondDeriv_smoothTransition_eq_zero_of_one_le hL,
    secondDeriv_smoothTransition_eq_zero_of_one_le hR]
  ring

/-- The first derivative is supported in the two unit transition strips. -/
theorem explicitIntervalPlateauDeriv_eq_zero_of_not_mem_transitions
    {x N u : ℝ}
    (hu : u ∉ Icc (x - 1) x ∪ Icc N (N + 1)) :
    explicitIntervalPlateauDeriv x N u = 0 := by
  rw [mem_union, not_or] at hu
  by_cases hleft : u ≤ x - 1
  · exact explicitIntervalPlateauDeriv_eq_zero_of_le hleft
  by_cases hright : N + 1 ≤ u
  · exact explicitIntervalPlateauDeriv_eq_zero_of_ge hright
  apply explicitIntervalPlateauDeriv_eq_zero_of_mem_Icc
  constructor
  · exact le_of_not_ge fun hux => hu.1 ⟨le_of_lt (lt_of_not_ge hleft), hux⟩
  · exact le_of_not_ge fun hNu => hu.2 ⟨hNu, le_of_lt (lt_of_not_ge hright)⟩

/-- The second derivative is supported in the same two unit transition
strips. -/
theorem explicitIntervalPlateauSecondDeriv_eq_zero_of_not_mem_transitions
    {x N u : ℝ}
    (hu : u ∉ Icc (x - 1) x ∪ Icc N (N + 1)) :
    explicitIntervalPlateauSecondDeriv x N u = 0 := by
  rw [mem_union, not_or] at hu
  by_cases hleft : u ≤ x - 1
  · exact explicitIntervalPlateauSecondDeriv_eq_zero_of_le hleft
  by_cases hright : N + 1 ≤ u
  · exact explicitIntervalPlateauSecondDeriv_eq_zero_of_ge hright
  apply explicitIntervalPlateauSecondDeriv_eq_zero_of_mem_Icc
  constructor
  · exact le_of_not_ge fun hux => hu.1 ⟨le_of_lt (lt_of_not_ge hleft), hux⟩
  · exact le_of_not_ge fun hNu => hu.2 ⟨hNu, le_of_lt (lt_of_not_ge hright)⟩

theorem deriv_smoothTransition_hasCompactSupport :
    HasCompactSupport (deriv Real.smoothTransition) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  intro u hu
  rw [mem_Icc, not_and_or] at hu
  rcases hu with hu | hu
  · exact deriv_smoothTransition_eq_zero_of_nonpos (le_of_lt (lt_of_not_ge hu))
  · exact deriv_smoothTransition_eq_zero_of_one_le (le_of_lt (lt_of_not_ge hu))

theorem secondDeriv_smoothTransition_hasCompactSupport :
    HasCompactSupport (deriv (deriv Real.smoothTransition)) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  intro u hu
  rw [mem_Icc, not_and_or] at hu
  rcases hu with hu | hu
  · exact secondDeriv_smoothTransition_eq_zero_of_nonpos
      (le_of_lt (lt_of_not_ge hu))
  · exact secondDeriv_smoothTransition_eq_zero_of_one_le
      (le_of_lt (lt_of_not_ge hu))

/-- A height-independent global bound for the first derivative of the fixed
transition function. -/
theorem exists_uniform_smoothTransition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, |deriv Real.smoothTransition u| ≤ C := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (@Real.smoothTransition.contDiff 1).continuous_deriv le_rfl
  rcases deriv_smoothTransition_hasCompactSupport.exists_bound_of_continuous hcont with
    ⟨C, hC⟩
  refine ⟨C, (abs_nonneg (deriv Real.smoothTransition 0)).trans (hC 0), ?_⟩
  intro u
  simpa only [Real.norm_eq_abs] using hC u

/-- A height-independent global bound for the second derivative of the fixed
transition function. -/
theorem exists_uniform_smoothTransition_secondDeriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : ℝ, |deriv (deriv Real.smoothTransition) u| ≤ C := by
  have hdcont : ContDiff ℝ (⊤ : ℕ∞) (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  have hcont : Continuous (deriv (deriv Real.smoothTransition)) :=
    hdcont.continuous_deriv (by simp)
  rcases secondDeriv_smoothTransition_hasCompactSupport.exists_bound_of_continuous hcont with
    ⟨C, hC⟩
  refine ⟨C, (abs_nonneg (deriv (deriv Real.smoothTransition) 0)).trans (hC 0), ?_⟩
  intro u
  simpa only [Real.norm_eq_abs] using hC u

theorem abs_explicitIntervalPlateauDeriv_le
    {C₁ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (x N u : ℝ) :
    |explicitIntervalPlateauDeriv x N u| ≤ 2 * C₁ := by
  have hL0 := Real.smoothTransition.nonneg (u - (x - 1))
  have hL1 := Real.smoothTransition.le_one (u - (x - 1))
  have hR0 := Real.smoothTransition.nonneg ((N + 1) - u)
  have hR1 := Real.smoothTransition.le_one ((N + 1) - u)
  rw [explicitIntervalPlateauDeriv]
  calc
    |deriv Real.smoothTransition (u - (x - 1)) *
          Real.smoothTransition (N + 1 - u) -
        Real.smoothTransition (u - (x - 1)) *
          deriv Real.smoothTransition (N + 1 - u)|
        ≤ |deriv Real.smoothTransition (u - (x - 1))| *
              |Real.smoothTransition (N + 1 - u)| +
            |Real.smoothTransition (u - (x - 1))| *
              |deriv Real.smoothTransition (N + 1 - u)| := by
          rw [sub_eq_add_neg]
          simpa only [abs_mul, abs_neg] using
            abs_add_le
              (deriv Real.smoothTransition (u - (x - 1)) *
                Real.smoothTransition (N + 1 - u))
              (-(Real.smoothTransition (u - (x - 1)) *
                deriv Real.smoothTransition (N + 1 - u)))
    _ ≤ C₁ * 1 + 1 * C₁ := by
      rw [abs_of_nonneg hL0, abs_of_nonneg hR0]
      apply add_le_add
      · exact mul_le_mul (hC₁ _) hR1 hR0 hC₁0
      · exact mul_le_mul hL1 (hC₁ _) (abs_nonneg _) zero_le_one
    _ = 2 * C₁ := by ring

theorem abs_explicitIntervalPlateauSecondDeriv_le
    {C₁ C₂ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂)
    (x N u : ℝ) :
    |explicitIntervalPlateauSecondDeriv x N u| ≤
      2 * C₂ + 2 * C₁ ^ 2 := by
  have hL0 := Real.smoothTransition.nonneg (u - (x - 1))
  have hL1 := Real.smoothTransition.le_one (u - (x - 1))
  have hR0 := Real.smoothTransition.nonneg ((N + 1) - u)
  have hR1 := Real.smoothTransition.le_one ((N + 1) - u)
  rw [explicitIntervalPlateauSecondDeriv]
  calc
    |deriv (deriv Real.smoothTransition) (u - (x - 1)) *
            Real.smoothTransition (N + 1 - u) -
          2 * deriv Real.smoothTransition (u - (x - 1)) *
            deriv Real.smoothTransition (N + 1 - u) +
        Real.smoothTransition (u - (x - 1)) *
          deriv (deriv Real.smoothTransition) (N + 1 - u)|
        ≤ |deriv (deriv Real.smoothTransition) (u - (x - 1)) *
              Real.smoothTransition (N + 1 - u) -
            2 * deriv Real.smoothTransition (u - (x - 1)) *
              deriv Real.smoothTransition (N + 1 - u)| +
            |Real.smoothTransition (u - (x - 1)) *
              deriv (deriv Real.smoothTransition) (N + 1 - u)| := abs_add_le _ _
    _ ≤ |deriv (deriv Real.smoothTransition) (u - (x - 1))| *
              |Real.smoothTransition (N + 1 - u)| +
            2 * |deriv Real.smoothTransition (u - (x - 1))| *
              |deriv Real.smoothTransition (N + 1 - u)| +
            |Real.smoothTransition (u - (x - 1))| *
              |deriv (deriv Real.smoothTransition) (N + 1 - u)| := by
          calc
            _ ≤ (|deriv (deriv Real.smoothTransition) (u - (x - 1))| *
                    |Real.smoothTransition (N + 1 - u)| +
                  2 * |deriv Real.smoothTransition (u - (x - 1))| *
                    |deriv Real.smoothTransition (N + 1 - u)|) +
                |Real.smoothTransition (u - (x - 1))| *
                  |deriv (deriv Real.smoothTransition) (N + 1 - u)| := by
              apply add_le_add
              · rw [sub_eq_add_neg]
                simpa only [abs_mul, abs_neg,
                  abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
                  abs_add_le
                    (deriv (deriv Real.smoothTransition) (u - (x - 1)) *
                      Real.smoothTransition (N + 1 - u))
                    (-(2 * deriv Real.smoothTransition (u - (x - 1)) *
                      deriv Real.smoothTransition (N + 1 - u)))
              · rw [abs_mul]
            _ = _ := by ring
    _ ≤ C₂ * 1 + 2 * C₁ * C₁ + 1 * C₂ := by
      rw [abs_of_nonneg hL0, abs_of_nonneg hR0]
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul (hC₂ _) hR1 hR0 hC₂0
        · have hp := mul_le_mul
              (hC₁ (u - (x - 1))) (hC₁ ((N + 1) - u))
              (abs_nonneg (deriv Real.smoothTransition ((N + 1) - u))) hC₁0
          convert mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 2 by norm_num) using 1 <;>
            ring
      · exact mul_le_mul hL1 (hC₂ _) (abs_nonneg _) zero_le_one
    _ = 2 * C₂ + 2 * C₁ ^ 2 := by ring

/-- Uniform first- and second-derivative constants for every translated
explicit plateau. -/
theorem exists_uniform_explicitIntervalPlateau_deriv_bounds :
    ∃ B₁ B₂ : ℝ, 0 ≤ B₁ ∧ 0 ≤ B₂ ∧
      ∀ x N u : ℝ,
        |explicitIntervalPlateauDeriv x N u| ≤ B₁ ∧
        |explicitIntervalPlateauSecondDeriv x N u| ≤ B₂ := by
  rcases exists_uniform_smoothTransition_deriv_bound with ⟨C₁, hC₁0, hC₁⟩
  rcases exists_uniform_smoothTransition_secondDeriv_bound with ⟨C₂, hC₂0, hC₂⟩
  refine ⟨2 * C₁, 2 * C₂ + 2 * C₁ ^ 2, by positivity, by positivity, ?_⟩
  intro x N u
  exact ⟨abs_explicitIntervalPlateauDeriv_le hC₁0 hC₁ x N u,
    abs_explicitIntervalPlateauSecondDeriv_le hC₁0 hC₂0 hC₁ hC₂ x N u⟩

end AFE
end HardyTheorem
