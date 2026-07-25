import Mathlib

open Set

namespace HardyTheorem

/-!
# Dyadic geometry for the Selberg lag representation

The triangular lag section keeps both the original point and its translate
inside the dyadic interval used by the short-interval argument.
-/

/-- A point in the lag section's translated interior interval remains in the
original dyadic interval. -/
theorem selberg_lag_dyadic_mem
    {T H τ v x : ℝ} (hH0 : 0 ≤ H) (hHT : H ≤ T)
    (hτ : τ ∈ Icc (-H) H)
    (hv : v ∈ Icc (max 0 (-τ)) (min H (H - τ)))
    (hx : x ∈ Icc (T + v) ((2 * T - H) + v)) :
    x ∈ Icc T (2 * T) := by
  rcases hτ with ⟨hτlow, hτhigh⟩
  rcases hv with ⟨hvlow, hvhigh⟩
  rcases hx with ⟨hxlow, hxhigh⟩
  have hv0 : 0 ≤ v := le_trans (le_max_left _ _) hvlow
  have hvH : v ≤ H := le_trans hvhigh (min_le_left _ _)
  constructor <;> linarith

/-- The lag translate of a point in the triangular section remains in the
same dyadic interval. -/
theorem selberg_lag_shifted_dyadic_mem
    {T H τ v x : ℝ} (hH0 : 0 ≤ H) (hHT : H ≤ T)
    (hτ : τ ∈ Icc (-H) H)
    (hv : v ∈ Icc (max 0 (-τ)) (min H (H - τ)))
    (hx : x ∈ Icc (T + v) ((2 * T - H) + v)) :
    x + τ ∈ Icc T (2 * T) := by
  rcases hτ with ⟨hτlow, hτhigh⟩
  rcases hv with ⟨hvlow, hvhigh⟩
  rcases hx with ⟨hxlow, hxhigh⟩
  have hvτ0 : 0 ≤ v + τ := by
    have hnegτ : -τ ≤ v := le_trans (le_max_right _ _) hvlow
    linarith
  have hvτH : v + τ ≤ H := by
    have hsub : v ≤ H - τ := le_trans hvhigh (min_le_right _ _)
    linarith
  constructor <;> linarith

/-- The control interval spanning the original and translated lag sections is
contained in the dyadic interval. -/
theorem selberg_lag_controlInterval_subset_dyadic
    {T H τ v : ℝ} (hH0 : 0 ≤ H) (hHT : H ≤ T)
    (hτ : τ ∈ Icc (-H) H)
    (hv : v ∈ Icc (max 0 (-τ)) (min H (H - τ))) :
    Icc (min (T + v) (T + v + τ))
        (max ((2 * T - H) + v) ((2 * T - H) + v + τ)) ⊆ Icc T (2 * T) := by
  intro x hx
  rcases hτ with ⟨hτlow, hτhigh⟩
  rcases hv with ⟨hvlow, hvhigh⟩
  rcases hx with ⟨hxlow, hxhigh⟩
  have hv0 : 0 ≤ v := le_trans (le_max_left _ _) hvlow
  have hvH : v ≤ H := le_trans hvhigh (min_le_left _ _)
  have hvτ0 : 0 ≤ v + τ := by
    have hnegτ : -τ ≤ v := le_trans (le_max_right _ _) hvlow
    linarith
  have hvτH : v + τ ≤ H := by
    have hsub : v ≤ H - τ := le_trans hvhigh (min_le_right _ _)
    linarith
  constructor
  · have hleft : T ≤ min (T + v) (T + v + τ) := by
      apply le_min <;> linarith
    exact hleft.trans hxlow
  · have hright : max ((2 * T - H) + v) ((2 * T - H) + v + τ) ≤ 2 * T := by
      apply max_le <;> linarith
    exact hxhigh.trans hright

end HardyTheorem
