import PrimeNumberTheorem.LittlewoodRemainderContinuity

open Complex Filter MeasureTheory Set Topology
open scoped Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

set_option maxHeartbeats 1200000 in
/-- Littlewood's weighted zero-count upper bound on the limiting rectangle,
with zeros allowed on its left edge.

The proof applies the shifted reverse-Fatou estimate to every tail of the
zero-free-line sequence.  This forces its existentially selected line far
enough out that both the coefficient `critical - x n` and the complete
non-left remainder are close to their limiting values. -/
theorem littlewoodRectangle_mass_le_logNormEdges_of_leftBoundaryZeros
    {f : ℂ → ℂ} {x0 x1 y0 y1 critical : ℝ}
    (hx : x0 < x1) (hy : y0 < y1)
    (hcritical1 : critical < x1)
    (poles : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ),
      f z = 0 ↔ z ∈ poles)
    (horder : ∀ rho ∈ poles,
      analyticOrderAt f rho = multiplicity rho)
    (hpoles : ∀ rho ∈ poles,
      x0 ≤ rho.re ∧ rho.re < x1 ∧ y0 < rho.im ∧ rho.im < y1)
    {x : ℕ → ℝ}
    (hxleft : ∀ n, x0 < x n)
    (hxcritical : ∀ n, x n < critical)
    (hxline : ∀ n y, y ∈ [[y0, y1]] →
      f ((x n : ℂ) + I * (y : ℂ)) ≠ 0)
    (hxtend : Tendsto x atTop (𝓝 x0))
    {C : ℝ}
    (hlogle : ∀ sigma ∈ [[x0, x1]], ∀ y ∈ [[y0, y1]],
      Real.log ‖f ((sigma : ℂ) + I * (y : ℂ))‖ ≤ C) :
    (2 * Real.pi) * (critical - x0) *
        zeroMultiplicityMassAtOrRight poles multiplicity critical ≤
      (∫ y in y0..y1,
        Real.log ‖f ((x0 : ℂ) + I * (y : ℂ))‖) +
      littlewoodRectangleNonleftRemainder f x0 x1 y0 y1 := by
  let mass : ℝ := zeroMultiplicityMassAtOrRight poles multiplicity critical
  let coeff : ℕ → ℝ := fun n =>
    (2 * Real.pi) * (critical - x n) * mass
  let coeff0 : ℝ := (2 * Real.pi) * (critical - x0) * mass
  let rem : ℝ → ℝ := fun u =>
    littlewoodRectangleNonleftRemainder f u x1 y0 y1
  have hxmem : ∀ n, x n ∈ [[x0, x1]] := by
    intro n
    rw [uIcc_of_le hx.le]
    exact ⟨(hxleft n).le, (hxcritical n).trans hcritical1 |>.le⟩
  have hbottomA : ∀ u ∈ [[x0, x1]],
      AnalyticAt ℂ f ((u : ℂ) + (y0 : ℂ) * I) := by
    intro u hu
    apply hf
    rw [mem_reProdIm]
    simpa using And.intro hu (left_mem_uIcc : y0 ∈ [[y0, y1]])
  have htopA : ∀ u ∈ [[x0, x1]],
      AnalyticAt ℂ f ((u : ℂ) + (y1 : ℂ) * I) := by
    intro u hu
    apply hf
    rw [mem_reProdIm]
    simpa using And.intro hu (right_mem_uIcc : y1 ∈ [[y0, y1]])
  have hbottomNe : ∀ u ∈ [[x0, x1]],
      f ((u : ℂ) + (y0 : ℂ) * I) ≠ 0 := by
    intro u hu hfu
    let z : ℂ := (u : ℂ) + (y0 : ℂ) * I
    have hzmem : z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ) := by
      rw [mem_reProdIm]
      simpa [z] using And.intro hu (left_mem_uIcc : y0 ∈ [[y0, y1]])
    have hzp : z ∈ poles := (hzero z hzmem).mp hfu
    have := (hpoles z hzp).2.2.1
    simp [z] at this
  have htopNe : ∀ u ∈ [[x0, x1]],
      f ((u : ℂ) + (y1 : ℂ) * I) ≠ 0 := by
    intro u hu hfu
    let z : ℂ := (u : ℂ) + (y1 : ℂ) * I
    have hzmem : z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ) := by
      rw [mem_reProdIm]
      simpa [z] using And.intro hu (right_mem_uIcc : y1 ∈ [[y0, y1]])
    have hzp : z ∈ poles := (hzero z hzmem).mp hfu
    have := (hpoles z hzp).2.2.2
    simp [z] at this
  have hrem : Tendsto (fun n => rem (x n)) atTop (𝓝 (rem x0)) := by
    exact tendsto_littlewoodRectangleNonleftRemainder
      hbottomA hbottomNe htopA htopNe hxmem hxtend
  have hcoeff : Tendsto coeff atTop (𝓝 coeff0) := by
    dsimp only [coeff, coeff0]
    exact ((tendsto_const_nhds.sub hxtend).const_mul (2 * Real.pi)).mul_const mass
  refine le_of_forall_pos_le_add fun epsilon hepsilon => ?_
  have hepsilonThird : 0 < epsilon / 3 := by positivity
  rcases (Metric.tendsto_atTop.mp hcoeff) (epsilon / 3) hepsilonThird with
    ⟨Ncoeff, hNcoeff⟩
  rcases (Metric.tendsto_atTop.mp hrem) (epsilon / 3) hepsilonThird with
    ⟨Nrem, hNrem⟩
  let N := max Ncoeff Nrem
  let xtail : ℕ → ℝ := fun k => x (k + N)
  have hxtailLeft : ∀ k, x0 < xtail k := fun k => hxleft (k + N)
  have hxtailCritical : ∀ k, xtail k < critical := fun k => hxcritical (k + N)
  have hxtailLine : ∀ k y, y ∈ [[y0, y1]] →
      f ((xtail k : ℂ) + I * (y : ℂ)) ≠ 0 := by
    intro k y hy'
    exact hxline (k + N) y hy'
  have hxtailTend : Tendsto xtail atTop (𝓝 x0) := by
    exact hxtend.comp (tendsto_add_atTop_nat N)
  rcases exists_littlewoodRectangle_mass_le_logNormEdges_of_leftBoundaryZeros
      hx hy hcritical1 poles multiplicity hf hzero horder hpoles
      hxtailLeft hxtailCritical hxtailLine hxtailTend
      hepsilonThird hlogle with ⟨k, hk⟩
  have hNk : N ≤ k + N := Nat.le_add_left N k
  have hNcoeffLe : Ncoeff ≤ k + N := (le_max_left _ _).trans hNk
  have hNremLe : Nrem ≤ k + N := (le_max_right _ _).trans hNk
  have hcoeffClose := hNcoeff (k + N) hNcoeffLe
  have hremClose := hNrem (k + N) hNremLe
  rw [Real.dist_eq] at hcoeffClose hremClose
  rcases abs_lt.mp hcoeffClose with ⟨hcoeffLower, hcoeffUpper⟩
  rcases abs_lt.mp hremClose with ⟨hremLower, hremUpper⟩
  dsimp only [xtail, coeff, coeff0, mass, rem] at hk hcoeffLower hcoeffUpper hremLower hremUpper ⊢
  linarith

end CarlsonZeroDensity
end PrimeNumberTheorem
