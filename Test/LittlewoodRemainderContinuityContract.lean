import PrimeNumberTheorem.LittlewoodRemainderContinuity

open Complex Filter MeasureTheory Set Topology
open scoped Interval
open PrimeNumberTheorem.CarlsonZeroDensity

-- Mutation caught: reversing the moving endpoint or dropping the `(u - x)`
-- weight changes this exact public contract.
example {g : ℝ → ℝ} {x0 x1 : ℝ}
    (hg : ContinuousOn g [[x0, x1]]) :
    ContinuousOn
      (fun x => ∫ u in x..x1, (u - x) * g u)
      [[x0, x1]] := by
  exact continuousOn_intervalIntegral_sub_mul_left hg

-- Mutation caught: adding a zero-free hypothesis on the limiting left edge,
-- or moving one horizontal term to a different endpoint, no longer fits.
example {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (hbottomA : ∀ x ∈ [[x0, x1]],
      AnalyticAt ℂ f ((x : ℂ) + (y0 : ℂ) * I))
    (hbottomNe : ∀ x ∈ [[x0, x1]],
      f ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htopA : ∀ x ∈ [[x0, x1]],
      AnalyticAt ℂ f ((x : ℂ) + (y1 : ℂ) * I))
    (htopNe : ∀ x ∈ [[x0, x1]],
      f ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) :
    ContinuousOn
      (fun x => littlewoodRectangleNonleftRemainder f x x1 y0 y1)
      [[x0, x1]] := by
  exact continuousOn_littlewoodRectangleNonleftRemainder
    hbottomA hbottomNe htopA htopNe

-- Mutation caught: the sequence must stay in the ambient interval and the
-- target is the remainder at the limiting endpoint `x0`, not at a shifted line.
example {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (hbottomA : ∀ x ∈ [[x0, x1]],
      AnalyticAt ℂ f ((x : ℂ) + (y0 : ℂ) * I))
    (hbottomNe : ∀ x ∈ [[x0, x1]],
      f ((x : ℂ) + (y0 : ℂ) * I) ≠ 0)
    (htopA : ∀ x ∈ [[x0, x1]],
      AnalyticAt ℂ f ((x : ℂ) + (y1 : ℂ) * I))
    (htopNe : ∀ x ∈ [[x0, x1]],
      f ((x : ℂ) + (y1 : ℂ) * I) ≠ 0)
    {x : ℕ → ℝ}
    (hxmem : ∀ n, x n ∈ [[x0, x1]])
    (hxtend : Tendsto x atTop (𝓝 x0)) :
    Tendsto
      (fun n => littlewoodRectangleNonleftRemainder f (x n) x1 y0 y1)
      atTop
      (𝓝 (littlewoodRectangleNonleftRemainder f x0 x1 y0 y1)) := by
  exact tendsto_littlewoodRectangleNonleftRemainder
    hbottomA hbottomNe htopA htopNe hxmem hxtend

#print axioms continuousOn_intervalIntegral_sub_mul_left
#print axioms continuousOn_littlewoodRectangleNonleftRemainder
#print axioms tendsto_littlewoodRectangleNonleftRemainder
