import MathlibAux.LeftRegularizedLogDeriv
import MathlibAux.HorizontalArgument
import PrimeNumberTheorem.LittlewoodRectangle

/-!
# The complete half-weight argument identity with left-boundary zeros

The real trace is constructed by principal-part regularization. Only the
three zero-free edges use subtraction of complex logarithmic principal parts;
the entire left edge uses the continuous regularized function instead.
-/

open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace MathlibAux

/-- The oriented three-edge argument minus the constructed real left trace
counts interior zeros fully and strictly interior left-boundary zeros by half
their analytic multiplicity. The exact zero data exclude all corner zeros. -/
theorem exists_regularized_trace_half_boundary_argument
    {f : ℂ → ℂ} {x0 x1 U T : ℝ}
    (hx : x0 < x1) (hUT : U < T)
    (off left : Finset ℂ) (m : ℂ → ℕ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[U, T]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[U, T]]),
      f z = 0 ↔ z ∈ off ∪ left)
    (hoff : ∀ p ∈ off, x0 < p.re ∧ p.re < x1 ∧ U < p.im ∧ p.im < T)
    (hleft : ∀ p ∈ left, p.re = x0 ∧ U < p.im ∧ p.im < T)
    (horder : ∀ p ∈ off ∪ left, analyticOrderAt f p = m p) :
    ∃ q : ℝ → ℝ,
      ContinuousOn q (Icc U T) ∧
      (∀ t ∈ Icc U T, f ((x0 : ℂ) + I * t) ≠ 0 →
        q t = (logDeriv f ((x0 : ℂ) + I * t)).re) ∧
      (∫ x in x0..x1, (logDeriv f ((x : ℂ) + I * U)).im) +
        (∫ t in U..T, (logDeriv f ((x1 : ℂ) + I * t)).re) -
        (∫ x in x0..x1, (logDeriv f ((x : ℂ) + I * T)).im) -
        (∫ t in U..T, q t) =
          2 * Real.pi * ((∑ p ∈ off, (m p : ℝ)) + (∑ p ∈ left, (m p : ℝ)) / 2) := by
  classical
  obtain ⟨G, hG, hlink, hq, htrace, hres⟩ :=
    exists_left_regularized_logDeriv hx hUT off left m hf hzero hoff hleft horder
  let K : Set ℂ := [[x0, x1]] ×ℂ [[U, T]]
  let S : Set ℂ := {z | z ∈ K ∧ (z.im = U ∨ z.re = x1 ∨ z.im = T)}
  let P : ℂ → ℂ := fun z => ∑ p ∈ left, (z - p)⁻¹ * (m p : ℂ)
  have hSne : ∀ z ∈ S, f z ≠ 0 := by
    intro z hz hz0
    rcases Finset.mem_union.mp ((hzero z hz.1).mp hz0) with ho | hl
    · rcases hoff z ho with ⟨hz0, hz1, hzU, hzT⟩
      rcases hz.2 with hb | hr | ht <;> linarith
    · rcases hleft z hl with ⟨hz0, hzU, hzT⟩
      rcases hz.2 with hb | hr | ht <;> linarith
  have hSG : ContinuousOn G S := by
    apply hG.continuousOn.mono
    intro z hz
    refine ⟨hz.1, ?_⟩
    intro ho
    exact hSne z hz ((hzero z hz.1).mpr (Finset.mem_union_left left ho))
  have hSf : ContinuousOn (logDeriv f) S := by
    intro z hz
    exact ((hf z hz.1).deriv.div (hf z hz.1) (hSne z hz)).continuousAt.continuousWithinAt
  have hSP : ContinuousOn P S := by
    have han : AnalyticOnNhd ℂ P S := by
      intro z hz
      apply Finset.analyticAt_fun_sum
      intro p hp
      have hzp : z ≠ p := by
        intro heq
        subst p
        exact hSne z hz ((hzero z hz.1).mpr (Finset.mem_union_right off hp))
      exact ((analyticAt_id.sub analyticAt_const).inv
        (sub_ne_zero.mpr hzp)).mul analyticAt_const
    exact han.continuousOn
  have hbMap : MapsTo (fun x : ℝ => (x : ℂ) + I * U) (uIcc x0 x1) S := by
    intro x hx'
    refine ⟨?_, Or.inl (by simp)⟩
    simpa [K, mem_reProdIm] using And.intro hx' (left_mem_uIcc : U ∈ [[U, T]])
  have htMap : MapsTo (fun x : ℝ => (x : ℂ) + I * T) (uIcc x0 x1) S := by
    intro x hx'
    refine ⟨?_, Or.inr (Or.inr (by simp))⟩
    simpa [K, mem_reProdIm] using And.intro hx' (right_mem_uIcc : T ∈ [[U, T]])
  have hrMap : MapsTo (fun t : ℝ => (x1 : ℂ) + I * t) (uIcc U T) S := by
    intro t ht
    refine ⟨?_, Or.inr (Or.inl (by simp))⟩
    simpa [K, mem_reProdIm] using And.intro (right_mem_uIcc : x1 ∈ [[x0, x1]]) ht
  have hlMap : MapsTo (fun t : ℝ => (x0 : ℂ) + I * t) (uIcc U T)
      (K \ (off : Set ℂ)) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · simpa [K, mem_reProdIm] using And.intro (left_mem_uIcc : x0 ∈ [[x0, x1]]) ht
    · intro hp
      have hbad := (hoff _ hp).1
      simp at hbad
  have hbc : Continuous (fun x : ℝ => (x : ℂ) + I * U) :=
    Complex.continuous_ofReal.add continuous_const
  have htc : Continuous (fun x : ℝ => (x : ℂ) + I * T) :=
    Complex.continuous_ofReal.add continuous_const
  have hrc : Continuous (fun t : ℝ => (x1 : ℂ) + I * t) :=
    continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  have hlc : Continuous (fun t : ℝ => (x0 : ℂ) + I * t) :=
    continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  have hGb : IntervalIntegrable (fun x : ℝ => G ((x : ℂ) + I * U)) volume x0 x1 :=
    (hSG.comp hbc.continuousOn hbMap).intervalIntegrable
  have hGt : IntervalIntegrable (fun x : ℝ => G ((x : ℂ) + I * T)) volume x0 x1 :=
    (hSG.comp htc.continuousOn htMap).intervalIntegrable
  have hGr : IntervalIntegrable (fun t : ℝ => G ((x1 : ℂ) + I * t)) volume U T :=
    (hSG.comp hrc.continuousOn hrMap).intervalIntegrable
  have hGl : IntervalIntegrable (fun t : ℝ => G ((x0 : ℂ) + I * t)) volume U T :=
    (hG.continuousOn.comp hlc.continuousOn hlMap).intervalIntegrable
  have hedge {a b : ℝ} (path : ℝ → ℂ) (hc : Continuous path)
      (hm : MapsTo path (uIcc a b) S) (L : ℂ →L[ℝ] ℝ) :
      (∫ t in a..b, L (G (path t))) =
        (∫ t in a..b, L (logDeriv f (path t))) - (∫ t in a..b, L (P (path t))) := by
    calc
      _ = ∫ t in a..b, L (logDeriv f (path t)) - L (P (path t)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        change L (G (path t)) = L (logDeriv f (path t)) - L (P (path t))
        rw [hlink _ (hm ht).1 (hSne _ (hm ht))]
        exact L.map_sub _ _
      _ = _ := intervalIntegral.integral_sub
        (L.continuous.comp_continuousOn (hSf.comp hc.continuousOn hm)).intervalIntegrable
        (L.continuous.comp_continuousOn (hSP.comp hc.continuousOn hm)).intervalIntegrable
  have hb := hedge _ hbc hbMap Complex.imCLM
  have ht := hedge _ htc htMap Complex.imCLM
  have hr := hedge _ hrc hrMap Complex.reCLM
  simp only [Complex.imCLM_apply] at hb ht
  simp only [Complex.reCLM_apply] at hr
  have hfour := PrimeNumberTheorem.CarlsonZeroDensity.im_boundaryRectIntegral_eq_four_edges
    (G := G) (x0 := x0) (x1 := x1) (y0 := U) (y1 := T)
    (by simpa only [mul_comm] using hGb) (by simpa only [mul_comm] using hGt)
    (by simpa only [mul_comm] using hGr) (by simpa only [mul_comm] using hGl)
  simp only [mul_comm] at hfour
  have hresIm : (boundaryRectIntegral G x0 x1 U T).im =
      2 * Real.pi * ∑ p ∈ off, (m p : ℝ) := by
    rw [hres]
    simp [Complex.mul_im, Complex.mul_re]
  have hPthree :
      (∫ x in x0..x1, (P ((x : ℂ) + I * U)).im) +
      (∫ t in U..T, (P ((x1 : ℂ) + I * t)).re) -
      (∫ x in x0..x1, (P ((x : ℂ) + I * T)).im) =
        Real.pi * ∑ p ∈ left, (m p : ℝ) :=
    threeEdgeArgument_left_principalParts_eq_pi_mul_sum left m hx hleft
  refine ⟨fun t : ℝ => (G ((x0 : ℂ) + I * t)).re, hq, htrace, ?_⟩
  nlinarith only [hb, ht, hr, hfour, hresIm, hPthree]

end MathlibAux
