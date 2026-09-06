import PrimeNumberTheorem.LittlewoodRectangle
import MathlibAux.ReverseFatouEpsilon
import MathlibAux.VerticalLogIntegrable

open Complex Filter MeasureTheory Set Topology
open scoped Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The three non-left edge terms in Littlewood's rectangle identity when
the left edge is at `x`. -/
noncomputable def littlewoodRectangleNonleftRemainder
    (f : ℂ → ℂ) (x x1 y0 y1 : ℝ) : ℝ :=
  -(∫ y in y0..y1,
      Real.log ‖f ((x1 : ℂ) + (y : ℂ) * I)‖) +
    (∫ u in x..x1,
      (u - x) * (logDeriv f ((u : ℂ) + (y0 : ℂ) * I)).im) -
    (∫ u in x..x1,
      (u - x) * (logDeriv f ((u : ℂ) + (y1 : ℂ) * I)).im) +
    (x1 - x) *
      (∫ y in y0..y1,
        (logDeriv f ((x1 : ℂ) + (y : ℂ) * I)).re)

set_option maxHeartbeats 800000 in
/-- Littlewood's weighted zero-count upper bound with zeros permitted on the
limiting left edge.

The sequence `x` consists of zero-free vertical lines to the right of `x0`
and to the left of `critical`, converging to `x0`.  Reverse Fatou replaces
the logarithmic integral on one such shifted line by the limiting left-edge
integral plus `delta`.  The remaining boundary terms are intentionally kept
at that same shifted line; their ordinary convergence is a separate lemma. -/
theorem exists_littlewoodRectangle_mass_le_logNormEdges_of_leftBoundaryZeros
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
    {C delta : ℝ} (hdelta : 0 < delta)
    (hlogle : ∀ sigma ∈ [[x0, x1]], ∀ y ∈ [[y0, y1]],
      Real.log ‖f ((sigma : ℂ) + I * (y : ℂ))‖ ≤ C) :
    ∃ n,
      (2 * Real.pi) * (critical - x n) *
          zeroMultiplicityMassAtOrRight poles multiplicity critical ≤
        (∫ y in y0..y1,
          Real.log ‖f ((x0 : ℂ) + I * (y : ℂ))‖) + delta +
        littlewoodRectangleNonleftRemainder f (x n) x1 y0 y1 := by
  let mu : Measure ℝ := volume.restrict (Set.Ioc y0 y1)
  let verticalLog : ℕ → ℝ → ℝ := fun n y =>
    Real.log ‖f ((x n : ℂ) + I * (y : ℂ))‖
  let leftLog : ℝ → ℝ := fun y =>
    Real.log ‖f ((x0 : ℂ) + I * (y : ℂ))‖
  have hxmem : ∀ n, x n ∈ [[x0, x1]] := by
    intro n
    rw [uIcc_of_le hx.le]
    exact ⟨(hxleft n).le, (hxcritical n).trans hcritical1 |>.le⟩
  have hyMem : ∀ y ∈ Set.Ioc y0 y1, y ∈ [[y0, y1]] := by
    intro y hy'
    rw [uIcc_of_le hy.le]
    exact ⟨hy'.1.le, hy'.2⟩
  have hCint : Integrable (fun _ : ℝ => C) mu := by
    dsimp only [mu]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hy.le).mp
      intervalIntegrable_const
  have hverticalInt : ∀ n, Integrable (verticalLog n) mu := by
    intro n
    dsimp only [verticalLog, mu]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hy.le).mp
      (MathlibAux.intervalIntegrable_log_norm_vertical_of_analyticOnNhd
        hf (hxmem n))
  have hleftInt : Integrable leftLog mu := by
    dsimp only [leftLog, mu]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hy.le).mp
      (MathlibAux.intervalIntegrable_log_norm_vertical_of_analyticOnNhd
        hf (left_mem_uIcc : x0 ∈ [[x0, x1]]))
  have hverticalLe : ∀ n, verticalLog n ≤ᵐ[mu] fun _ => C := by
    intro n
    dsimp only [mu]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy'
    exact hlogle (x n) (hxmem n) y (hyMem y hy')
  have hleftLe : leftLog ≤ᵐ[mu] fun _ => C := by
    dsimp only [mu]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy'
    exact hlogle x0 (left_mem_uIcc : x0 ∈ [[x0, x1]]) y (hyMem y hy')
  have hverticalTendsto : ∀ᵐ y ∂mu,
      Tendsto (fun n => verticalLog n y) atTop (𝓝 (leftLog y)) := by
    simpa only [mu, verticalLog, leftLog] using
      (MathlibAux.ae_tendsto_log_norm_vertical_of_analyticOnNhd_finite_zeros
        hf hzero hxtend)
  rcases MathlibAux.exists_integral_le_add_of_ae_tendsto_of_le
      hdelta hCint hverticalInt hleftInt hverticalLe hleftLe
      hverticalTendsto with ⟨n, hn⟩
  have hleftLogBound :
      (∫ y in y0..y1,
          Real.log ‖f ((x n : ℂ) + I * (y : ℂ))‖) ≤
        (∫ y in y0..y1,
          Real.log ‖f ((x0 : ℂ) + I * (y : ℂ))‖) + delta := by
    rw [intervalIntegral.integral_of_le hy.le,
      intervalIntegral.integral_of_le hy.le]
    simpa only [mu, verticalLog, leftLog] using hn
  let shiftedPoles : Finset ℂ := poles.filter (fun rho => x n < rho.re)
  have hrectSubset :
      ([[x n, x1]] ×ℂ [[y0, y1]] : Set ℂ) ⊆
        ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ) := by
    intro z hz
    rw [mem_reProdIm] at hz ⊢
    constructor
    · rw [uIcc_of_le ((hxcritical n).trans hcritical1).le] at hz
      rw [uIcc_of_le hx.le]
      exact ⟨(hxleft n).le.trans hz.1.1, hz.1.2⟩
    · exact hz.2
  have hfShift : AnalyticOnNhd ℂ f
      ([[x n, x1]] ×ℂ [[y0, y1]]) := hf.mono hrectSubset
  have hzeroShift : ∀ z ∈
      ([[x n, x1]] ×ℂ [[y0, y1]] : Set ℂ),
      f z = 0 ↔ z ∈ shiftedPoles := by
    intro z hz
    have hzOriginal := hrectSubset hz
    rw [mem_reProdIm] at hz
    constructor
    · intro hfz
      have hpole : z ∈ poles := (hzero z hzOriginal).mp hfz
      have hxnle : x n ≤ z.re := by
        rw [uIcc_of_le ((hxcritical n).trans hcritical1).le] at hz
        exact hz.1.1
      have hxnne : x n ≠ z.re := by
        intro heq
        have hlineNe := hxline n z.im hz.2
        apply hlineNe
        have hpointEq : (x n : ℂ) + I * (z.im : ℂ) = z := calc
          (x n : ℂ) + I * (z.im : ℂ) =
              (z.re : ℂ) + (z.im : ℂ) * I := by
            rw [heq]
            ring
          _ = z := Complex.re_add_im z
        rw [hpointEq]
        exact hfz
      exact Finset.mem_filter.mpr
        ⟨hpole, lt_of_le_of_ne hxnle hxnne⟩
    · intro hzFiltered
      exact (hzero z hzOriginal).mpr (Finset.mem_filter.mp hzFiltered).1
  have horderShift : ∀ rho ∈ shiftedPoles,
      analyticOrderAt f rho = multiplicity rho := by
    intro rho hrho
    exact horder rho (Finset.mem_filter.mp hrho).1
  have hpolesShift : ∀ rho ∈ shiftedPoles,
      x n < rho.re ∧ rho.re < x1 ∧ y0 < rho.im ∧ rho.im < y1 := by
    intro rho hrho
    have hmem := Finset.mem_filter.mp hrho
    exact ⟨hmem.2, (hpoles rho hmem.1).2⟩
  have hexact :=
    littlewoodRectangle_zeroMultiplicityWeightedRealSum_eq_logNormEdges
      ((hxcritical n).trans hcritical1) hy shiftedPoles multiplicity
      hfShift hzeroShift horderShift hpolesShift
  have hmassEq :
      zeroMultiplicityMassAtOrRight shiftedPoles multiplicity critical =
        zeroMultiplicityMassAtOrRight poles multiplicity critical := by
    unfold zeroMultiplicityMassAtOrRight
    congr 1
    ext rho
    simp only [shiftedPoles, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hrho, _⟩, hcritical⟩
      exact ⟨hrho, hcritical⟩
    · rintro ⟨hrho, hcritical⟩
      exact ⟨⟨hrho, (hxcritical n).trans_le hcritical⟩, hcritical⟩
  have hweighted :=
    sub_mul_zeroMultiplicityMassAtOrRight_le_weightedRealSum
      (poles := shiftedPoles) (multiplicity := multiplicity)
      (x0 := x n) (critical := critical)
      (fun rho hrho => (Finset.mem_filter.mp hrho).2.le)
  have hpiNonneg : 0 ≤ 2 * Real.pi := by positivity
  have hweightedPi := mul_le_mul_of_nonneg_left hweighted hpiNonneg
  refine ⟨n, ?_⟩
  calc
    (2 * Real.pi) * (critical - x n) *
          zeroMultiplicityMassAtOrRight poles multiplicity critical =
        (2 * Real.pi) *
          ((critical - x n) *
            zeroMultiplicityMassAtOrRight shiftedPoles multiplicity critical) := by
      rw [hmassEq]
      ring
    _ ≤ (2 * Real.pi) *
        (∑ rho ∈ shiftedPoles,
          (rho.re - x n) * (multiplicity rho : ℝ)) := hweightedPi
    _ = (∫ y in y0..y1,
          Real.log ‖f ((x n : ℂ) + I * (y : ℂ))‖) +
        littlewoodRectangleNonleftRemainder f (x n) x1 y0 y1 := by
      rw [hexact]
      simp only [littlewoodRectangleNonleftRemainder]
      simp only [mul_comm I]
      abel
    _ ≤ (∫ y in y0..y1,
          Real.log ‖f ((x0 : ℂ) + I * (y : ℂ))‖) + delta +
        littlewoodRectangleNonleftRemainder f (x n) x1 y0 y1 := by
      linarith

end CarlsonZeroDensity
end PrimeNumberTheorem
