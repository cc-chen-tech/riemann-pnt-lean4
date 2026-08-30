import HardyTheorem.AFEExplicitPoissonIdentity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Subtract the exact Mellin main term before passing to the cutoff limit. -/

open Complex Set MeasureTheory

namespace HardyTheorem.AFE

private theorem norm_cutoff_le {s : ℂ} {x N u : ℝ} (hu : 0 < u) :
    ‖explicitWeightedPoissonCutoff s x N u‖ ≤ u ^ (-s.re) := by
  have hw0 := explicitIntervalPlateau_nonneg x N u
  have hw1 := explicitIntervalPlateau_le_one x N u
  rw [explicitWeightedPoissonCutoff, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hw0, Complex.norm_exp]
  have hexp : Real.exp ((-s * (Real.log u : ℂ)).re) = u ^ (-s.re) := by
    rw [Real.rpow_def_of_pos hu]
    congr 1
    simp
    ring
  rw [hexp]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hu.le _) hw1

private theorem norm_cutoff_interval_le {s : ℂ} {x N a b : ℝ}
    (hs : 0 ≤ s.re) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ u in a..b, explicitWeightedPoissonCutoff s x N u‖ ≤
      a ^ (-s.re) * (b - a) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := explicitWeightedPoissonCutoff s x N)
    (C := a ^ (-s.re)) (fun u hu => by
      have hu' : u ∈ Ioc a b := by simpa only [uIoc_of_le hab] using hu
      exact (norm_cutoff_le (ha.trans hu'.1)).trans
        (Real.rpow_le_rpow_of_nonpos ha hu'.1.le (neg_nonpos.mpr hs)))
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using h

/-- The two width-one transitions are the only errors in the Mellin core. -/
theorem norm_explicitWeightedPoissonIntegral_sub_core_le {s : ℂ} {x N : ℝ}
    (hs : 0 ≤ s.re) (hs1 : s ≠ 1) (hx : 1 < x) (hxN : x ≤ N) :
    ‖(∫ u in (x - 1)..(N + 1), explicitWeightedPoissonCutoff s x N u) -
      ((N : ℂ) ^ (1 - s) - (x : ℂ) ^ (1 - s)) / (1 - s)‖ ≤
        (x - 1) ^ (-s.re) + N ^ (-s.re) := by
  let f := explicitWeightedPoissonCutoff s x N
  have hx0 : 0 < x := by linarith
  have hN0 : 0 < N := hx0.trans_le hxN
  have hi (a b : ℝ) : IntervalIntegrable f volume a b :=
    (explicitWeightedPoissonCutoff_contDiff s hx).continuous.intervalIntegrable a b
  have hcore : (∫ u in x..N, f u) =
      ((N : ℂ) ^ (1 - s) - (x : ℂ) ^ (1 - s)) / (1 - s) := by
    calc
      _ = ∫ u in x..N, (u : ℂ) ^ (-s) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact explicitWeightedPoissonCutoff_eq_cpow s hx0
          (by simpa only [uIcc_of_le hxN] using hu)
      _ = _ := by
        have hz : (0 : ℝ) ∉ uIcc x N := by
          rw [uIcc_of_le hxN]
          intro h
          linarith [h.1]
        have hr : -s ≠ -(1 : ℂ) := fun h => hs1 (neg_injective h)
        simpa only [show -s + 1 = 1 - s by ring] using
          (integral_cpow (a := x) (b := N) (r := -s) (Or.inr ⟨hr, hz⟩))
  have hsplit : (∫ u in (x - 1)..(N + 1), f u) =
      (∫ u in (x - 1)..x, f u) + (∫ u in x..N, f u) +
        (∫ u in N..(N + 1), f u) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi (x - 1) x) (hi x N),
      intervalIntegral.integral_add_adjacent_intervals (hi (x - 1) N) (hi N (N + 1))]
  have hleft : ‖∫ u in (x - 1)..x, f u‖ ≤ (x - 1) ^ (-s.re) := by
    simpa only [show x - (x - 1) = (1 : ℝ) by ring, mul_one] using
      (norm_cutoff_interval_le (x := x) (N := N) hs
        (show 0 < x - 1 by linarith) (show x - 1 ≤ x by linarith))
  have hright : ‖∫ u in N..(N + 1), f u‖ ≤ N ^ (-s.re) := by
    simpa only [show N + 1 - N = (1 : ℝ) by ring, mul_one] using
      (norm_cutoff_interval_le (x := x) (N := N) hs hN0 (show N ≤ N + 1 by linarith))
  change ‖(∫ u in (x - 1)..(N + 1), f u) - _‖ ≤ _
  rw [hsplit, ← hcore]
  convert (norm_add_le (∫ u in (x - 1)..x, f u) (∫ u in N..(N + 1), f u)).trans
    (add_le_add hleft hright) using 1 <;> congr 1 <;> ring

private theorem explicitPoissonMode_zero_eq_integral
    (sigma t : ℝ) {x N : ℝ} (hx : 1 < x) (hxN : x ≤ N) :
    explicitPoissonMode sigma x N t 0 =
      ∫ u in (x - 1)..(N + 1),
        explicitWeightedPoissonCutoff ((sigma : ℂ) + I * t) x N u := by
  unfold explicitPoissonMode
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc (x - 1) (N + 1) := by
    simpa only [uIcc_of_le (show x - 1 ≤ N + 1 by linarith)] using hu
  have hu0 : 0 < u := by linarith [hu'.1]
  simpa using
    (explicitWeightedPoissonCutoff_fourierIntegrand_eq sigma t x N u 0 hu0).symm

/-- Subtract the upper main term before taking the upper-cutoff limit. -/
theorem norm_explicitPoissonZeroMode_sub_main_le {sigma x N t : ℝ}
    (hs : 0 ≤ sigma) (hx : 1 < x) (hxN : x ≤ N) (ht : 0 < t) :
    let s : ℂ := (sigma : ℂ) + I * t
    ‖explicitPoissonMode sigma x N t 0 - (N : ℂ) ^ (1 - s) / (1 - s)‖ ≤
      (x - 1) ^ (-sigma) + N ^ (-sigma) + x ^ (1 - sigma) / t := by
  let s : ℂ := (sigma : ℂ) + I * t
  change ‖explicitPoissonMode sigma x N t 0 - (N : ℂ) ^ (1 - s) / (1 - s)‖ ≤ _
  have hsre : s.re = sigma := by simp [s]
  have hs1 : s ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp [s] at hi
    linarith
  have hden : t ≤ ‖1 - s‖ := by
    simpa [s, abs_of_pos ht] using Complex.abs_im_le_norm (1 - s)
  have hx0 : 0 < x := by linarith
  have hpower : ‖(x : ℂ) ^ (1 - s) / (1 - s)‖ ≤ x ^ (1 - sigma) / t := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (1 - s).re = 1 - sigma := by simp [s]
    rw [hre]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) ht hden
  have hcore := norm_explicitWeightedPoissonIntegral_sub_core_le
    (s := s) (by simpa only [hsre] using hs) hs1 hx hxN
  rw [← explicitPoissonMode_zero_eq_integral sigma t hx hxN] at hcore
  simp only [hsre] at hcore
  have hid : explicitPoissonMode sigma x N t 0 - (N : ℂ) ^ (1 - s) / (1 - s) =
      (explicitPoissonMode sigma x N t 0 -
        ((N : ℂ) ^ (1 - s) - (x : ℂ) ^ (1 - s)) / (1 - s)) -
          (x : ℂ) ^ (1 - s) / (1 - s) := by rw [sub_div]; ring
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add hcore hpower)

end HardyTheorem.AFE
