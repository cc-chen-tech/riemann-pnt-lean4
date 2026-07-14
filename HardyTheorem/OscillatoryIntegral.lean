import Mathlib

open Complex Filter Set Topology

namespace HardyTheorem.OscillatoryIntegral

/-- The phase appearing after inserting the first zeta approximation into Hardy's integral. -/
noncomputable def hardyPhase (n : ℕ) (t : ℝ) : ℝ :=
  t / 2 *
      (Real.log (t / (2 * Real.pi * ((n : ℝ) ^ 2))) - 1) -
    Real.pi / 8

theorem deriv_hardyPhase {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t) :
    deriv (hardyPhase n) t =
      (1 / 2) * Real.log (t / (2 * Real.pi * ((n : ℝ) ^ 2))) := by
  have hn_real : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hc : 2 * Real.pi * ((n : ℝ) ^ 2) ≠ 0 := by
    positivity
  have harg_ne : t / (2 * Real.pi * ((n : ℝ) ^ 2)) ≠ 0 :=
    div_ne_zero (ne_of_gt ht) hc
  have h_arg :
      HasDerivAt (fun x : ℝ => x / (2 * Real.pi * ((n : ℝ) ^ 2)))
        (1 / (2 * Real.pi * ((n : ℝ) ^ 2))) t := by
    convert (hasDerivAt_id t).div_const (2 * Real.pi * ((n : ℝ) ^ 2)) using 1
  have h_log := h_arg.log harg_ne
  have h_linear : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) t := by
    simpa using (hasDerivAt_id t).div_const 2
  have h_phase :
      HasDerivAt (hardyPhase n)
        ((1 / 2) *
          (Real.log (t / (2 * Real.pi * ((n : ℝ) ^ 2))) - 1) +
          (t / 2) *
            ((1 / (2 * Real.pi * ((n : ℝ) ^ 2))) /
              (t / (2 * Real.pi * ((n : ℝ) ^ 2))))) t := by
    convert ((h_linear.mul (h_log.sub_const 1)).sub_const (Real.pi / 8)) using 1
  rw [h_phase.deriv]
  field_simp [ne_of_gt ht, hc]
  ring

theorem iteratedDeriv_two_hardyPhase
    {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (hardyPhase n) t = 1 / (2 * t) := by
  let g : ℝ → ℝ := fun x =>
    (1 / 2) * Real.log (x / (2 * Real.pi * ((n : ℝ) ^ 2)))
  have h_event : deriv (hardyPhase n) =ᶠ[𝓝 t] g := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact deriv_hardyPhase hn hx
  rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h_event.deriv_eq]
  have hn_real : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hc : 2 * Real.pi * ((n : ℝ) ^ 2) ≠ 0 := by
    positivity
  have harg_ne : t / (2 * Real.pi * ((n : ℝ) ^ 2)) ≠ 0 :=
    div_ne_zero (ne_of_gt ht) hc
  have h_arg :
      HasDerivAt (fun x : ℝ => x / (2 * Real.pi * ((n : ℝ) ^ 2)))
        (1 / (2 * Real.pi * ((n : ℝ) ^ 2))) t := by
    convert (hasDerivAt_id t).div_const (2 * Real.pi * ((n : ℝ) ^ 2)) using 1
  have h_g :
      HasDerivAt g
        ((1 / 2) *
          ((1 / (2 * Real.pi * ((n : ℝ) ^ 2))) /
            (t / (2 * Real.pi * ((n : ℝ) ^ 2))))) t := by
    convert (h_arg.log harg_ne).const_mul (1 / 2) using 1
  rw [h_g.deriv]
  field_simp [ne_of_gt ht, hc]

end HardyTheorem.OscillatoryIntegral
