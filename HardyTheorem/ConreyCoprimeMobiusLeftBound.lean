import HardyTheorem.ConreyCoprimeMobiusLeftMajorant
import MathlibAux.LogPowerMajorants

open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace HardyTheorem

/-- Uniform bound for the actual unnormalized left Perron edge. The
constants are independent of height, modulus, shift, cutoff and width.
The pole unit and all analytic/integrability inputs are proved natively. -/
theorem exists_conrey_coprime_mobius_left_bound :
    ∃ κ C M : ℝ, 0 < κ ∧ κ ≤ 1 / 4 ∧ 0 < C ∧ 3 ≤ M ∧
      ∀ (K : ℝ) (m : ℕ) (δ : ℝ) (α : ℂ) (X b : ℝ),
        M ≤ K → 0 ≤ δ → δ ≤ 1 / 16 → 0 < X → 0 < b → ‖α‖ < b →
        b + ‖α‖ ≤ 2 * δ → b + ‖α‖ ≤ κ / (1 + Real.log (K + 3)) →
        let f : ℝ → ℂ := fun t => (X : ℂ) ^ ((-b : ℂ) + t * I) *
          (riemannZeta (1 + α + ((-b : ℂ) + t * I)) *
            ∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + ((-b : ℂ) + t * I)))))⁻¹ *
          (1 / ((-b : ℂ) + t * I) ^ 2)
        IntervalIntegrable f volume (-K) K ∧
          ‖∫ t in (-K)..K, f t‖ ≤ C *
            (∏ p ∈ m.primeFactors, (1 + (p : ℝ) ^ (-(1 - 2 * δ)))) *
            X ^ (-b) * (1 + Real.log (1 + 1 / b)) := by
  obtain ⟨κ, C, D, M, hκ, hκ4, hC, hD, hM, hmajor⟩ :=
    exists_conrey_coprime_mobius_left_majorants
  have hMpos : 0 < M := by linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  let C' := 2 * C * (1 + Real.log M) + 4 * D
  have hC' : 0 < C' := by dsimp [C']; positivity
  refine ⟨κ, C', M, hκ, hκ4, hC', hM, ?_⟩
  intro K m δ α X b hK hδ hδ16 hX hb hαb hδwidth hwidth
  dsimp only
  obtain ⟨hcont, hlow, hhigh⟩ := hmajor K m δ α X b hK hδ hδ16 hX hb hαb hδwidth hwidth
  have hB := conreyCoprimeEulerMajorant_nonneg m δ
  have hXP : 0 < X ^ (-b) := Real.rpow_pos_of_pos hX _
  have hbound := MathlibAux.norm_integral_le_log_power_majorants
    (A := C * conreyCoprimeEulerMajorant m δ * X ^ (-b))
    (D := D * conreyCoprimeEulerMajorant m δ * X ^ (-b))
    (by positivity) (by positivity) hb (by linarith) hK hcont hlow hhigh
  have hL : 0 ≤ Real.log (1 + 1 / b) :=
    Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have hlog : Real.log (1 + M / b) ≤ Real.log M + Real.log (1 + 1 / b) := by
    rw [← Real.log_mul hMpos.ne' (by positivity)]
    apply Real.log_le_log (by positivity)
    have hh : 1 + M / b ≤ M + M / b := by linarith
    convert hh using 1 <;> ring
  have hscalar : 2 * C * Real.log (1 + M / b) + 4 * D ≤
      C' * (1 + Real.log (1 + 1 / b)) := by
    have hh : Real.log (1 + M / b) ≤
        (1 + Real.log M) * (1 + Real.log (1 + 1 / b)) := by
      nlinarith [mul_nonneg hlogM hL]
    have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * C)
    dsimp [C']
    nlinarith [mul_nonneg hD.le hL]
  refine ⟨?_, ?_⟩
  · apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by linarith : -K ≤ K)] using hcont
  · calc
      _ ≤ (conreyCoprimeEulerMajorant m δ * X ^ (-b)) *
          (2 * C * Real.log (1 + M / b) + 4 * D) := by
        convert hbound using 1 <;> ring
      _ ≤ (conreyCoprimeEulerMajorant m δ * X ^ (-b)) *
          (C' * (1 + Real.log (1 + 1 / b))) :=
        mul_le_mul_of_nonneg_left hscalar (mul_nonneg hB hXP.le)
      _ = _ := by unfold conreyCoprimeEulerMajorant; ring

end HardyTheorem
