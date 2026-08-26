import Mathlib.Analysis.Complex.Hadamard

/-!
# Squared-norm Hadamard three-lines estimate

The existing mathlib theorem is already Banach-valued.  This file records
the squared-norm form consumed by local second-moment interpolation.
-/

open Set Function Complex

namespace MathlibAux

/-- Banach-valued Hadamard three-lines with squared endpoint norms.  This is
the exact algebraic form needed when the target norm is an `L²` norm and the
available endpoint estimates are second moments. -/
theorem norm_sq_le_interp_of_mem_verticalClosedStrip'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {z : ℂ} {a b l u : ℝ}
    (hul : l < u)
    (hz : z ∈ HadamardThreeLines.verticalClosedStrip l u)
    (hd : DiffContOnCl ℂ f (HadamardThreeLines.verticalStrip l u))
    (hB : BddAbove
      ((norm ∘ f) '' HadamardThreeLines.verticalClosedStrip l u))
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : ∀ w ∈ re ⁻¹' {l}, ‖f w‖ ≤ a)
    (hb : ∀ w ∈ re ⁻¹' {u}, ‖f w‖ ≤ b) :
    ‖f z‖ ^ 2 ≤
      (a ^ 2) ^ (1 - (z.re - l) / (u - l)) *
        (b ^ 2) ^ ((z.re - l) / (u - l)) := by
  let p : ℝ := 1 - (z.re - l) / (u - l)
  let q : ℝ := (z.re - l) / (u - l)
  have hnorm : ‖f z‖ ≤ a ^ p * b ^ q := by
    simpa [p, q] using
      HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
        hul hz hd hB ha hb
  have hsquare : ‖f z‖ ^ 2 ≤ (a ^ p * b ^ q) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have haPow : (a ^ p) ^ 2 = (a ^ 2) ^ p := by
    rw [← Real.rpow_mul_natCast ha0 p 2, mul_comm,
      Real.rpow_natCast_mul ha0 2 p]
  have hbPow : (b ^ q) ^ 2 = (b ^ 2) ^ q := by
    rw [← Real.rpow_mul_natCast hb0 q 2, mul_comm,
      Real.rpow_natCast_mul hb0 2 q]
  calc
    ‖f z‖ ^ 2 ≤ (a ^ p * b ^ q) ^ 2 := hsquare
    _ = (a ^ p) ^ 2 * (b ^ q) ^ 2 := by ring
    _ = (a ^ 2) ^ p * (b ^ 2) ^ q := by rw [haPow, hbPow]
    _ = (a ^ 2) ^ (1 - (z.re - l) / (u - l)) *
        (b ^ 2) ^ ((z.re - l) / (u - l)) := by rfl

end MathlibAux
