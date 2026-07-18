import HardyTheorem.FirstZetaApproximation

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- A Carlson-ready zeta approximation in a fixed strip.  When the cutoff is
comparable to the height, the pole term in Abel's formula has the same
`x ^ (-Re s)` size as the floor-error remainder and can be absorbed into it. -/
theorem exists_riemannZeta_carlson_approximation :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℂ) (x : ℝ),
      (1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 → s ≠ 1 → 2 ≤ x →
        |s.im| ≤ x / 2 → x ≤ 2 * |s.im| →
          ∃ R : ℂ,
            riemannZeta s =
              (∑ n ∈ Finset.Icc 1 (Nat.floor x), 1 / (n : ℂ) ^ s) + R ∧
            ‖R‖ ≤ C * x ^ (-s.re) := by
  obtain ⟨A, hA, hbase⟩ :=
    HardyTheorem.exists_riemannZeta_first_approximation
  refine ⟨A + 2, by positivity, ?_⟩
  intro s x hs_lower hs_upper hs1 hx him_upper him_lower
  have hs_quarter : (1 / 4 : ℝ) ≤ s.re := by linarith
  have hs_two : s.re ≤ 2 := hs_upper.trans (by norm_num)
  rcases hbase s x hs_quarter hs_two hs1 (by linarith) him_upper with
    ⟨R0, heq, hR0⟩
  let P : ℂ := (x : ℂ) ^ (1 - s) / (s - 1)
  refine ⟨P + R0, ?_, ?_⟩
  · dsimp [P]
    rw [heq]
    ring
  · have hxpos : 0 < x := by linarith
    have hs_sub_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hden : x / 2 ≤ ‖s - 1‖ := by
      calc
        x / 2 ≤ |s.im| := by linarith
        _ = |(s - 1).im| := by simp
        _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    have hpow_nonneg : 0 ≤ x ^ (1 - s.re) :=
      Real.rpow_nonneg hxpos.le _
    have hP : ‖P‖ ≤ 2 * x ^ (-s.re) := by
      dsimp [P]
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      calc
        x ^ (1 - s.re) / ‖s - 1‖ ≤
            x ^ (1 - s.re) / (x / 2) :=
          div_le_div_of_nonneg_left hpow_nonneg (by positivity) hden
        _ = 2 * x ^ (-s.re) := by
          rw [show 1 - s.re = 1 + (-s.re) by ring,
            Real.rpow_add hxpos, Real.rpow_one]
          field_simp
    calc
      ‖P + R0‖ ≤ ‖P‖ + ‖R0‖ := norm_add_le _ _
      _ ≤ 2 * x ^ (-s.re) + A * x ^ (-s.re) := add_le_add hP hR0
      _ = (A + 2) * x ^ (-s.re) := by ring

end CarlsonZeroDensity
end PrimeNumberTheorem
