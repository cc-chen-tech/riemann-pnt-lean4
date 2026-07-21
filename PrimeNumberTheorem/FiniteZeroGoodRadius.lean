import ZeroFreeRegion.MeromorphicAux

open Complex

namespace PrimeNumberTheorem

/-- A finite cover of the zeros in a closed disk yields a smaller positive
circle which is quantitatively separated from the covered points and has no
zeros of the function. -/
theorem exists_good_radius_avoiding_covered_finset_zeros
    {f : ℂ → ℂ} (zeros : Finset ℂ) (c : ℂ)
    {a q b : ℝ} (ha : 0 < a) (haq : a < q) (hqb : q < b)
    (hcover : ∀ z ∈ Metric.closedBall c b, f z = 0 → z ∈ zeros) :
    ∃ r : ℝ,
      0 < r ∧ r ∈ Set.Icc a q ∧
      (∀ z ∈ Metric.sphere c r, ∀ ρ ∈ zeros,
        (q - a) / (4 * (((zeros.image (dist c)).card : ℝ) + 1)) ≤ dist z ρ) ∧
      (∀ z ∈ Metric.sphere c r, z ∈ Metric.closedBall c b) ∧
      ∀ z ∈ Metric.sphere c r, f z ≠ 0 := by
  classical
  rcases ZeroFreeRegion.exists_radius_separated_from_finset_norm_sub zeros c haq with
    ⟨r, hr, hradial⟩
  have hsphere_sep : ∀ z ∈ Metric.sphere c r, ∀ ρ ∈ zeros,
      (q - a) / (4 * (((zeros.image (dist c)).card : ℝ) + 1)) ≤ dist z ρ := by
    intro z hz ρ hρ
    have hzrad : dist c z = r := by
      calc
        dist c z = dist z c := dist_comm _ _
        _ = r := Metric.mem_sphere.mp hz
    have hmetric : |dist c z - dist c ρ| ≤ dist z ρ := by
      simpa [Real.dist_eq] using dist_dist_dist_le_right c z ρ
    rw [hzrad] at hmetric
    exact (hradial ρ hρ).trans hmetric
  have hsphere_closed : ∀ z ∈ Metric.sphere c r, z ∈ Metric.closedBall c b := by
    intro z hz
    have hzrad : dist c z = r := by
      calc
        dist c z = dist z c := dist_comm _ _
        _ = r := Metric.mem_sphere.mp hz
    rw [Metric.mem_closedBall, _root_.dist_comm z c, hzrad]
    exact hr.2.trans hqb.le
  refine ⟨r, ha.trans_le hr.1, hr, hsphere_sep, hsphere_closed, ?_⟩
  intro z hz hfz
  have hzmem : z ∈ zeros := hcover z (hsphere_closed z hz) hfz
  have hsep := hsphere_sep z hz z hzmem
  have hsep_pos : 0 <
      (q - a) / (4 * (((zeros.image (dist c)).card : ℝ) + 1)) := by
    exact div_pos (sub_pos.mpr haq) (mul_pos (by norm_num) (by positivity))
  simpa using hsep_pos.trans_le hsep

end PrimeNumberTheorem
