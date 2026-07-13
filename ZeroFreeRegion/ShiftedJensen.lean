import ZeroFreeRegion.PhragmenLindelofZeta

open Complex Filter Set Topology
open scoped Topology

namespace ZeroFreeRegion

/-- The polynomial zeta-growth estimate on the enlarged Jensen disk centered
at `2 + I * t`. -/
lemma norm_riemannZeta_le_large_jensen_closedBall
    {C r t : ℝ}
    (hC : 0 ≤ C)
    (hpoly : ∀ s : ℂ, s.re ∈ Icc (0 : ℝ) 4 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ 4)
    (hr : r ≤ 39 / 20) (ht : 4 ≤ |t|)
    {z : ℂ} (hz : z ∈ Metric.closedBall ((2 : ℂ) + I * t) r) :
    ‖riemannZeta z‖ ≤ max C 1 * (|t| + 5) ^ 4 := by
  have hdist : ‖z - ((2 : ℂ) + I * t)‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hre_abs : |z.re - 2| ≤ r := by
    have := Complex.abs_re_le_norm (z - ((2 : ℂ) + I * t))
    simpa using this.trans hdist
  have him_abs : |z.im - t| ≤ r := by
    have := Complex.abs_im_le_norm (z - ((2 : ℂ) + I * t))
    simpa using this.trans hdist
  have hzre : z.re ∈ Icc (0 : ℝ) 4 := by
    constructor <;> rw [abs_le] at hre_abs <;> linarith
  have hzim_lower : 1 ≤ |z.im| := by
    have htri : |t| ≤ |z.im - t| + |z.im| := by
      calc
        |t| = |(t - z.im) + z.im| := by ring_nf
        _ ≤ |t - z.im| + |z.im| := abs_add_le _ _
        _ = |z.im - t| + |z.im| := by rw [abs_sub_comm]
    linarith
  have hzim_upper : |z.im| ≤ |t| + r := by
    calc
      |z.im| = |(z.im - t) + t| := by ring_nf
      _ ≤ |z.im - t| + |t| := abs_add_le _ _
      _ ≤ |t| + r := by linarith
  have hbase : |z.im| + 3 ≤ |t| + 5 := by linarith
  calc
    ‖riemannZeta z‖ ≤ C * (|z.im| + 3) ^ 4 := hpoly z hzre hzim_lower
    _ ≤ C * (|t| + 5) ^ 4 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hbase 4) hC
    _ ≤ max C 1 * (|t| + 5) ^ 4 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by positivity) 4)

/-- Logarithmic form of the enlarged Jensen-disk growth bound. -/
lemma log_norm_riemannZeta_le_large_jensen_closedBall
    {C r t : ℝ}
    (hC : 0 ≤ C)
    (hpoly : ∀ s : ℂ, s.re ∈ Icc (0 : ℝ) 4 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ 4)
    (hr : r ≤ 39 / 20) (ht : 4 ≤ |t|)
    {z : ℂ} (hz : z ∈ Metric.closedBall ((2 : ℂ) + I * t) r) :
    Real.log ‖riemannZeta z‖ ≤
      Real.log (max C 1) + 4 * Real.log (|t| + 5) := by
  have hnorm := norm_riemannZeta_le_large_jensen_closedBall
    hC hpoly hr ht hz
  have hA : 1 ≤ max C 1 := le_max_right _ _
  have hApos : 0 < max C 1 := zero_lt_one.trans_le hA
  have hxpos : 0 < |t| + 5 := by positivity
  have hMpos : 0 < max C 1 * (|t| + 5) ^ 4 :=
    mul_pos hApos (pow_pos hxpos 4)
  by_cases hzeta : ‖riemannZeta z‖ = 0
  · rw [hzeta, Real.log_zero]
    have hlogA : 0 ≤ Real.log (max C 1) := Real.log_nonneg hA
    have hlogx : 0 ≤ Real.log (|t| + 5) :=
      Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  · have hzeta_pos : 0 < ‖riemannZeta z‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzeta)
    have hlog := Real.log_le_log hzeta_pos hnorm
    rw [Real.log_mul hApos.ne' (pow_ne_zero 4 hxpos.ne'), Real.log_pow] at hlog
    norm_num at hlog ⊢
    exact hlog

/-- The enlarged Jensen disk has zeta divisor mass
`O(1 + log (|t| + 5))`. -/
theorem exists_finsum_divisor_riemannZeta_large_disk_log_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 4 ≤ |t| →
      (∑ᶠ u, (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + I * t) (19 / 10 : ℝ)) u : ℝ)) ≤
          B * (1 + Real.log (|t| + 5)) := by
  rcases exists_norm_riemannZeta_le_polynomial_on_zero_four with
    ⟨C, hC, hpoly⟩
  let A : ℝ := max C 1
  let c0 : ℝ := Real.log A + Real.log 3
  let D : ℝ := Real.log ((39 / 20 : ℝ) / (19 / 10 : ℝ))
  let E : ℝ := D⁻¹
  let B : ℝ := (c0 + 4) * E
  have hA : 1 ≤ A := le_max_right _ _
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    exact add_nonneg (Real.log_nonneg hA) (Real.log_nonneg (by norm_num))
  have hD : 0 < D := by
    dsimp [D]
    apply Real.log_pos
    norm_num
  have hE : 0 < E := by simp [E, hD]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro t ht
  let M : ℝ := A * (|t| + 5) ^ 4
  let L : ℝ := Real.log (|t| + 5)
  have hx : 1 ≤ |t| + 5 := by linarith [abs_nonneg t]
  have hxpos : 0 < |t| + 5 := zero_lt_one.trans_le hx
  have hL : 0 ≤ L := Real.log_nonneg hx
  have hM : 1 ≤ M := by
    have hxpow : 1 ≤ (|t| + 5) ^ 4 := one_le_pow₀ hx
    exact one_le_mul_of_one_le_of_one_le hA hxpow
  have houter : ∀ w : ℂ,
      w ∈ Metric.sphere ((2 : ℂ) + I * t) (39 / 20 : ℝ) →
        ‖riemannZeta w‖ ≤ M := by
    intro w hw
    have hwc : w ∈ Metric.closedBall
        ((2 : ℂ) + I * t) (39 / 20 : ℝ) :=
      Metric.sphere_subset_closedBall hw
    simpa [A, M] using
      norm_riemannZeta_le_large_jensen_closedBall hC hpoly (by norm_num) ht hwc
  have hmass := finsum_divisor_riemannZeta_closedBall_le_log_bound_div
    (b := (19 / 10 : ℝ)) (R := (39 / 20 : ℝ)) (t := t) (M := M)
    (by norm_num) (by norm_num) (by linarith) hM houter
  have hlogM : Real.log M + Real.log 3 = c0 + 4 * L := by
    dsimp [M, c0]
    rw [Real.log_mul hApos.ne' (pow_ne_zero 4 hxpos.ne'), Real.log_pow]
    simp [L]
    ring
  rw [hlogM] at hmass
  have hdiv : (c0 + 4 * L) / D = (c0 + 4 * L) * E := by
    simp [E, div_eq_mul_inv]
  rw [hdiv] at hmass
  apply hmass.trans
  dsimp [B]
  calc
    (c0 + 4 * L) * E ≤
        (c0 + 4 * L) * E + E * (4 + c0 * L) :=
      le_add_of_nonneg_right (mul_nonneg hE.le
        (add_nonneg (by norm_num) (mul_nonneg hc0 hL)))
    _ = (c0 + 4) * E * (1 + Real.log (|t| + 5)) := by
      dsimp [L]
      ring

/-- The radius-`7/5` disk centered at `3/2 + I*t` lies inside the enlarged
radius-`19/10` disk centered at `2 + I*t`; its zeta divisor mass is therefore
controlled by the latter disk at high height. -/
lemma finsum_divisor_riemannZeta_shifted_closedBall_le_large_disk
    {t : ℝ} (ht : 4 ≤ |t|) :
    (∑ᶠ u, (MeromorphicOn.divisor riemannZeta
      (Metric.closedBall ((3 / 2 : ℂ) + I * t) (7 / 5 : ℝ)) u : ℝ)) ≤
    ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
      (Metric.closedBall ((2 : ℂ) + I * t) (19 / 10 : ℝ)) u : ℝ) := by
  classical
  let cs : ℂ := (3 / 2 : ℂ) + I * t
  let cb : ℂ := (2 : ℂ) + I * t
  let Ds := MeromorphicOn.divisor riemannZeta
    (Metric.closedBall cs (7 / 5 : ℝ))
  let Db := MeromorphicOn.divisor riemannZeta
    (Metric.closedBall cb (19 / 10 : ℝ))
  have hcenters : dist cs cb = (1 / 2 : ℝ) := by
    simp [cs, cb, dist_eq_norm, Complex.norm_def]
    norm_num
  have hball : Metric.closedBall cs (7 / 5 : ℝ) ⊆
      Metric.closedBall cb (19 / 10 : ℝ) := by
    intro u hu
    rw [Metric.mem_closedBall] at hu ⊢
    calc
      dist u cb ≤ dist u cs + dist cs cb := dist_triangle _ _ _
      _ ≤ (7 / 5 : ℝ) + 1 / 2 := by rw [hcenters]; linarith
      _ = 19 / 10 := by norm_num
  have havoid : ∀ z : ℂ,
      z ∈ Metric.closedBall cb (19 / 10 : ℝ) → z ≠ 1 := by
    intro z hz
    exact closedBall_sigma_it_ne_one_of_height_add_le
      (z := z) (σ := 2) (t := t) (R := (19 / 10 : ℝ))
      (H := |t| - 19 / 10)
      (by simpa [cb] using hz) (by linarith) (by linarith)
  have hDb_nonneg : 0 ≤ Db := by
    dsimp [Db]
    exact divisor_riemannZeta_closedBall_nonneg havoid
  have hDs_finite : Ds.support.Finite := by
    dsimp [Ds]
    exact (MeromorphicOn.divisor riemannZeta
      (Metric.closedBall cs (7 / 5 : ℝ))).finiteSupport
        (isCompact_closedBall cs (7 / 5 : ℝ))
  have hDb_finite : Db.support.Finite := by
    dsimp [Db]
    exact (MeromorphicOn.divisor riemannZeta
      (Metric.closedBall cb (19 / 10 : ℝ))).finiteSupport
        (isCompact_closedBall cb (19 / 10 : ℝ))
  have hlocal : ∀ u ∈ Ds.support, Ds u = Db u := by
    intro u hu
    have hus : u ∈ Metric.closedBall cs (7 / 5 : ℝ) :=
      Ds.supportWithinDomain hu
    have hub := hball hus
    dsimp [Ds, Db]
    rw [MeromorphicOn.divisor_apply
        (meromorphicOn_riemannZeta_closedBall cs (7 / 5 : ℝ)) hus,
      MeromorphicOn.divisor_apply
        (meromorphicOn_riemannZeta_closedBall cb (19 / 10 : ℝ)) hub]
  have hsupport : hDs_finite.toFinset ⊆ hDb_finite.toFinset := by
    intro u hu
    apply hDb_finite.mem_toFinset.mpr
    have huDs : u ∈ Ds.support := hDs_finite.mem_toFinset.mp hu
    have hneDs : Ds u ≠ 0 := by simpa [Function.mem_support] using huDs
    have hneDb : Db u ≠ 0 := by rwa [← hlocal u huDs]
    simpa [Function.mem_support] using hneDb
  have hDs_cast_support : (fun u : ℂ => (Ds u : ℝ)).support ⊆
      hDs_finite.toFinset := by
    intro u hu
    apply hDs_finite.mem_toFinset.mpr
    simpa [Function.mem_support] using hu
  have hDb_cast_support : (fun u : ℂ => (Db u : ℝ)).support ⊆
      hDb_finite.toFinset := by
    intro u hu
    apply hDb_finite.mem_toFinset.mpr
    simpa [Function.mem_support] using hu
  change (∑ᶠ u, (Ds u : ℝ)) ≤ ∑ᶠ u, (Db u : ℝ)
  rw [finsum_eq_sum_of_support_subset _ hDs_cast_support,
    finsum_eq_sum_of_support_subset _ hDb_cast_support]
  calc
    ∑ u ∈ hDs_finite.toFinset, (Ds u : ℝ) =
        ∑ u ∈ hDs_finite.toFinset, (Db u : ℝ) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact_mod_cast hlocal u (hDs_finite.mem_toFinset.mp hu)
    _ ≤ ∑ u ∈ hDb_finite.toFinset, (Db u : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsupport (by
        intro u _hu _hu_not_small
        exact_mod_cast hDb_nonneg u)

/-- The shifted radius-`7/5` divisor mass is itself
`O(1 + log (|t| + 5))`. -/
theorem exists_finsum_divisor_riemannZeta_shifted_disk_log_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 4 ≤ |t| →
      (∑ᶠ u, (MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((3 / 2 : ℂ) + I * t) (7 / 5 : ℝ)) u : ℝ)) ≤
          B * (1 + Real.log (|t| + 5)) := by
  rcases exists_finsum_divisor_riemannZeta_large_disk_log_bound with
    ⟨B, hB, hlarge⟩
  refine ⟨B, hB, ?_⟩
  intro t ht
  exact (finsum_divisor_riemannZeta_shifted_closedBall_le_large_disk ht).trans
    (hlarge t ht)

/-- On the retained radius-`1` disk centered at `3/2 + I*t`, the logarithmic
derivative after removing the radius-`7/5` zeta divisor is
`O(1 + log (|t| + 5))`. -/
theorem exists_shifted_disk_regularized_logDeriv_riemannZeta_log_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 4 ≤ |t| →
      ∀ z ∈ Metric.closedBall ((3 / 2 : ℂ) + I * t) 1,
        riemannZeta z ≠ 0 →
        ‖logDeriv riemannZeta z -
            ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
              (Metric.closedBall ((3 / 2 : ℂ) + I * t) (7 / 5 : ℝ)) u : ℂ) *
                (z - u)⁻¹‖ ≤
          B * (1 + Real.log (|t| + 5)) := by
  rcases exists_norm_riemannZeta_le_polynomial_on_zero_four with
    ⟨C, hC, hpoly⟩
  rcases exists_finsum_divisor_riemannZeta_shifted_disk_log_bound with
    ⟨Bm, hBm, hmass_bound⟩
  let A : ℝ := max C 1
  let c0 : ℝ := Real.log A + Real.log 3
  let m : ℝ := max c0 1
  let B : ℝ := 384 * m + 1536 + (8 / 3 : ℝ) * Bm
  have hA : 1 ≤ A := le_max_right _ _
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    exact add_nonneg (Real.log_nonneg hA) (Real.log_nonneg (by norm_num))
  have hm : 0 ≤ m := hc0.trans (le_max_left _ _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro t ht z hz hzeta
  let c : ℂ := (3 / 2 : ℂ) + I * t
  let D := MeromorphicOn.divisor riemannZeta
    (Metric.closedBall c (7 / 5 : ℝ))
  let L : ℝ := Real.log (|t| + 5)
  let K : ℝ := Real.log A + 4 * L
  have hx : 1 ≤ |t| + 5 := by linarith [abs_nonneg t]
  have hL : 0 ≤ L := Real.log_nonneg hx
  have havoid : ∀ w : ℂ,
      w ∈ Metric.closedBall c (7 / 5 : ℝ) → w ≠ 1 := by
    intro w hw
    exact closedBall_sigma_it_ne_one_of_height_add_le
      (z := w) (σ := (3 / 2 : ℝ)) (t := t) (R := (7 / 5 : ℝ))
      (H := |t| - 7 / 5)
      (by simpa [c] using hw) (by linarith) (by linarith)
  rcases
      exists_good_radius_separated_from_riemannZeta_zeros_closedBall_strictly_inside
        (c := c) (a := (11 / 8 : ℝ)) (q := (111 / 80 : ℝ))
        (b := (7 / 5 : ℝ)) (by norm_num) (by norm_num) (by norm_num) havoid with
    ⟨_zeros, r, _hzeros, hrpos, hr, _hsep, hsphere_ne⟩
  rcases exists_analytic_nonzero_factorization_riemannZeta_closedBall havoid with
    ⟨g, hg, hgne, hfactor⟩
  have hcenters : dist c ((2 : ℂ) + I * t) = (1 / 2 : ℝ) := by
    simp [c, dist_eq_norm, Complex.norm_def]
    norm_num
  have hsphere_log : ∀ w ∈ Metric.sphere c r,
      Real.log ‖riemannZeta w‖ ≤ K := by
    intro w hw
    have hw_closed : w ∈ Metric.closedBall c r :=
      Metric.sphere_subset_closedBall hw
    have hw_q : w ∈ Metric.closedBall c (111 / 80 : ℝ) :=
      Metric.closedBall_subset_closedBall hr.2 hw_closed
    have hw_large : w ∈ Metric.closedBall
        ((2 : ℂ) + I * t) (39 / 20 : ℝ) := by
      rw [Metric.mem_closedBall] at hw_q ⊢
      calc
        dist w ((2 : ℂ) + I * t) ≤
            dist w c + dist c ((2 : ℂ) + I * t) := dist_triangle _ _ _
        _ ≤ (111 / 80 : ℝ) + 1 / 2 := by rw [hcenters]; linarith
        _ ≤ 39 / 20 := by norm_num
    simpa [A, K, L] using
      log_norm_riemannZeta_le_large_jensen_closedBall
        hC hpoly (by norm_num) ht hw_large
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact divisor_riemannZeta_closedBall_nonneg havoid
  have hmass_nonneg : 0 ≤ ∑ᶠ u, (D u : ℝ) := by
    apply finsum_nonneg
    intro u
    exact_mod_cast hD_nonneg u
  have hmass : (∑ᶠ u, (D u : ℝ)) ≤ Bm * (1 + L) := by
    simpa [c, D, L] using hmass_bound t ht
  have hdr : (1 : ℝ) < r := (by norm_num : (1 : ℝ) < 11 / 8).trans_le hr.1
  have hrb : r < (7 / 5 : ℝ) := hr.2.trans_lt (by norm_num)
  have hzdist : dist z c ≤ 1 := by
    simpa [c, Metric.mem_closedBall] using hz
  have hzrho : dist z c + (1 / 64 : ℝ) ≤ 3 * r / 4 := by
    nlinarith [hr.1]
  have hlocal :=
    norm_regularized_logDeriv_riemannZeta_le_mixedCanonical_bound_three_quarters
      (c := c) (z := z) (d := (1 : ℝ)) (r := r) (b := (7 / 5 : ℝ))
      (B := K) (ρ := (1 / 64 : ℝ)) (g := g)
      (by norm_num [c]) (by norm_num) hdr hrb (by norm_num)
      havoid hg hgne hfactor hsphere_ne hsphere_log
      (by simpa [c] using hz) hzeta hzrho
  have had : 0 < (11 / 8 : ℝ) - 1 := by norm_num
  have hradial : (∑ᶠ u, (D u : ℝ)) / (r - 1) ≤
      (∑ᶠ u, (D u : ℝ)) / ((11 / 8 : ℝ) - 1) :=
    div_le_div_of_nonneg_left hmass_nonneg had
      (sub_le_sub_right hr.1 1)
  have hmass_div : (∑ᶠ u, (D u : ℝ)) / ((11 / 8 : ℝ) - 1) ≤
      (Bm * (1 + L)) / ((11 / 8 : ℝ) - 1) :=
    div_le_div_of_nonneg_right hmass had.le
  have hbound :
      ‖logDeriv riemannZeta z -
          ∑ᶠ u, (D u : ℂ) * (z - u)⁻¹‖ ≤
        6 * max (K + Real.log 3) 1 / (1 / 64 : ℝ) +
          (Bm * (1 + L)) / ((11 / 8 : ℝ) - 1) := by
    simpa [D] using
      hlocal.trans (add_le_add_right (hradial.trans hmass_div) _)
  have hmax : max (c0 + 4 * L) 1 ≤ m + 4 * L := by
    apply max_le
    · dsimp [m]
      linarith [le_max_left c0 (1 : ℝ)]
    · have : 1 ≤ m := le_max_right c0 (1 : ℝ)
      linarith
  have hrewrite :
      6 * max (K + Real.log 3) 1 / (1 / 64 : ℝ) +
          (Bm * (1 + L)) / ((11 / 8 : ℝ) - 1) =
        384 * max (c0 + 4 * L) 1 +
          (8 / 3 : ℝ) * Bm * (1 + L) := by
    dsimp [K, c0]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    norm_num
    ring
  rw [hrewrite] at hbound
  apply hbound.trans
  dsimp [B]
  nlinarith

end ZeroFreeRegion
