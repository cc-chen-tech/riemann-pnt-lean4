import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import HardyTheorem.OscillatoryIntegral

/-!
# A smooth compact cutoff for the weighted Poisson step in the critical AFE

Titchmarsh's finite weighted Poisson transformation can be reached without
applying whole-line Poisson summation to the discontinuous hard cutoff.  This
file constructs a smooth plateau which is exactly one on `[x, N]` and is zero
outside `[x - 2, N + 2]`.  If `2 < x <= N`, multiplying it by the Mellin
weight `u ^ (-s)` gives a compactly supported smooth function, hence a
Schwartz function.  Mathlib's Poisson theorem then applies unconditionally.

The remaining AFE work is quantitative: estimate the two transition strips
and split the Fourier side into stationary and nonstationary modes.  No such
estimate is postulated here.
-/

noncomputable section

open Complex Filter Metric Set
open scoped FourierTransform SchwartzMap Topology

namespace HardyTheorem
namespace AFE

/-- A symmetric smooth bump centered at the midpoint of `x` and `N`.  Its
inner radius is `|N-x|/2+1` and its outer radius is `|N-x|/2+2`. -/
noncomputable def intervalPlateauBump (x N : ℝ) :
    ContDiffBump ((x + N) / 2) where
  rIn := |N - x| / 2 + 1
  rOut := |N - x| / 2 + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The plateau is identically one on the requested interval. -/
theorem intervalPlateauBump_eq_one {x N u : ℝ} (hxN : x ≤ N)
    (hu : u ∈ Icc x N) :
    intervalPlateauBump x N u = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [mem_closedBall, Real.dist_eq]
  change |u - (x + N) / 2| ≤ |N - x| / 2 + 1
  rw [abs_of_nonneg (sub_nonneg.mpr hxN), abs_le]
  constructor <;> linarith [hu.1, hu.2]

/-- The left transition strip has width at most two. -/
theorem intervalPlateauBump_eq_zero_of_le {x N u : ℝ} (hxN : x ≤ N)
    (hu : u ≤ x - 2) :
    intervalPlateauBump x N u = 0 := by
  apply ContDiffBump.zero_of_le_dist
  rw [Real.dist_eq]
  change |N - x| / 2 + 2 ≤ |u - (x + N) / 2|
  rw [abs_of_nonneg (sub_nonneg.mpr hxN), abs_of_nonpos]
  · linarith
  · linarith

/-- The right transition strip has width at most two. -/
theorem intervalPlateauBump_eq_zero_of_ge {x N u : ℝ} (hxN : x ≤ N)
    (hu : N + 2 ≤ u) :
    intervalPlateauBump x N u = 0 := by
  apply ContDiffBump.zero_of_le_dist
  rw [Real.dist_eq]
  change |N - x| / 2 + 2 ≤ |u - (x + N) / 2|
  rw [abs_of_nonneg (sub_nonneg.mpr hxN), abs_of_nonneg]
  · linarith
  · linarith

/-- The compactly supported Mellin weight used in the Poisson transformation.
`Real.log` is used in the definition so smoothness can be proved directly.
On the positive plateau this is exactly `(u : ℂ) ^ (-s)`. -/
noncomputable def weightedPoissonCutoff (s : ℂ) (x N : ℝ) (u : ℝ) : ℂ :=
  (intervalPlateauBump x N u : ℂ) *
    Complex.exp (-s * (Real.log u : ℂ))

theorem weightedPoissonCutoff_hasCompactSupport (s : ℂ) (x N : ℝ) :
    HasCompactSupport (weightedPoissonCutoff s x N) := by
  have hb : HasCompactSupport
      (fun u : ℝ => (intervalPlateauBump x N u : ℂ)) :=
    (intervalPlateauBump x N).hasCompactSupport.comp_left Complex.ofReal_zero
  exact hb.mul_right

/-- The only apparent singularity is at zero.  When `2 < x <= N`, the bump
vanishes on a neighborhood of zero, so the product is globally smooth. -/
theorem weightedPoissonCutoff_contDiff (s : ℂ) {x N : ℝ}
    (hx : 2 < x) (hxN : x ≤ N) :
    ContDiff ℝ (⊤ : ℕ∞) (weightedPoissonCutoff s x N) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u = 0
  · subst u
    apply (contDiffAt_const (x := (0 : ℝ)) (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < x - 2 by linarith)] with v hv
    simp [weightedPoissonCutoff,
      intervalPlateauBump_eq_zero_of_le hxN hv.le]
  · have hb : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun v : ℝ => (intervalPlateauBump x N v : ℂ)) u :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp u
        (intervalPlateauBump x N).contDiffAt
    have hlog : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : ℝ => (Real.log v : ℂ)) u :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp u
        (Real.contDiffAt_log.mpr hu)
    exact hb.mul ((contDiffAt_const.mul hlog).cexp)

/-- On the whole requested interval the smoothed summand is the original
Mellin summand. -/
theorem weightedPoissonCutoff_eq_cpow (s : ℂ) {x N u : ℝ}
    (hx : 0 < x) (hxN : x ≤ N) (hu : u ∈ Icc x N) :
    weightedPoissonCutoff s x N u = (u : ℂ) ^ (-s) := by
  have hu0 : 0 < u := hx.trans_le hu.1
  rw [weightedPoissonCutoff, intervalPlateauBump_eq_one hxN hu,
    ofReal_one, one_mul, Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hu0.ne')]
  rw [Complex.ofReal_log hu0.le]
  congr 1
  ring

/-- Pointwise size of the smoothed Mellin summand on the positive axis. -/
theorem norm_weightedPoissonCutoff_le_rpow (s : ℂ) (x N : ℝ) {u : ℝ}
    (hu : 0 < u) :
    ‖weightedPoissonCutoff s x N u‖ ≤ u ^ (-s.re) := by
  have hb0 : 0 ≤ intervalPlateauBump x N u :=
    (intervalPlateauBump x N).nonneg' u
  have hb1 : intervalPlateauBump x N u ≤ 1 :=
    (intervalPlateauBump x N).le_one
  rw [weightedPoissonCutoff, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hb0, Complex.norm_exp]
  have hexp :
      Real.exp ((-s * (Real.log u : ℂ)).re) = u ^ (-s.re) := by
    rw [Real.rpow_def_of_pos hu]
    congr 1
    simp
    ring
  rw [hexp]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hu.le _) hb1

/-- For integral endpoints, the smooth sum is supported on the finite integer
interval from `m-1` to `n+1`. -/
theorem weightedPoissonCutoff_tsum_eq_sum_Icc (s : ℂ) {m n : ℕ}
    (_hm : 2 < m) (hmn : m ≤ n) :
    (∑' k : ℤ, weightedPoissonCutoff s m n k) =
      ∑ k ∈ Finset.Icc ((m : ℤ) - 1) ((n : ℤ) + 1),
        weightedPoissonCutoff s m n k := by
  apply tsum_eq_sum
  intro k hk
  rw [Finset.mem_Icc] at hk
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  by_cases hkl : k < (m : ℤ) - 1
  · have hkZ : k ≤ (m : ℤ) - 2 := by omega
    have hkR : (k : ℝ) ≤ (m : ℝ) - 2 := by exact_mod_cast hkZ
    simp [weightedPoissonCutoff,
      intervalPlateauBump_eq_zero_of_le hmnR hkR]
  · have hlow : (m : ℤ) - 1 ≤ k := le_of_not_gt hkl
    have hku : (n : ℤ) + 1 < k := by
      apply lt_of_not_ge
      intro hkupper
      exact hk ⟨hlow, hkupper⟩
    have hkZ : (n : ℤ) + 2 ≤ k := by omega
    have hkR : (n : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hkZ
    simp [weightedPoissonCutoff,
      intervalPlateauBump_eq_zero_of_ge hmnR hkR]

/-- With integral endpoints there are exactly two smoothing terms, at
`m-1` and `n+1`; all integers from `m` through `n` retain their hard-cutoff
Mellin values. -/
theorem weightedPoissonCutoff_tsum_eq_boundary_add_core (s : ℂ) {m n : ℕ}
    (hm : 2 < m) (hmn : m ≤ n) :
    (∑' k : ℤ, weightedPoissonCutoff s m n k) =
      weightedPoissonCutoff s m n ((m : ℤ) - 1) +
        weightedPoissonCutoff s m n ((n : ℤ) + 1) +
          ∑ k ∈ Finset.Icc (m : ℤ) n, (k : ℂ) ^ (-s) := by
  rw [weightedPoissonCutoff_tsum_eq_sum_Icc s hm hmn]
  have hinterval :
      Finset.Icc ((m : ℤ) - 1) ((n : ℤ) + 1) =
        insert ((m : ℤ) - 1)
          (insert ((n : ℤ) + 1) (Finset.Icc (m : ℤ) n)) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hinterval]
  have hleft : (m : ℤ) - 1 ∉ insert ((n : ℤ) + 1) (Finset.Icc (m : ℤ) n) := by
    simp only [Finset.mem_insert, Finset.mem_Icc, not_or, not_and_or, not_le]
    constructor
    · omega
    · exact Or.inl (by omega)
  have hright : (n : ℤ) + 1 ∉ Finset.Icc (m : ℤ) n := by
    simp
  rw [Finset.sum_insert hleft, Finset.sum_insert hright]
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, Int.cast_add]
  rw [← add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  apply weightedPoissonCutoff_eq_cpow s
  · exact_mod_cast (show 0 < m by omega)
  · exact_mod_cast hmn
  · constructor
    · exact_mod_cast hk.1
    · exact_mod_cast hk.2

/-- Real phase of the `k`-th Fourier transform of the Mellin weight at
`s = sigma + I*t`, with mathlib's `exp (-2*pi*I*k*u)` convention. -/
noncomputable def weightedPoissonPhase (t : ℝ) (k : ℤ) (u : ℝ) : ℝ :=
  -t * Real.log u - 2 * Real.pi * (k : ℝ) * u

/-- Our Fourier-sign convention is the existing Mellin--Fourier phase with
the integer frequency negated. -/
theorem weightedPoissonPhase_eq_fourierMellinPhase_neg
    (t : ℝ) (k : ℤ) (u : ℝ) :
    weightedPoissonPhase t k u =
      OscillatoryIntegral.fourierMellinPhase (-k) t u := by
  simp [weightedPoissonPhase, OscillatoryIntegral.fourierMellinPhase]
  ring

/-- First derivative of the Poisson phase away from the logarithmic
singularity. -/
theorem weightedPoissonPhase_hasDerivAt
    (t : ℝ) (k : ℤ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (weightedPoissonPhase t k)
      (-t / u - 2 * Real.pi * (k : ℝ)) u := by
  unfold weightedPoissonPhase
  simpa [div_eq_mul_inv, Pi.sub_def, Pi.mul_def] using
    (((Real.hasDerivAt_log hu).const_mul (-t)).sub
      ((hasDerivAt_id u).const_mul (2 * Real.pi * (k : ℝ))))

theorem deriv_weightedPoissonPhase
    (t : ℝ) (k : ℤ) {u : ℝ} (hu : u ≠ 0) :
    deriv (weightedPoissonPhase t k) u =
      -t / u - 2 * Real.pi * (k : ℝ) :=
  (weightedPoissonPhase_hasDerivAt t k hu).deriv

/-- For frequency `-m`, the only possible stationary point solves
`2*pi*m=t/u`. -/
theorem deriv_weightedPoissonPhase_neg_nat
    (t : ℝ) (m : ℕ) {u : ℝ} (hu : u ≠ 0) :
    deriv (weightedPoissonPhase t (-(m : ℤ))) u =
      2 * Real.pi * (m : ℝ) - t / u := by
  rw [deriv_weightedPoissonPhase t (-(m : ℤ)) hu]
  push_cast
  ring

/-- A negative frequency has exactly one positive candidate stationary
point.  This is the source of the dual Dirichlet polynomial in the AFE. -/
theorem deriv_weightedPoissonPhase_neg_nat_eq_zero_iff
    {t u : ℝ} {m : ℕ} (ht : 0 < t) (hu : 0 < u) (hm : 0 < m) :
    deriv (weightedPoissonPhase t (-(m : ℤ))) u = 0 ↔
      u = t / (2 * Real.pi * (m : ℝ)) := by
  rw [deriv_weightedPoissonPhase_neg_nat t m hu.ne']
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hden : 0 < 2 * Real.pi * (m : ℝ) :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) hmR
  constructor
  · intro h
    apply (eq_div_iff hden.ne').2
    field_simp [hu.ne'] at h
    nlinarith
  · intro h
    rw [h]
    field_simp [hden.ne', ht.ne']
    ring

/-- Frequencies `k >= 0` are strictly nonstationary when `t,u>0`; hence all
stationary modes lie on the negative Fourier side. -/
theorem deriv_weightedPoissonPhase_neg_of_nonneg
    {t u : ℝ} {k : ℤ} (ht : 0 < t) (hu : 0 < u) (hk : 0 ≤ k) :
    deriv (weightedPoissonPhase t k) u < 0 := by
  rw [deriv_weightedPoissonPhase t k hu.ne']
  have hkR : 0 ≤ (k : ℝ) := by exact_mod_cast hk
  have hfirst : -t / u < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos ht) hu
  have hfreq : 0 ≤ 2 * Real.pi * (k : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hkR
  exact lt_of_le_of_lt (sub_le_self _ hfreq) hfirst

/-- Exact amplitude--phase normalization of a Fourier summand on the
positive axis. -/
theorem weightedPoissonCutoff_fourierIntegrand_eq
    (sigma t x N u : ℝ) (k : ℤ) (hu : 0 < u) :
    Complex.exp ((-2 * Real.pi * u * (k : ℝ) : ℝ) * I) •
        weightedPoissonCutoff ((sigma : ℂ) + I * t) x N u =
      (intervalPlateauBump x N u * u ^ (-sigma)) •
        Complex.exp (I * weightedPoissonPhase t k u) := by
  rw [weightedPoissonCutoff, Real.rpow_def_of_pos hu]
  simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_exp, Complex.ofReal_neg]
  let A : ℂ :=
    Complex.exp (-(2 : ℂ) * (Real.pi : ℂ) * (u : ℂ) * (k : ℂ) * I)
  let B : ℂ :=
    Complex.exp (-((sigma : ℂ) + I * t) * (Real.log u : ℂ))
  let C : ℂ := Complex.exp ((Real.log u : ℂ) * (-sigma : ℂ))
  let D : ℂ := Complex.exp (I * (weightedPoissonPhase t k u : ℂ))
  let b : ℂ := intervalPlateauBump x N u
  change A * (b * B) = b * C * D
  calc
    A * (b * B) = b * (A * B) := by ring
    _ = b * (C * D) := by
      congr 1
      dsimp [A, B, C, D]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      apply Complex.ext <;> simp [weightedPoissonPhase] <;> ring
    _ = b * C * D := by ring

/-- The Fourier transform is supported on the same constant-width enlarged
interval as the plateau.  This fixes the Fourier sign and `2*pi`
normalization before stationary modes are extracted. -/
theorem fourier_weightedPoissonCutoff_eq_intervalIntegral
    (s : ℂ) {x N : ℝ} (hxN : x ≤ N) (k : ℤ) :
    𝓕 (weightedPoissonCutoff s x N) k =
      ∫ u in (x - 2)..(N + 2),
        Complex.exp ((-2 * Real.pi * u * (k : ℝ) : ℝ) * I) •
          weightedPoissonCutoff s x N u := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply (intervalIntegral.integral_eq_integral_of_support_subset ?_).symm
  intro u hu
  have hmnR : x ≤ N := hxN
  have hleft : x - 2 < u := by
    apply lt_of_not_ge
    intro hul
    apply hu
    simp [weightedPoissonCutoff,
      intervalPlateauBump_eq_zero_of_le hmnR hul]
  have hright : u < N + 2 := by
    apply lt_of_not_ge
    intro hur
    apply hu
    simp [weightedPoissonCutoff,
      intervalPlateauBump_eq_zero_of_ge hmnR hur]
  exact ⟨hleft, hright.le⟩

/-- Fourier transform in the positive-weight oscillatory form used by the
existing first- and second-derivative integral estimates. -/
theorem fourier_weightedPoissonCutoff_eq_phaseIntegral
    (sigma t : ℝ) {x N : ℝ} (hx : 2 < x) (hxN : x ≤ N) (k : ℤ) :
    𝓕 (weightedPoissonCutoff ((sigma : ℂ) + I * t) x N) k =
      ∫ u in (x - 2)..(N + 2),
        (intervalPlateauBump x N u * u ^ (-sigma)) •
          Complex.exp (I * weightedPoissonPhase t k u) := by
  rw [fourier_weightedPoissonCutoff_eq_intervalIntegral _ hxN]
  apply intervalIntegral.integral_congr
  intro u hu
  have hbounds : u ∈ Icc (x - 2) (N + 2) := by
    have horder : x - 2 ≤ N + 2 := by linarith
    rw [uIcc_of_le horder] at hu
    exact hu
  apply weightedPoissonCutoff_fourierIntegrand_eq
  linarith [hbounds.1]

/-- Whole-line Poisson summation for the smoothed Mellin cutoff.  This is an
actual theorem obtained from the Schwartz Poisson formula, not an analytic
interface or an axiom. -/
theorem weightedPoissonCutoff_tsum_eq_fourier_tsum (s : ℂ) {x N : ℝ}
    (hx : 2 < x) (hxN : x ≤ N) :
    (∑' n : ℤ, weightedPoissonCutoff s x N n) =
      ∑' n : ℤ, 𝓕 (weightedPoissonCutoff s x N) n := by
  let F : 𝓢(ℝ, ℂ) :=
    (weightedPoissonCutoff_hasCompactSupport s x N).toSchwartzMap
      (weightedPoissonCutoff_contDiff s hx hxN)
  have h := SchwartzMap.tsum_eq_tsum_fourier F 0
  simp_rw [SchwartzMap.fourier_coe] at h
  change (∑' n : ℤ, F n) = ∑' n : ℤ, 𝓕 (F : ℝ → ℂ) n
  simpa using h

end AFE
end HardyTheorem
