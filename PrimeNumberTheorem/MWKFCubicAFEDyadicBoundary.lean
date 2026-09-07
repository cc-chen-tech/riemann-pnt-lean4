import PrimeNumberTheorem.MWKFCubicAFEDyadicReassembly

open Set Filter Complex
open scoped ContDiff Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The exact continuous lower-boundary weight in dyadic recombination

The dyadic windows have mass one on x >= 1, but not on the whole positive
axis. Their mass on every real input is explicitly recorded here. This
weight must survive in any zero-mode integral; pointwise reassembly alone
does not justify exchanging an infinite dyadic sum with an integral.
-/

noncomputable def cubicAFEDyadicLowerWeight (x : ℝ) : ℝ :=
  1 - Real.smoothTransition (2 - 2 * x)

theorem cubicAFEDyadicLowerWeight_nonneg (x : ℝ) : 0 ≤ cubicAFEDyadicLowerWeight x :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

theorem cubicAFEDyadicLowerWeight_le_one (x : ℝ) : cubicAFEDyadicLowerWeight x ≤ 1 :=
  sub_le_self _ (Real.smoothTransition.nonneg _)

theorem cubicAFEDyadicLowerWeight_zero {x : ℝ} (hx : x ≤ 1 / 2) :
    cubicAFEDyadicLowerWeight x = 0 := by
  rw [cubicAFEDyadicLowerWeight, Real.smoothTransition.one_of_one_le (by linarith), sub_self]

theorem cubicAFEDyadicLowerWeight_one {x : ℝ} (hx : 1 ≤ x) :
    cubicAFEDyadicLowerWeight x = 1 := by
  rw [cubicAFEDyadicLowerWeight, Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

theorem contDiff_cubicAFEDyadicLowerWeight : ContDiff ℝ ∞ cubicAFEDyadicLowerWeight := by
  unfold cubicAFEDyadicLowerWeight
  fun_prop

theorem hasSum_cubicAFEDyadicWindow_allReal (x : ℝ) :
    HasSum (fun j : ℕ ↦ cubicAFEDyadicWindow j x) (cubicAFEDyadicLowerWeight x) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun j ↦ cubicAFEDyadicWindow_nonneg j x) _).mpr
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually
    (eventually_ge_atTop x)] with J hJ
  rw [sum_cubicAFEDyadicWindow_range]
  have hp : (0 : ℝ) < 2^J := pow_pos (by norm_num) _
  have hquot : x / (2 : ℝ)^J ≤ 1 := (div_le_one hp).mpr hJ
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  rfl

theorem hasSum_cubicAFEProgressionDyadicCutoff_allReal {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (x : ℝ) :
    HasSum (fun jk : ℕ × ℕ ↦ cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 x)
      (cubicAFEDyadicLowerWeight x *
        cubicAFEDyadicLowerWeight (cubicAFEProgressionRealSecond d e δ x)) := by
  let y := cubicAFEProgressionRealSecond d e δ x
  change HasSum (fun jk : ℕ × ℕ ↦ cubicAFEDyadicWindow jk.1 x * cubicAFEDyadicWindow jk.2 y)
    (cubicAFEDyadicLowerWeight x * cubicAFEDyadicLowerWeight y)
  have ha := hasSum_cubicAFEDyadicWindow_allReal x
  have hb := hasSum_cubicAFEDyadicWindow_allReal y
  have hs : Summable (fun jk : ℕ × ℕ ↦ cubicAFEDyadicWindow jk.1 x * cubicAFEDyadicWindow jk.2 y) :=
    Summable.mul_of_nonneg (f := fun j : ℕ ↦ cubicAFEDyadicWindow j x)
      (g := fun k : ℕ ↦ cubicAFEDyadicWindow k y) ha.summable hb.summable
      (fun j ↦ cubicAFEDyadicWindow_nonneg j x) (fun k ↦ cubicAFEDyadicWindow_nonneg k y)
  exact HasSum.mul (f := fun j : ℕ ↦ cubicAFEDyadicWindow j x) (g := fun k : ℕ ↦ cubicAFEDyadicWindow k y)
    (s := cubicAFEDyadicLowerWeight x) (t := cubicAFEDyadicLowerWeight y) ha hb hs

/-- Exact all-real kernel reassembly, including both lower-boundary weights. -/
theorem hasSum_cubicAFEProgressionDyadicKernel_allReal
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e) (δ : ℤ) (t x : ℝ) :
    HasSum (fun jk : ℕ × ℕ ↦ cubicAFEProgressionCutoffSummand W T X V
      (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2) t x)
      (((cubicAFEDyadicLowerWeight x *
        cubicAFEDyadicLowerWeight (cubicAFEProgressionRealSecond d e δ x) : ℝ) : ℂ) *
          cubicAFEProgressionPhysicalSummand W T X V d e δ t x) := by
  have hc := Complex.hasSum_ofReal.mpr (hasSum_cubicAFEProgressionDyadicCutoff_allReal (d := d) he δ x)
  exact hc.mul_right (cubicAFEProgressionPhysicalSummand W T X V d e δ t x)

/-- Pointwise absolute convergence does not yet assert integrated absolute
convergence over the full physical domain. -/
theorem hasSum_norm_cubicAFEProgressionDyadicKernel_allReal
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e) (δ : ℤ) (t x : ℝ) :
    HasSum (fun jk : ℕ × ℕ ↦ ‖cubicAFEProgressionCutoffSummand W T X V
      (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2) t x‖)
      (cubicAFEDyadicLowerWeight x *
        cubicAFEDyadicLowerWeight (cubicAFEProgressionRealSecond d e δ x) *
          ‖cubicAFEProgressionPhysicalSummand W T X V d e δ t x‖) := by
  have hh := (hasSum_cubicAFEProgressionDyadicCutoff_allReal (d := d) he δ x).mul_right
    ‖cubicAFEProgressionPhysicalSummand W T X V d e δ t x‖
  apply hh.congr_fun
  intro jk
  rw [cubicAFEProgressionCutoffSummand, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (cubicAFEProgressionDyadicCutoff_nonneg he δ jk.1 jk.2 x)]

end PrimeNumberTheorem.MWKFCubic
