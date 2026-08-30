import PrimeNumberTheorem.MWKFCubicAFEDyadicBoundary

open Complex Filter
open scoped Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Exact lower-scale completion before the common Mellin zero mode

Rebasing the windows by J adds scales down to 2^(-J). Their continuous
mass is beta(2^J x) beta(2^J y), while every positive integer pair retains
mass one. Eventual pointwise equality does not justify integral limits.
-/

noncomputable def cubicAFEDyadicCompletionWeight (J : ℕ) (x y : ℝ) : ℝ :=
  cubicAFEDyadicLowerWeight ((2 : ℝ)^J * x) * cubicAFEDyadicLowerWeight ((2 : ℝ)^J * y)

theorem cubicAFEDyadicCompletionWeight_zero (x y : ℝ) :
    cubicAFEDyadicCompletionWeight 0 x y = cubicAFEDyadicLowerWeight x * cubicAFEDyadicLowerWeight y := by
  simp [cubicAFEDyadicCompletionWeight]

theorem hasSum_cubicAFEDyadicCompletionWeight (J : ℕ) (x y : ℝ) :
    HasSum (fun jk : ℕ × ℕ ↦ cubicAFEDyadicWindow jk.1 ((2 : ℝ)^J * x) *
      cubicAFEDyadicWindow jk.2 ((2 : ℝ)^J * y)) (cubicAFEDyadicCompletionWeight J x y) := by
  let f (j : ℕ) := cubicAFEDyadicWindow j ((2 : ℝ)^J * x)
  let g (k : ℕ) := cubicAFEDyadicWindow k ((2 : ℝ)^J * y)
  have hf := hasSum_cubicAFEDyadicWindow_allReal ((2 : ℝ)^J * x)
  have hg := hasSum_cubicAFEDyadicWindow_allReal ((2 : ℝ)^J * y)
  have hs : Summable (fun jk : ℕ × ℕ ↦ f jk.1 * g jk.2) :=
    Summable.mul_of_nonneg (f := f) (g := g) hf.summable hg.summable
      (fun j ↦ cubicAFEDyadicWindow_nonneg j _) (fun k ↦ cubicAFEDyadicWindow_nonneg k _)
  exact HasSum.mul (f := f) (g := g) hf hg hs

theorem cubicAFEDyadicCompletionWeight_eq_one_of_one_le
    (J : ℕ) {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    cubicAFEDyadicCompletionWeight J x y = 1 := by
  have hp : (1 : ℝ) ≤ 2^J := one_le_pow₀ (by norm_num)
  have hx' : (1 : ℝ) ≤ 2^J * x := one_le_mul_of_one_le_of_one_le hp hx
  have hy' : (1 : ℝ) ≤ 2^J * y := one_le_mul_of_one_le_of_one_le hp hy
  rw [cubicAFEDyadicCompletionWeight, cubicAFEDyadicLowerWeight_one hx',
    cubicAFEDyadicLowerWeight_one hy', mul_one]

theorem eventually_cubicAFEDyadicCompletionWeight_eq_one {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    ∀ᶠ J : ℕ in atTop, cubicAFEDyadicCompletionWeight J x y = 1 := by
  have hp := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  filter_upwards [hp.eventually (eventually_ge_atTop (1 / x)),
    hp.eventually (eventually_ge_atTop (1 / y))] with J hxJ hyJ
  have hx' : (1 : ℝ) ≤ 2^J * x := (div_le_iff₀ hx).mp hxJ
  have hy' : (1 : ℝ) ≤ 2^J * y := (div_le_iff₀ hy).mp hyJ
  rw [cubicAFEDyadicCompletionWeight, cubicAFEDyadicLowerWeight_one hx',
    cubicAFEDyadicLowerWeight_one hy', mul_one]

noncomputable def cubicAFEDyadicCompletionCorrection
    (W : CubicTestWeight) (T X V : ℝ) (d e : ℕ) (δ : ℤ) (J : ℕ) (t x : ℝ) : ℂ :=
  ((cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) -
    cubicAFEDyadicCompletionWeight 0 x (cubicAFEProgressionRealSecond d e δ x) : ℝ) : ℂ) *
      cubicAFEProgressionPhysicalSummand W T X V d e δ t x

/-- The added continuous lower scales change no admissible integer term. -/
theorem cubicAFEDyadicCompletionCorrection_eq_zero_on_progression
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    {δ : ℤ} {m : ℕ} (hm : m ∈ cubicAFEProgression d e δ) (J : ℕ) (t : ℝ) :
    cubicAFEDyadicCompletionCorrection W T X V d e δ J t m = 0 := by
  have hx : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
  have hy : (1 : ℝ) ≤ cubicAFEProgressionRealSecond d e δ m := by
    change 1 ≤ ((δ : ℝ) + (m : ℝ) * ((d / Nat.gcd d e : ℕ) : ℝ)) /
      ((e / Nat.gcd d e : ℕ) : ℝ)
    rw [← cubicAFEProgressionPair_second_cast he hm]
    exact_mod_cast Nat.succ_pos (cubicAFEProgressionPair d e δ m).2
  rw [cubicAFEDyadicCompletionCorrection,
    cubicAFEDyadicCompletionWeight_eq_one_of_one_le J hx hy,
    cubicAFEDyadicCompletionWeight_eq_one_of_one_le 0 hx hy, sub_self,
    Complex.ofReal_zero, zero_mul]

/-- Exact physical kernel correction; this is not an integral interchange. -/
theorem cubicAFEDyadicCompletionKernel_eq_boundary_add_correction
    (W : CubicTestWeight) (T X V : ℝ) (d e : ℕ) (δ : ℤ) (J : ℕ) (t x : ℝ) :
    (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) : ℂ) *
      cubicAFEProgressionPhysicalSummand W T X V d e δ t x =
      ((cubicAFEDyadicLowerWeight x *
        cubicAFEDyadicLowerWeight (cubicAFEProgressionRealSecond d e δ x) : ℝ) : ℂ) *
          cubicAFEProgressionPhysicalSummand W T X V d e δ t x +
        cubicAFEDyadicCompletionCorrection W T X V d e δ J t x := by
  rw [cubicAFEDyadicCompletionCorrection, cubicAFEDyadicCompletionWeight_zero, Complex.ofReal_sub]
  ring

end PrimeNumberTheorem.MWKFCubic
