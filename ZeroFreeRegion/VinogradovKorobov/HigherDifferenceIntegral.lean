import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import ZeroFreeRegion.VinogradovKorobov.IteratedDifference

namespace ZeroFreeRegion.VinogradovKorobov

/-- The real-variable analogue of the signed difference used by the
discrete A-process. -/
def realPhaseDifference (h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x - f (x + h)

/-- Iterated real-variable signed differences. -/
def realIteratedPhaseDifference : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | h :: shifts, f =>
      realPhaseDifference h (realIteratedPhaseDifference shifts f)

/-- Iterated integration over successive positive shifts.  The value for
`h :: shifts` integrates the remaining kernel from `x` to `x + h`. -/
noncomputable def iteratedShiftIntegral : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | h :: shifts, f => fun x ↦
      ∫ u in x..x + h, iteratedShiftIntegral shifts f u

@[simp] lemma realIteratedPhaseDifference_nil (f : ℝ → ℝ) :
    realIteratedPhaseDifference [] f = f := rfl

@[simp] lemma realIteratedPhaseDifference_cons
    (h : ℝ) (shifts : List ℝ) (f : ℝ → ℝ) :
    realIteratedPhaseDifference (h :: shifts) f =
      realPhaseDifference h (realIteratedPhaseDifference shifts f) := rfl

@[simp] lemma iteratedShiftIntegral_nil (f : ℝ → ℝ) :
    iteratedShiftIntegral [] f = f := rfl

@[simp] lemma iteratedShiftIntegral_cons
    (h : ℝ) (shifts : List ℝ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedShiftIntegral (h :: shifts) f x =
      ∫ u in x..x + h, iteratedShiftIntegral shifts f u := rfl

/-- Signed differences preserve a derivative tower on the positive axis. -/
lemma hasDerivAt_realIteratedPhaseDifference_of_tower
    (F : ℕ → ℝ → ℝ)
    (hF : ∀ j y, 0 < y → HasDerivAt (F j) (F (j + 1) y) y)
    (shifts : List ℝ) (hshifts : ∀ h ∈ shifts, 0 ≤ h)
    (j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (realIteratedPhaseDifference shifts (F j))
      (realIteratedPhaseDifference shifts (F (j + 1)) x) x := by
  induction shifts generalizing j x with
  | nil => simpa using hF j x hx
  | cons h shifts ih =>
      have hh : 0 ≤ h := hshifts h (by simp)
      have htail : ∀ k ∈ shifts, 0 ≤ k := by
        intro k hk
        exact hshifts k (by simp [hk])
      have hleft := ih htail j hx
      have hxh : 0 < x + h := lt_of_lt_of_le hx (le_add_of_nonneg_right hh)
      have hrightBase := ih htail j hxh
      have hright : HasDerivAt
          (fun y ↦ realIteratedPhaseDifference shifts (F j) (y + h))
          (realIteratedPhaseDifference shifts (F (j + 1)) (x + h)) x := by
        convert hrightBase.comp x ((hasDerivAt_id x).add_const h) using 1 <;>
          simp
      convert hleft.sub hright using 1 <;>
        simp [realPhaseDifference]

/-- An arbitrary finite signed difference is an iterated integral of the
corresponding member of a derivative tower. -/
theorem iteratedShiftIntegral_tower_eq_signedDifference
    (F : ℕ → ℝ → ℝ)
    (hF : ∀ j y, 0 < y → HasDerivAt (F j) (F (j + 1) y) y)
    (shifts : List ℝ) (hshifts : ∀ h ∈ shifts, 0 ≤ h)
    (j : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedShiftIntegral shifts (F (shifts.length + j)) x =
      (-1 : ℝ) ^ shifts.length *
        realIteratedPhaseDifference shifts (F j) x := by
  induction shifts generalizing j x with
  | nil => simp
  | cons h shifts ih =>
      have hh : 0 ≤ h := hshifts h (by simp)
      have htail : ∀ k ∈ shifts, 0 ≤ k := by
        intro k hk
        exact hshifts k (by simp [hk])
      have hxxh : x ≤ x + h := le_add_of_nonneg_right hh
      have hpos (u : ℝ) (hu : u ∈ Set.uIcc x (x + h)) : 0 < u := by
        rw [Set.uIcc_of_le hxxh] at hu
        exact hx.trans_le hu.1
      have hderiv (u : ℝ) (hu : u ∈ Set.uIcc x (x + h)) :
          HasDerivAt
            (realIteratedPhaseDifference shifts (F j))
            (realIteratedPhaseDifference shifts (F (j + 1)) u) u :=
        hasDerivAt_realIteratedPhaseDifference_of_tower
          F hF shifts htail j (hpos u hu)
      have hcont : ContinuousOn
          (realIteratedPhaseDifference shifts (F (j + 1)))
          (Set.uIcc x (x + h)) := by
        intro u hu
        exact (hasDerivAt_realIteratedPhaseDifference_of_tower
          F hF shifts htail (j + 1) (hpos u hu)).continuousAt.continuousWithinAt
      have hftc :
          (∫ u in x..x + h,
              realIteratedPhaseDifference shifts (F (j + 1)) u) =
            realIteratedPhaseDifference shifts (F j) (x + h) -
              realIteratedPhaseDifference shifts (F j) x :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          hderiv hcont.intervalIntegrable
      calc
        iteratedShiftIntegral (h :: shifts)
            (F ((h :: shifts).length + j)) x =
            ∫ u in x..x + h,
              ((-1 : ℝ) ^ shifts.length *
                realIteratedPhaseDifference shifts (F (j + 1)) u) := by
          apply intervalIntegral.integral_congr
          intro u hu
          have hi := ih htail (j + 1) (hpos u hu)
          simpa only [List.length_cons, Nat.succ_add, Nat.add_succ] using hi
        _ = (-1 : ℝ) ^ shifts.length *
            (∫ u in x..x + h,
              realIteratedPhaseDifference shifts (F (j + 1)) u) := by
          rw [intervalIntegral.integral_const_mul]
        _ = (-1 : ℝ) ^ shifts.length *
            (realIteratedPhaseDifference shifts (F j) (x + h) -
              realIteratedPhaseDifference shifts (F j) x) := by rw [hftc]
        _ = (-1 : ℝ) ^ (h :: shifts).length *
            realIteratedPhaseDifference (h :: shifts) (F j) x := by
          simp only [List.length_cons, realIteratedPhaseDifference_cons,
            realPhaseDifference, pow_succ]
          ring

/-- Iterated shift integration preserves global continuity. -/
lemma continuous_iteratedShiftIntegral
    {f : ℝ → ℝ} (hf : Continuous f) (shifts : List ℝ) :
    Continuous (iteratedShiftIntegral shifts f) := by
  induction shifts with
  | nil => exact hf
  | cons h shifts ih =>
      have hprimitive : Continuous
          (fun y ↦ ∫ u in (0 : ℝ)..y, iteratedShiftIntegral shifts f u) :=
        (intervalIntegral.differentiable_integral_of_continuous ih).continuous
      have heq : iteratedShiftIntegral (h :: shifts) f =
          fun x ↦
            (∫ u in (0 : ℝ)..x + h, iteratedShiftIntegral shifts f u) -
              ∫ u in (0 : ℝ)..x, iteratedShiftIntegral shifts f u := by
        funext x
        rw [iteratedShiftIntegral_cons]
        exact (intervalIntegral.integral_interval_sub_left
          (ih.intervalIntegrable 0 (x + h))
          (ih.intervalIntegrable 0 x)).symm
      rw [heq]
      exact (hprimitive.comp (continuous_id.add continuous_const)).sub hprimitive

/-- Pointwise comparison passes through any finite collection of nonnegative
shift integrals. -/
lemma iteratedShiftIntegral_mono
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ y, f y ≤ g y)
    (shifts : List ℝ) (hshifts : ∀ h ∈ shifts, 0 ≤ h) (x : ℝ) :
    iteratedShiftIntegral shifts f x ≤ iteratedShiftIntegral shifts g x := by
  induction shifts generalizing x with
  | nil => exact hfg x
  | cons h shifts ih =>
      have hh : 0 ≤ h := hshifts h (by simp)
      have htail : ∀ k ∈ shifts, 0 ≤ k := by
        intro k hk
        exact hshifts k (by simp [hk])
      apply intervalIntegral.integral_mono_on (le_add_of_nonneg_right hh)
        ((continuous_iteratedShiftIntegral hf shifts).intervalIntegrable x (x + h))
        ((continuous_iteratedShiftIntegral hg shifts).intervalIntegrable x (x + h))
      intro y _
      exact ih htail y

/-- The iterated shift integral of a constant is the product of the shift
lengths times that constant. -/
lemma iteratedShiftIntegral_const
    (shifts : List ℝ) (c x : ℝ) :
    iteratedShiftIntegral shifts (fun _ ↦ c) x = shifts.prod * c := by
  induction shifts generalizing x with
  | nil => simp
  | cons h shifts ih =>
      simp only [iteratedShiftIntegral_cons]
      rw [show (fun u ↦ iteratedShiftIntegral shifts (fun _ ↦ c) u) =
          fun _ ↦ shifts.prod * c by
        funext u
        exact ih u,
        intervalIntegral.integral_const]
      simp only [List.prod_cons, sub_self, add_sub_cancel_left, smul_eq_mul]
      ring

/-- Uniform pointwise bounds give product-scale bounds for an iterated shift
integral. -/
lemma iteratedShiftIntegral_bounds
    {f : ℝ → ℝ} (hf : Continuous f) (lower upper : ℝ)
    (hlower : ∀ y, lower ≤ f y) (hupper : ∀ y, f y ≤ upper)
    (shifts : List ℝ) (hshifts : ∀ h ∈ shifts, 0 ≤ h) (x : ℝ) :
    shifts.prod * lower ≤ iteratedShiftIntegral shifts f x ∧
      iteratedShiftIntegral shifts f x ≤ shifts.prod * upper := by
  constructor
  · rw [← iteratedShiftIntegral_const shifts lower x]
    exact iteratedShiftIntegral_mono continuous_const hf hlower shifts hshifts x
  · rw [← iteratedShiftIntegral_const shifts upper x]
    exact iteratedShiftIntegral_mono hf continuous_const hupper shifts hshifts x

/-- An iterated shift integral based at `x` only uses values between `x` and
`x + shifts.sum`. -/
lemma iteratedShiftIntegral_congr_Icc
    {f g : ℝ → ℝ} (shifts : List ℝ)
    (hshifts : ∀ h ∈ shifts, 0 ≤ h) {x : ℝ}
    (hfg : ∀ y ∈ Set.Icc x (x + shifts.sum), f y = g y) :
    iteratedShiftIntegral shifts f x = iteratedShiftIntegral shifts g x := by
  induction shifts generalizing x with
  | nil =>
      exact hfg x (by simp)
  | cons h shifts ih =>
      have hh : 0 ≤ h := hshifts h (by simp)
      have htail : ∀ k ∈ shifts, 0 ≤ k := by
        intro k hk
        exact hshifts k (by simp [hk])
      apply intervalIntegral.integral_congr
      intro u hu
      have hxu : x ≤ u := by
        rw [Set.uIcc_of_le (le_add_of_nonneg_right hh)] at hu
        exact hu.1
      have huxh : u ≤ x + h := by
        rw [Set.uIcc_of_le (le_add_of_nonneg_right hh)] at hu
        exact hu.2
      apply ih htail
      intro y hy
      apply hfg y
      constructor
      · exact hxu.trans hy.1
      · simp only [List.sum_cons]
        calc
          y ≤ u + shifts.sum := hy.2
          _ ≤ (x + h) + shifts.sum := add_le_add huxh le_rfl
          _ = x + (h + shifts.sum) := by ring

end ZeroFreeRegion.VinogradovKorobov
