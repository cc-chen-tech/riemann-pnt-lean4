import PrimeNumberTheorem.MWKFCubicAFEPhysicalWeight
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Complex Set
open scoped ContDiff

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The actual progression kernel before Poisson summation

The real extension retains the full amplitude, logarithmic phase, finite-height
Mellin weight, both Möbius coefficients, and physical test weight. Smoothness
is proved on the exact positive-index region, including negative shifts.
-/

noncomputable def cubicAFEProgressionRealSecond (d e : ℕ) (δ : ℤ) (x : ℝ) : ℝ :=
  ((δ : ℝ) + x * ((d / Nat.gcd d e : ℕ) : ℝ)) /
    ((e / Nat.gcd d e : ℕ) : ℝ)

noncomputable def cubicAFEProgressionRealProduct (d e : ℕ) (δ : ℤ) (x : ℝ) : ℝ :=
  x * cubicAFEProgressionRealSecond d e δ x

def cubicAFEProgressionDomain (d e : ℕ) (δ : ℤ) : Set ℝ :=
  {x | 0 < x ∧ 0 < (δ : ℝ) + x * ((d / Nat.gcd d e : ℕ) : ℝ)}

private theorem reduced_positive {d e : ℕ} (hd : 0 < d) : 0 < d / Nat.gcd d e := by
  have h := (gcd_extraction (Nat.gcd_pos_of_pos_left e hd).ne').1
  apply Nat.pos_of_ne_zero
  intro hz
  rw [hz, mul_zero] at h
  exact hd.ne' h

theorem isOpen_cubicAFEProgressionDomain (d e : ℕ) (δ : ℤ) :
    IsOpen (cubicAFEProgressionDomain d e δ) := by
  exact (isOpen_lt continuous_const continuous_id).inter
    (isOpen_lt continuous_const (continuous_const.add (continuous_id.mul continuous_const)))

theorem cubicAFEProgressionRealProduct_pos {d e : ℕ} (he : 0 < e) {δ : ℤ} {x : ℝ}
    (hx : x ∈ cubicAFEProgressionDomain d e δ) :
    0 < cubicAFEProgressionRealProduct d e δ x := by
  have hs : (0 : ℝ) < ((e / Nat.gcd d e : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < e / Nat.gcd d e by
      simpa only [Nat.gcd_comm] using (reduced_positive (e := d) he))
  exact mul_pos hx.1 (div_pos hx.2 hs)

theorem cubicAFEProgression_logArgument_pos {d e : ℕ} (hd : 0 < d) {δ : ℤ} {x : ℝ}
    (hx : x ∈ cubicAFEProgressionDomain d e δ) :
    0 < 1 + (δ : ℝ) / (x * ((d / Nat.gcd d e : ℕ) : ℝ)) := by
  have hr : (0 : ℝ) < ((d / Nat.gcd d e : ℕ) : ℝ) := by
    exact_mod_cast reduced_positive (e := e) hd
  have hden := mul_pos hx.1 hr
  have hform : 1 + (δ : ℝ) / (x * ((d / Nat.gcd d e : ℕ) : ℝ)) =
      ((δ : ℝ) + x * ((d / Nat.gcd d e : ℕ) : ℝ)) /
        (x * ((d / Nat.gcd d e : ℕ) : ℝ)) := by
    rw [add_div, div_self hden.ne']
    ring
  rw [hform]
  exact div_pos hx.2 hden

theorem cubicAFEProgression_natCast_mem_domain {d e : ℕ} {δ : ℤ} {m : ℕ}
    (hm : m ∈ cubicAFEProgression d e δ) :
    (m : ℝ) ∈ cubicAFEProgressionDomain d e δ := by
  refine ⟨by exact_mod_cast hm.1, ?_⟩
  have hnum : (0 : ℝ) < (cubicAFEProgressionNumerator d e δ m : ℝ) := by
    exact_mod_cast hm.2.1
  simpa only [cubicAFEProgressionNumerator, Int.cast_add, Int.cast_mul, Int.cast_natCast] using hnum

theorem cubicAFEProgressionRealProduct_natCast {d e : ℕ} (he : 0 < e) {δ : ℤ} {m : ℕ}
    (hm : m ∈ cubicAFEProgression d e δ) :
    cubicAFEProgressionRealProduct d e δ m =
      (cubicAFEPositiveIndexProduct (cubicAFEProgressionPair d e δ m) : ℝ) := by
  simp only [cubicAFEPositiveIndexProduct, Nat.cast_mul]
  rw [(cubicAFEProgressionPair_succ he hm).1, cubicAFEProgressionPair_second_cast he hm]
  rfl

noncomputable def cubicAFEProgressionPhysicalSummand
    (W : CubicTestWeight) (T X V : ℝ) (d e : ℕ) (δ : ℤ) (t x : ℝ) : ℂ :=
  (cubicMollifierCoefficient T d : ℂ) * (cubicMollifierCoefficient T e : ℂ) * 2 *
    (((Real.sqrt (cubicAFEProgressionRealProduct d e δ x) : ℂ)⁻¹ *
      (Real.sqrt (d * e) : ℂ)⁻¹) *
      Complex.exp ((Complex.I * (Real.log (1 + (δ : ℝ) /
        (x * ((d / Nat.gcd d e : ℕ) : ℝ))) : ℂ)) * t) *
      cubicAFERealProductWeightFinite t X V (cubicAFEProgressionRealProduct d e δ x)) *
    (W (t / T) : ℂ)

/-- Exact equality with the original complete summand, not just with its
oscillatory part. The product is an exact real quotient, never a floor. -/
theorem cubicAFEProgressionPhysicalSummand_eq_discrete
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (t : ℝ) {δ : ℤ} {m : ℕ} (hm : m ∈ cubicAFEProgression d e δ) :
    cubicAFEProgressionPhysicalSummand W T X V d e δ t m =
      cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m) := by
  have hp : cubicAFEReducedShift d e (cubicAFEProgressionPair d e δ m) = δ :=
    cubicAFEProgressionPair_mem he hm
  have hk : 0 < cubicAFEPositiveIndexProduct (cubicAFEProgressionPair d e δ m) := by
    unfold cubicAFEPositiveIndexProduct
    positivity
  rw [cubicAFECombinedSummandFinite_eq_reducedShift W T X V hd he t,
    hp, (cubicAFEProgressionPair_succ he hm).1,
    ← cubicAFERealProductWeightFinite_natCast t X V hk,
    ← cubicAFEProgressionRealProduct_natCast he hm]
  rfl

/-- Local regularity for the actual kernel, with its two positive-index
constraints. No uniform bound in the physical parameters is asserted. -/
theorem contDiffOn_cubicAFEProgressionPhysicalSummand
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (δ : ℤ) (t : ℝ) (hX : 1 / 2 < X) :
    ContDiffOn ℝ ∞ (cubicAFEProgressionPhysicalSummand W T X V d e δ t)
      (cubicAFEProgressionDomain d e δ) := by
  intro x hx
  have hP : ContDiff ℝ ∞ (cubicAFEProgressionRealProduct d e δ) := by
    unfold cubicAFEProgressionRealProduct cubicAFEProgressionRealSecond
    fun_prop
  have hpos := cubicAFEProgressionRealProduct_pos he hx
  have hsqrt : ContDiffWithinAt ℝ ∞
      (fun y ↦ (Real.sqrt (cubicAFEProgressionRealProduct d e δ y) : ℂ)⁻¹)
      (cubicAFEProgressionDomain d e δ) x := by
    apply (Complex.ofRealCLM.contDiff.comp_contDiffWithinAt
      (hP.contDiffWithinAt.sqrt hpos.ne')).inv
    change (Real.sqrt (cubicAFEProgressionRealProduct d e δ x) : ℂ) ≠ 0
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  have hr : (0 : ℝ) < ((d / Nat.gcd d e : ℕ) : ℝ) := by
    exact_mod_cast reduced_positive (e := e) hd
  have hphase : ContDiffWithinAt ℝ ∞
      (fun y : ℝ ↦ Real.log (1 + (δ : ℝ) / (y * ((d / Nat.gcd d e : ℕ) : ℝ))))
      (cubicAFEProgressionDomain d e δ) x := by
    have hden : ContDiffWithinAt ℝ ∞
        (fun y : ℝ ↦ y * ((d / Nat.gcd d e : ℕ) : ℝ))
        (cubicAFEProgressionDomain d e δ) x :=
      contDiffWithinAt_id.mul contDiffWithinAt_const
    have hquot : ContDiffWithinAt ℝ ∞
        (fun y : ℝ ↦ (δ : ℝ) / (y * ((d / Nat.gcd d e : ℕ) : ℝ)))
        (cubicAFEProgressionDomain d e δ) x := by
      have hc : ContDiffWithinAt ℝ ∞ (fun _ : ℝ ↦ (δ : ℝ))
          (cubicAFEProgressionDomain d e δ) x := contDiffWithinAt_const
      exact hc.div hden (mul_pos hx.1 hr).ne'
    exact (contDiffWithinAt_const.add hquot).log
      (cubicAFEProgression_logArgument_pos hd hx).ne'
  have hexp : ContDiffWithinAt ℝ ∞
      (fun y : ℝ ↦ Complex.exp ((Complex.I * (Real.log (1 + (δ : ℝ) /
        (y * ((d / Nat.gcd d e : ℕ) : ℝ))) : ℂ)) * t))
      (cubicAFEProgressionDomain d e δ) x :=
    ((contDiffWithinAt_const.mul
      (Complex.ofRealCLM.contDiff.comp_contDiffWithinAt hphase)).mul contDiffWithinAt_const).cexp
  have hweight : ContDiffWithinAt ℝ ∞
      (fun y ↦ cubicAFERealProductWeightFinite t X V (cubicAFEProgressionRealProduct d e δ y))
      (cubicAFEProgressionDomain d e δ) x :=
    ((contDiffOn_cubicAFERealProductWeightFinite t X V hX).contDiffAt
      (isOpen_Ioi.mem_nhds hpos)).comp_contDiffWithinAt x hP.contDiffWithinAt
  exact (contDiffWithinAt_const.mul
    (((hsqrt.mul contDiffWithinAt_const).mul hexp).mul hweight)).mul contDiffWithinAt_const

end PrimeNumberTheorem.MWKFCubic
