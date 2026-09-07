import PrimeNumberTheorem.CarlsonGaussianHilbertSection
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite Gaussian covering

This is the exact local-to-dyadic covering step used after the Carlson
three-lines estimate.  It is purely real-variable: a finite set of Gaussian
windows covering an interval turns uniform local weighted bounds into an
unweighted interval bound.
-/

open Set MeasureTheory
open scoped BigOperators

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Midpoints of the consecutive `Delta`-windows starting at `U` and ending
after `V`. -/
noncomputable def carlsonGaussianCoverCenters
    (Delta U V : ℝ) : Finset ℝ :=
  (Finset.range (Nat.floor ((V - U) / Delta) + 1)).image
    (fun j : ℕ => U + ((j : ℝ) + 1 / 2) * Delta)

/-- The midpoint grid covers `[U,V]` by closed half-windows of radius
`Delta/2`. -/
theorem exists_mem_carlsonGaussianCoverCenters_abs_sub_le_half
    {Delta U V t : ℝ} (hDelta : 0 < Delta)
    (ht : t ∈ Icc U V) :
    ∃ c ∈ carlsonGaussianCoverCenters Delta U V,
      |t - c| ≤ Delta / 2 := by
  classical
  let r : ℝ := (t - U) / Delta
  let j : ℕ := Nat.floor r
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (sub_nonneg.mpr ht.1) hDelta.le
  have hrR : r ≤ (V - U) / Delta := by
    dsimp [r]
    exact div_le_div_of_nonneg_right (sub_le_sub_right ht.2 U) hDelta.le
  have hjle : (j : ℝ) ≤ r := by
    dsimp [j]
    exact Nat.floor_le hr0
  have hrlt : r < (j : ℝ) + 1 := by
    dsimp [j]
    exact Nat.lt_floor_add_one r
  have hjBound : j < Nat.floor ((V - U) / Delta) + 1 := by
    apply Nat.lt_succ_iff.mpr
    dsimp [j]
    exact Nat.floor_mono hrR
  let c : ℝ := U + ((j : ℝ) + 1 / 2) * Delta
  have hc : c ∈ carlsonGaussianCoverCenters Delta U V := by
    dsimp [c, carlsonGaussianCoverCenters]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjBound, rfl⟩
  have hnormalized : |r - ((j : ℝ) + 1 / 2)| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hidentity : t - c = Delta * (r - ((j : ℝ) + 1 / 2)) := by
    dsimp [c, r]
    field_simp [hDelta.ne']
    ring
  refine ⟨c, hc, ?_⟩
  rw [hidentity, abs_mul, abs_of_pos hDelta]
  calc
    Delta * |r - ((j : ℝ) + 1 / 2)| ≤ Delta * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hnormalized hDelta.le
    _ = Delta / 2 := by ring

/-- The explicit midpoint grid uses no more than
`floor ((V-U)/Delta)+1` centers. -/
theorem card_carlsonGaussianCoverCenters_le
    (Delta U V : ℝ) :
    (carlsonGaussianCoverCenters Delta U V).card ≤
      Nat.floor ((V - U) / Delta) + 1 := by
  classical
  unfold carlsonGaussianCoverCenters
  exact (Finset.card_image_le).trans_eq (Finset.card_range _)

/-- If every point of `[U,V]` lies within `Delta/2` of one of finitely many
centers, then uniform full Gaussian integral bounds imply an unweighted
interval integral bound.  The loss is the explicit constant `exp(1/4)` times
the number of centers. -/
theorem integral_indicator_Icc_le_card_mul_of_gaussian_cover
    {g : ℝ → ℝ} {centers : Finset ℝ} {Delta U V L : ℝ}
    (hDelta : 0 < Delta) (hg : ∀ t, 0 ≤ g t)
    (hTargetInt : Integrable ((Icc U V).indicator g))
    (hLocalInt : ∀ c ∈ centers,
      Integrable (fun t => carlsonGaussianWeight Delta c t * g t))
    (hcover : ∀ t ∈ Icc U V, ∃ c ∈ centers, |t - c| ≤ Delta / 2)
    (hLocal : ∀ c ∈ centers,
      (∫ t : ℝ, carlsonGaussianWeight Delta c t * g t) ≤ L) :
    (∫ t : ℝ, (Icc U V).indicator g t) ≤
      Real.exp (1 / 4 : ℝ) * ((centers.card : ℝ) * L) := by
  let total : ℝ → ℝ := fun t =>
    ∑ c ∈ centers, carlsonGaussianWeight Delta c t * g t
  have htermNonneg (c t : ℝ) :
      0 ≤ carlsonGaussianWeight Delta c t * g t := by
    exact mul_nonneg (Real.exp_pos _).le (hg t)
  have htotalInt : Integrable total := by
    dsimp [total]
    exact integrable_finsetSum centers hLocalInt
  have hmajorInt : Integrable (fun t => Real.exp (1 / 4 : ℝ) * total t) :=
    htotalInt.const_mul _
  have hpoint (t : ℝ) :
      (Icc U V).indicator g t ≤ Real.exp (1 / 4 : ℝ) * total t := by
    by_cases ht : t ∈ Icc U V
    · rw [Set.indicator_of_mem ht]
      rcases hcover t ht with ⟨c, hc, hclose⟩
      have hhalfNonneg : 0 ≤ Delta / 2 := by positivity
      have hsq : (t - c) ^ 2 ≤ (Delta / 2) ^ 2 := by
        have := (sq_le_sq₀ (abs_nonneg (t - c)) hhalfNonneg).2 hclose
        simpa [sq_abs] using this
      have hratio : (t - c) ^ 2 / Delta ^ 2 ≤ (1 / 4 : ℝ) := by
        apply (div_le_iff₀ (sq_pos_of_pos hDelta)).2
        nlinarith
      have hweight : Real.exp (-(1 / 4 : ℝ)) ≤
          carlsonGaussianWeight Delta c t := by
        unfold carlsonGaussianWeight
        apply Real.exp_le_exp.mpr
        rw [neg_div]
        exact neg_le_neg hratio
      have hfactor : 1 ≤ Real.exp (1 / 4 : ℝ) *
          carlsonGaussianWeight Delta c t := by
        calc
          1 = Real.exp (1 / 4 : ℝ) * Real.exp (-(1 / 4 : ℝ)) := by
            rw [← Real.exp_add]
            norm_num
          _ ≤ Real.exp (1 / 4 : ℝ) *
              carlsonGaussianWeight Delta c t :=
            mul_le_mul_of_nonneg_left hweight (Real.exp_pos _).le
      have hgSelected : g t ≤ Real.exp (1 / 4 : ℝ) *
          (carlsonGaussianWeight Delta c t * g t) := by
        calc
          g t ≤ (Real.exp (1 / 4 : ℝ) *
              carlsonGaussianWeight Delta c t) * g t :=
            le_mul_of_one_le_left (hg t) hfactor
          _ = Real.exp (1 / 4 : ℝ) *
              (carlsonGaussianWeight Delta c t * g t) := by ring
      have hselected : carlsonGaussianWeight Delta c t * g t ≤ total t := by
        dsimp [total]
        exact Finset.single_le_sum
          (fun d _hd => htermNonneg d t) hc
      exact hgSelected.trans
        (mul_le_mul_of_nonneg_left hselected (Real.exp_pos _).le)
    · simp only [Set.indicator, ht, ↓reduceIte]
      exact mul_nonneg (Real.exp_pos _).le <| by
        dsimp [total]
        exact Finset.sum_nonneg fun c _hc => htermNonneg c t
  calc
    (∫ t : ℝ, (Icc U V).indicator g t) ≤
        ∫ t : ℝ, Real.exp (1 / 4 : ℝ) * total t :=
      integral_mono hTargetInt hmajorInt hpoint
    _ = Real.exp (1 / 4 : ℝ) * ∫ t : ℝ, total t := by
      rw [integral_const_mul]
    _ = Real.exp (1 / 4 : ℝ) *
        ∑ c ∈ centers,
          ∫ t : ℝ, carlsonGaussianWeight Delta c t * g t := by
      rw [show (∫ t : ℝ, total t) =
          ∑ c ∈ centers,
            ∫ t : ℝ, carlsonGaussianWeight Delta c t * g t by
        dsimp [total]
        rw [integral_finsetSum centers hLocalInt]]
    _ ≤ Real.exp (1 / 4 : ℝ) * ∑ _c ∈ centers, L := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Finset.sum_le_sum fun c hc => hLocal c hc
    _ = Real.exp (1 / 4 : ℝ) * ((centers.card : ℝ) * L) := by
      simp

/-- Explicit-grid form of the finite Gaussian covering bound. -/
theorem integral_indicator_Icc_le_floor_add_one_mul_of_local_gaussian_bound
    {g : ℝ → ℝ} {Delta U V L : ℝ}
    (hDelta : 0 < Delta) (hL : 0 ≤ L)
    (hg : ∀ t, 0 ≤ g t)
    (hTargetInt : Integrable ((Icc U V).indicator g))
    (hLocalInt : ∀ c ∈ carlsonGaussianCoverCenters Delta U V,
      Integrable (fun t => carlsonGaussianWeight Delta c t * g t))
    (hLocal : ∀ c ∈ carlsonGaussianCoverCenters Delta U V,
      (∫ t : ℝ, carlsonGaussianWeight Delta c t * g t) ≤ L) :
    (∫ t : ℝ, (Icc U V).indicator g t) ≤
      Real.exp (1 / 4 : ℝ) *
        (((Nat.floor ((V - U) / Delta) + 1 : ℕ) : ℝ) * L) := by
  have hbase := integral_indicator_Icc_le_card_mul_of_gaussian_cover
    hDelta hg hTargetInt hLocalInt
    (fun t ht =>
      exists_mem_carlsonGaussianCoverCenters_abs_sub_le_half hDelta ht)
    hLocal
  refine hbase.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_right _ hL
  exact_mod_cast card_carlsonGaussianCoverCenters_le Delta U V

end CarlsonZeroDensity
end PrimeNumberTheorem
