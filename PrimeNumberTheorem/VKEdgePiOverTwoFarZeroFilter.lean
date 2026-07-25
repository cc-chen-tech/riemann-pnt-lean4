import PrimeNumberTheorem.GlobalZeroCount
import PrimeNumberTheorem.VKEdgePiOverTwoConcreteLocalizedData

open Complex Polynomial
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/--
Offsets from `w` of every nontrivial zeta zero whose absolute ordinate is at
most `|Im w| + B`.  For `B ≥ 0`, this contains every zero in the vertical
band `|Im ρ - Im w| ≤ B`.
-/
def localizedNearZeroOffsets (w : ℂ) (B : ℝ) : Finset ℂ :=
  (nontrivialZerosFinset (|w.im| + B)).image fun rho => rho - w

/-- The fixed target-preserving polynomial which annihilates the near-zero
offsets around `w`. -/
def localizedNearZeroFilter (w : ℂ) (B : ℝ) : ℂ[X] :=
  targetPreservingPoleFilter (localizedNearZeroOffsets w B)

theorem localizedNearZeroFilter_eval_zero (w : ℂ) (B : ℝ) :
    (localizedNearZeroFilter w B).eval 0 = 1 := by
  exact targetPreservingPoleFilter_eval_zero _

theorem mem_localizedNearZeroOffsets_of_isNontrivialZero
    {w rho : ℂ} {B : ℝ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (him : |rho.im - w.im| ≤ B) :
    rho - w ∈ localizedNearZeroOffsets w B := by
  have habs :
      |rho.im| ≤ |w.im| + B := by
    calc
      |rho.im| = |(rho.im - w.im) + w.im| := by ring_nf
      _ ≤ |rho.im - w.im| + |w.im| := abs_add_le _ _
      _ ≤ |w.im| + B := by linarith
  apply Finset.mem_image.mpr
  exact ⟨rho, mem_nontrivialZerosFinset.mpr ⟨hrho, habs⟩, rfl⟩

theorem localizedGaussianWeight_nearZeroFilter_eq_zero
    {w rho : ℂ} {B m : ℝ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (hrhoNe : rho ≠ w) (him : |rho.im - w.im| ≤ B) :
    localizedGaussianWeight
        (localizedNearZeroFilter w B) w m rho = 0 := by
  apply localizedGaussianWeight_targetPreservingPoleFilter_eq_zero
  · exact mem_localizedNearZeroOffsets_of_isNontrivialZero hrho him
  · exact hrhoNe

/-- The part of a finite weighted zero sum outside the fixed vertical band
around the distinguished zero. -/
def localizedFarZeroResidueSum
    (A : ℂ[X]) (w : ℂ) (m B : ℝ) (zeros : Finset ℂ) : ℂ :=
  ∑ rho ∈ zeros.filter (fun rho => B < |rho.im - w.im|),
    (analyticOrderNatAt riemannZeta rho : ℂ) *
      localizedGaussianWeight A w m rho

/--
After applying the fixed near-zero filter, a finite zero sum is exactly the
target analytic multiplicity plus the explicitly named far-zero sum.
-/
theorem localizedZeroResidueSum_nearZeroFilter_eq_target_add_far
    {zeros : Finset ℂ} {w : ℂ} {B m : ℝ}
    (hB : 0 ≤ B) (hw : w ∈ zeros)
    (hzeros :
      ∀ rho ∈ zeros, RiemannHypothesis.IsNontrivialZero rho) :
    localizedZeroResidueSum
        (localizedNearZeroFilter w B) w m zeros =
      (analyticOrderNatAt riemannZeta w : ℂ) +
        localizedFarZeroResidueSum
          (localizedNearZeroFilter w B) w m B zeros := by
  let f : ℂ → ℂ := fun rho =>
    (analyticOrderNatAt riemannZeta rho : ℂ) *
      localizedGaussianWeight (localizedNearZeroFilter w B) w m rho
  have htarget :
      f w = (analyticOrderNatAt riemannZeta w : ℂ) := by
    dsimp [f]
    rw [localizedGaussianWeight_self,
      localizedNearZeroFilter_eval_zero]
    ring
  have herase :
      (∑ rho ∈ zeros.erase w, f rho) =
        ∑ rho ∈ zeros.filter (fun rho => B < |rho.im - w.im|), f rho := by
    calc
      (∑ rho ∈ zeros.erase w, f rho) =
          ∑ rho ∈ zeros.erase w,
            if B < |rho.im - w.im| then f rho else 0 := by
        apply Finset.sum_congr rfl
        intro rho hrho
        by_cases hfar : B < |rho.im - w.im|
        · simp [hfar]
        · have hrhoZeros : rho ∈ zeros := (Finset.mem_erase.mp hrho).2
          have hrhoNe : rho ≠ w := (Finset.mem_erase.mp hrho).1
          have hnear : |rho.im - w.im| ≤ B := le_of_not_gt hfar
          rw [if_neg hfar]
          dsimp [f]
          rw [localizedGaussianWeight_nearZeroFilter_eq_zero
            (hzeros rho hrhoZeros) hrhoNe hnear]
          simp
      _ = ∑ rho ∈
          (zeros.erase w).filter (fun rho => B < |rho.im - w.im|),
            f rho := by
        rw [Finset.sum_filter]
      _ = ∑ rho ∈ zeros.filter (fun rho => B < |rho.im - w.im|),
            f rho := by
        congr 1
        ext rho
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_hrhoNe, hrho⟩, hfar⟩
          exact ⟨hrho, hfar⟩
        · rintro ⟨hrho, hfar⟩
          refine ⟨⟨?_, hrho⟩, hfar⟩
          intro hrhoEq
          subst rho
          simp at hfar
          linarith
  unfold localizedZeroResidueSum localizedFarZeroResidueSum
  change (∑ rho ∈ zeros, f rho) =
    (analyticOrderNatAt riemannZeta w : ℂ) +
      ∑ rho ∈ zeros.filter (fun rho => B < |rho.im - w.im|), f rho
  rw [← Finset.sum_erase_add _ _ hw, herase, htarget]
  ring

theorem ConcreteLocalizedContourSlice.isNontrivialZero_of_mem
    {A : ℂ[X]} {u v m : ℝ}
    (slice : ConcreteLocalizedContourSlice A u v m)
    {rho : ℂ} (hrho : rho ∈ slice.zeros) :
    RiemannHypothesis.IsNontrivialZero rho := by
  rcases slice.zeros_spec rho hrho with
    ⟨hzero, hreLower, _hreUpper, _himLower, _himUpper⟩
  have hrePos : 0 < rho.re := by
    by_contra hnot
    apply PrimeNumberTheorem.riemannZeta_ne_zero_of_re_le_zero
      (le_of_not_gt hnot)
    · intro n hrhoEq
      have hreEq := congrArg Complex.re hrhoEq
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      simp at hreEq
      linarith
    · exact hzero
  have hreLt : rho.re < 1 := by
    by_contra hnot
    exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hnot)) hzero
  exact ⟨hzero, hrePos, hreLt⟩

theorem ConcreteLocalizedContourSlice.center_mem
    {A : ℂ[X]} {u v m : ℝ}
    (slice : ConcreteLocalizedContourSlice A u v m)
    (hu : 0 < u) (hm : 0 < m)
    (hzero : riemannZeta ((u : ℂ) + I * v) = 0) :
    ((u : ℂ) + I * v) ∈ slice.zeros := by
  apply slice.zeros_complete ((u : ℂ) + I * v)
  · have hT : |v| < slice.height := by
      have hlower := slice.height_mem.1
      linarith
    have hvLower : -slice.height ≤ v := by
      linarith [neg_abs_le v]
    have hvUpper : v ≤ slice.height :=
      (le_abs_self v).trans hT.le
    rw [Complex.mem_reProdIm,
      Set.uIcc_of_le (by linarith [hu] : (-1 : ℝ) ≤ u + 2),
      Set.uIcc_of_le (by linarith [abs_nonneg v] :
        -slice.height ≤ slice.height)]
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im,
      I_im, zero_mul, one_mul, add_im, mul_im]
    constructor
    · constructor <;> linarith
    · exact ⟨by simpa using hvLower, by simpa using hvUpper⟩
  · exact hzero

/-- The selected far-zero sum associated with the fixed near-zero filter. -/
noncomputable def selectedLocalizedFarZeroResidueSum
    (u v B m : ℝ) : ℂ := by
  classical
  let w : ℂ := (u : ℂ) + I * v
  let A : ℂ[X] := localizedNearZeroFilter w B
  exact
    if hvalid : localizedContourScaleValid A u m then
      localizedFarZeroResidueSum A w m B
        (selectedConcreteLocalizedContourSlice A u v m hvalid).zeros
    else 0

/--
At every valid scale, the selected true-zeta zero sum for the fixed local
filter splits exactly into the target multiplicity and the selected far-zero
sum.
-/
theorem selectedLocalizedZeroResidueSum_nearZeroFilter_eq_target_add_far
    {u v B m : ℝ} (hB : 0 ≤ B)
    (hvalid :
      localizedContourScaleValid
        (localizedNearZeroFilter ((u : ℂ) + I * v) B) u m)
    (hzero : riemannZeta ((u : ℂ) + I * v) = 0) :
    selectedLocalizedZeroResidueSum
        (localizedNearZeroFilter ((u : ℂ) + I * v) B) u v m =
      (analyticOrderNatAt riemannZeta ((u : ℂ) + I * v) : ℂ) +
        selectedLocalizedFarZeroResidueSum u v B m := by
  let w : ℂ := (u : ℂ) + I * v
  let A : ℂ[X] := localizedNearZeroFilter w B
  let slice : ConcreteLocalizedContourSlice A u v m :=
    selectedConcreteLocalizedContourSlice A u v m hvalid
  rw [selectedLocalizedZeroResidueSum, dif_pos hvalid]
  rw [selectedLocalizedFarZeroResidueSum, dif_pos hvalid]
  change localizedZeroResidueSum A w m slice.zeros =
    (analyticOrderNatAt riemannZeta w : ℂ) +
      localizedFarZeroResidueSum A w m B slice.zeros
  apply localizedZeroResidueSum_nearZeroFilter_eq_target_add_far hB
  · exact slice.center_mem hvalid.1
      (lt_of_lt_of_le zero_lt_one hvalid.2.2.1) hzero
  · intro rho hrho
    exact slice.isNontrivialZero_of_mem hrho

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
