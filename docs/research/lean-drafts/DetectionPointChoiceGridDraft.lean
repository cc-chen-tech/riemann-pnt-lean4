/-
# DRAFT (uncompiled): L1 Appendix A — interval covering lemma, full proof

Paper proof: `docs/research/detection-point-choice-proof-draft.md`
(Appendix A, discrete grid double counting).

REVISION 2 of this draft fixes a real arithmetic trap: the ceiling-based
count `⌈2rM/H⌉ + 1` loses exactly the `1/2` slack that the contradiction
`M = 2n+1 > 2n + 1/2` needs (since `⌈M/2⌉ = n+1`, not `n + 1/2`).
The fix: keep the per-interval count as a REAL bound
`card ≤ 2 r M / H + 1` (integer count ≤ length + 1, exact), so the double
counting reads `M ≤ M/2 + n = 2n + 1/2 < M`.

All Mathlib lemmas verified in local sources (see
`L1-formalization-checklist.md`): `Int.card_Ioo`, `Int.floor_le`,
`Int.le_ceil`, `Int.lt_floor_add_one`, `Int.lt_ceil`.

-/
import Mathlib

namespace PrimeNumberTheorem.HalfIsolatedZeroDichotomy
namespace DetectionPointChoiceGrid

open scoped BigOperators

/-- Grid points `γ_k = T0 + (k + 1/2) · H / M`. -/
noncomputable def gridPoint (T0 H M : ℝ) (k : ℕ) : ℝ :=
  T0 + ((k : ℝ) + 1 / 2) * H / M

/-- Grid points are strictly increasing in `k` (for `0 < H`, `0 < M`). -/
lemma gridPoint_strictMono {T0 : ℝ} (hH : 0 < H) (hM : 0 < M) :
    StrictMono (fun k : ℕ => gridPoint T0 H M k) := by
  intro a b hab
  unfold gridPoint
  refine add_lt_add_left ?_ T0
  exact mul_lt_mul_of_pos_right
    (add_lt_add_right (Nat.cast_lt.mpr hab) (1 / 2)) (div_pos hH hM)

/-- Every grid point with `(k : ℝ) < M` lies in `[T0, T0 + H]`. -/
lemma gridPoint_mem_Icc {T0 : ℝ} (hH : 0 < H) (hM : 0 < M) {k : ℕ}
    (hk : (k : ℝ) < M) :
    T0 ≤ gridPoint T0 H M k ∧ gridPoint T0 H M k ≤ T0 + H := by
  unfold gridPoint
  have hnonneg : 0 ≤ ((k : ℝ) + 1 / 2) * H / M := by
    positivity
  have hleM : ((k : ℝ) + 1 / 2) ≤ M := by linarith
  have hle : ((k : ℝ) + 1 / 2) * H / M ≤ H := by
    calc
      ((k : ℝ) + 1 / 2) * H / M ≤ M * H / M := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hleM hH.le) hM.le
      _ = H := by field_simp [hM.ne']; ring
  exact ⟨by linarith [hnonneg], by linarith [hle]⟩

/-- Grid indices. -/
def gridIndices (M : ℕ) : Finset ℕ := Finset.range M

/-- Indices whose grid point lies in the open interval `(c - r, c + r)`. -/
noncomputable def coveredIndices (T0 H M : ℝ) (c r : ℝ) (K : Finset ℕ) : Finset ℕ :=
  K.filter fun k => |gridPoint T0 H M k - c| < r

/-- KEY COUNT LEMMA (real form): an interval of length `2r` contains at
most `2 r M / H + 1` grid points. -/
lemma coveredIndices_card_le (hH : 0 < H) (hM : 0 < M)
    (T0 c r : ℝ) (K : Finset ℕ) :
    ((coveredIndices T0 H M c r K).card : ℝ) ≤ 2 * r * M / H + 1 := by
  classical
  let a : ℝ := (c - r - T0) * M / H - 1 / 2
  let b : ℝ := (c + r - T0) * M / H - 1 / 2
  have hmem {k : ℕ} :
      k ∈ coveredIndices T0 H M c r K ↔ k ∈ K ∧ a < (k : ℝ) ∧ (k : ℝ) < b := by
    unfold coveredIndices gridPoint
    constructor
    · intro hk
      rcases Finset.mem_filter.mp hk with ⟨hkK, hlt⟩
      have hlt' : |T0 + ((k : ℝ) + 1 / 2) * H / M - c| < r := hlt
      rw [abs_lt] at hlt'
      rcases hlt' with ⟨hlo, hhi⟩
      refine ⟨hkK, ?_, ?_⟩
      · have hsub : c - r < T0 + ((k : ℝ) + 1 / 2) * H / M := by
          rw [sub_lt_iff_lt_add] at hlo
          exact hlo
        have hdiv : (c - r - T0) * M / H < (k : ℝ) + 1 / 2 := by
          have hpos : 0 < H / M := div_pos hH hM
          rw [← div_lt_iff₀ hpos] at hsub
          -- hsub : c - r - T0 < ((k+1/2)H)/M ; multiply by M/H? No:
          -- we need ((c-r-T0) * M / H < k + 1/2), i.e.
          --   (c-r-T0) < (k+1/2) * (H/M)  [hsub]
          --   (c-r-T0) * (M/H) < k + 1/2
          have hmul : (c - r - T0) * (M / H) < ((k : ℝ) + 1 / 2) * (H / M) * (M / H) :=
            mul_lt_mul_of_pos_right hsub (div_pos hM hH)
          have hcancel : ((k : ℝ) + 1 / 2) * (H / M) * (M / H) = (k : ℝ) + 1 / 2 := by
            field_simp [hH.ne', hM.ne']
          have hmul' : (c - r - T0) * (M / H) < (k : ℝ) + 1 / 2 := by
            simpa [hcancel] using hmul
          exact by simpa [div_eq_mul_inv] using hmul'
        exact sub_lt_iff_lt_add.mpr (by linarith [hdiv])
      · have hhi' : T0 + ((k : ℝ) + 1 / 2) * H / M < c + r := by
          rw [lt_add_iff_sub_lt] at hhi
          exact hhi
        have hdiv : (k : ℝ) + 1 / 2 < (c + r - T0) * M / H := by
          -- mirror of the above with upper side
          have hpos : 0 < H / M := div_pos hH hM
          have hshift : ((k : ℝ) + 1 / 2) * H / M < c + r - T0 := by
            exact sub_lt_iff_lt_add'.mpr (by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hhi')
          have hmul : ((k : ℝ) + 1 / 2) * (H / M) * (M / H) < (c + r - T0) * (M / H) :=
            mul_lt_mul_of_pos_right hshift (div_pos hM hH)
          have hcancel : ((k : ℝ) + 1 / 2) * (H / M) * (M / H) = (k : ℝ) + 1 / 2 := by
            field_simp [hH.ne', hM.ne']
          simpa [hcancel, div_eq_mul_inv] using hmul
        exact lt_add_iff_sub_lt.mpr (by linarith [hdiv])
    · intro hk
      rcases hk with ⟨hkK, hka, hkb⟩
      refine Finset.mem_filter.mpr ⟨hkK, ?_⟩
      rw [abs_lt]
      constructor
      · -- lower side: a < k  ⟹  c - r < gridPoint
        have hdiv : (c - r - T0) * M / H < (k : ℝ) + 1 / 2 := by linarith [hka]
        have hpos : 0 < H / M := div_pos hH hM
        have hmul : (c - r - T0) * (M / H) * (H / M) < ((k : ℝ) + 1 / 2) * (H / M) :=
          mul_lt_mul_of_pos_right hdiv hpos
        have hcancel : (c - r - T0) * (M / H) * (H / M) = c - r - T0 := by
          field_simp [hH.ne', hM.ne']
        have hsub : c - r - T0 < ((k : ℝ) + 1 / 2) * H / M := by
          rw [div_eq_mul_inv]
          simpa [hcancel] using hmul
        linarith
      · -- upper side symmetric
        have hdiv : (k : ℝ) + 1 / 2 < (c + r - T0) * M / H := by linarith [hkb]
        have hpos : 0 < H / M := div_pos hH hM
        have hmul : ((k : ℝ) + 1 / 2) * (H / M) < (c + r - T0) * (M / H) * (H / M) :=
          mul_lt_mul_of_pos_right hdiv hpos
        have hcancel : (c + r - T0) * (M / H) * (H / M) = c + r - T0 := by
          field_simp [hH.ne', hM.ne']
        have hsub : ((k : ℝ) + 1 / 2) * H / M < c + r - T0 := by
          rw [div_eq_mul_inv]
          simpa [hcancel] using hmul
        linarith
  -- integer count inside the open real interval (a, b):
  -- embed k ↦ (k : ℤ) into Int.Ioo ⌊a⌋ ⌈b⌉ injectively
  have himage :
      ∀ k ∈ coveredIndices T0 H M c r K, (k : ℤ) ∈ Int.Ioo (Int.floor a) (Int.ceil b) := by
    intro k hk
    rcases (hmem.mp hk).2 with ⟨hka, hkb⟩
    exact ⟨Int.floor_lt.mpr (by exact_mod_cast hka), Int.lt_ceil.mpr (by exact_mod_cast hkb)⟩
  have hcard_le_int :
      (coveredIndices T0 H M c r K).card ≤ (Int.Ioo (Int.floor a) (Int.ceil b)).card := by
    classical
    refine Finset.card_le_card_of_injOn (fun k : ℕ => (k : ℤ)) ?_ ?_
    · intro k hk
      exact himage k hk
    · intro x hx y hy hxy
      exact_mod_cast hxy
  have hcard_iio_bound :
      ((Int.Ioo (Int.floor a) (Int.ceil b)).card : ℝ) ≤ b - a := by
    -- classical integer-count fact: # integers in (a, b) ≤ b - a + 1... 
    -- CAUTION: the sharp fact used here is card ≤ b - a + 1;
    -- the REAL form below then reads card ≤ (b - a) + 1 = 2rM/H + 1.
    rw [Int.card_Ioo]
    have h1 : (Int.ceil b : ℤ) ≤ Int.ceil (b - a) + Int.floor a + 1 := by
      -- ⌈b⌉ ≤ ⌈b-a⌉ + ⌊a⌋ + 1  (since b = (b-a) + a and ⌈x+y⌉ ≤ ⌈x⌉+⌈y⌉+1)
      have := Int.ceil_add_le (b - a) a
      -- ⌈b⌉ ≤ ⌈b-a⌉ + ⌈a⌉  and ⌈a⌉ ≤ ⌊a⌋ + 1
      have ha : (Int.ceil a : ℤ) ≤ Int.floor a + 1 := Int.ceil_le_floor_add_one
      omega
    have h2 : ((Int.ceil b - Int.floor a - 1 : ℤ).toNat : ℝ) ≤ (Int.ceil b : ℤ) - Int.floor a - 1 := by
      exact_mod_cast (Int.toNat_le.mpr (by omega))
    calc
      ((Int.Ioo (Int.floor a) (Int.ceil b)).card : ℝ)
          = ((Int.ceil b - Int.floor a - 1 : ℤ).toNat : ℝ) := by rw [Int.card_Ioo]
      _ ≤ (Int.ceil b : ℤ) - Int.floor a - 1 := h2
      _ ≤ (Int.ceil (b - a) : ℤ) - 1 := by omega
      _ ≤ (b - a) := by
        have hceil : (Int.ceil (b - a) : ℤ) ≤ (b - a) + 1 := Int.ceil_le (by norm_num) (le_rfl)
        -- actually Int.ceil_le_add_one: ⌈x⌉ ≤ x + 1
        have := (Int.ceil_lt_add_one (b - a)).le
        linarith
  have hcard_le_real :
      ((coveredIndices T0 H M c r K).card : ℝ) ≤ b - a + 1 := by
    exact_mod_cast hcard_le_int.trans (by linarith [hcard_iio_bound])
  have hba : b - a = 2 * r * M / H := by
    dsimp [a, b]
    ring
  linarith

/-- MAIN TARGET: a finite family of open intervals of total length at most
`H / 2` cannot cover `[T0, T0+H]`. -/
theorem exists_point_avoiding_small_intervals
    {ι : Type*} [DecidableEq ι] (T0 H : ℝ) (I : Finset ι) (c : ι → ℝ) (r : ι → ℝ)
    (hH : 0 < H) (hr : ∀ i, 0 ≤ r i)
    (hsum : I.sum (fun i => 2 * r i) ≤ H / 2) :
    ∃ γ : ℝ, T0 ≤ γ ∧ γ ≤ T0 + H ∧ ∀ i ∈ I, r i ≤ |γ - c i| := by
  classical
  let n : ℕ := I.card
  let M : ℕ := 2 * n + 1
  let K : Finset ℕ := gridIndices M
  have hMpos : (0 : ℝ) < M := by dsimp [M]; positivity
  have hgrid {k : ℕ} (hk : k ∈ K) :
      T0 ≤ gridPoint T0 H M k ∧ gridPoint T0 H M k ≤ T0 + H := by
    have hkM : (k : ℝ) < M := by
      exact_mod_cast Finset.mem_range.mp hk
    exact gridPoint_mem_Icc hH hMpos hkM
  by_contra hnocover
  push_neg at hnocover
  have hcover {k : ℕ} (hk : k ∈ K) :
      k ∈ K.biUnion fun i => coveredIndices T0 H M (c i) (r i) K := by
    rcases hgrid hk with ⟨hT0, hT0H⟩
    rcases hnocover (gridPoint T0 H M k) hT0 hT0H with ⟨i, hi, hlt⟩
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hk, hlt⟩⟩
  have hKsub : K ⊆ K.biUnion fun i => coveredIndices T0 H M (c i) (r i) K := hcover
  have hcount :
      (M : ℝ) ≤ ∑ i ∈ I, ((coveredIndices T0 H M (c i) (r i) K).card : ℝ) := by
    calc
      (M : ℝ) = (K.card : ℝ) := by simp [K, gridIndices]
      _ ≤ (K.biUnion fun i => coveredIndices T0 H M (c i) (r i) K).card := by
        exact_mod_cast Finset.card_le_card hKsub
      _ ≤ (∑ i ∈ I, (coveredIndices T0 H M (c i) (r i) K).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
  have hper {i : ι} :
      ((coveredIndices T0 H M (c i) (r i) K).card : ℝ) ≤ 2 * r i * M / H + 1 :=
    coveredIndices_card_le hH hMpos T0 (c i) (r i) K
  have hfinal : (M : ℝ) ≤ M / 2 + I.card := by
    calc
      (M : ℝ) ≤ ∑ i ∈ I, ((coveredIndices T0 H M (c i) (r i) K).card : ℝ) := hcount
      _ ≤ ∑ i ∈ I, (2 * r i * M / H + 1) := by
        exact Finset.sum_le_sum (fun i _ => hper)
      _ = (M / H) * (I.sum fun i => 2 * r i) + I.card := by
        rw [← Finset.mul_sum]
        simp [Finset.sum_add_distrib, Finset.card_eq_sum_ones, div_eq_mul_inv]
        ring
      _ ≤ (M / H) * (H / 2) + I.card := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left hsum (by positivity)) I.card
      _ = M / 2 + I.card := by
        field_simp [hH.ne']
        ring
  have hM_eq : (M : ℝ) = 2 * I.card + 1 := by simp [M, n]
  have hMhalf : M / 2 = (I.card : ℝ) + 1 / 2 := by
    rw [hM_eq]
    ring
  nlinarith

end DetectionPointChoiceGrid
end PrimeNumberTheorem.HalfIsolatedZeroDichotomy
