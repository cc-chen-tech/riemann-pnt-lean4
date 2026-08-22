import Mathlib
import PrimeNumberTheorem.HalfIsolatedZeroDichotomy.Contract
import PrimeNumberTheorem.GlobalZeroCount
import PrimeNumberTheorem.RiemannVonMangoldt.AllHeightAsymptotic

/-!
# Detection-point choice for the windowed half-isolated detector

L1 of `docs/research/windowed-detector-lean-spec.md` (paper:
`docs/research/detection-point-choice-proof-draft.md`, revision 2).

Appendix A (the interval covering lemma) is proved here and replaces the
first axiom.  The remaining two `axiom`s are explicit unproved targets
(tracked by `Test/DetectionPointChoiceAxiomAudit.lean`); Appendix B and
the main assembly promote them later.
-/

namespace PrimeNumberTheorem
namespace HalfIsolatedZeroDichotomy

open scoped BigOperators
open Set
open RiemannVonMangoldt
open ExplicitFormulaAux

noncomputable section

/-- Frequency-weighted mass of a finite zero family at detection frequency
`γ`: the complementary-layer analogue of the detector envelope, with the
explicit `1 / |γ - Im ρ|` weight.  For non-zeros `analyticOrderNatAt` is
zero, so no zero hypothesis is needed on the family. -/
noncomputable def frequencyWeightedMass (complementary : Finset ℂ) (γ : ℝ) : ℝ :=
  ∑ ρ ∈ complementary,
    (analyticOrderNatAt riemannZeta ρ : ℝ) / (‖ρ‖ * |γ - ρ.im|)

/-! ## Appendix A: the interval covering lemma -/

/-- Grid points `γ_k = T0 + (k + 1/2) · H / M`. -/
noncomputable def gridPoint (T0 H M : ℝ) (k : ℕ) : ℝ :=
  T0 + ((k : ℝ) + 1 / 2) * H / M

/-- Grid points are strictly increasing in `k` (for `0 < H`, `0 < M`). -/
lemma gridPoint_strictMono {T0 : ℝ} (hH : 0 < H) (hM : 0 < M) :
    StrictMono (fun k : ℕ => gridPoint T0 H M k) := by
  intro a b hab
  have hab' : ((a : ℝ) + 1 / 2) * (H / M) < ((b : ℝ) + 1 / 2) * (H / M) := by
    have hlt : (a : ℝ) + 1 / 2 < (b : ℝ) + 1 / 2 := by
      exact add_lt_add_left (Nat.cast_lt.mpr hab) (1 / 2)
    exact mul_lt_mul_of_pos_right hlt (div_pos hH hM)
  simpa [gridPoint, div_eq_mul_inv, mul_assoc, add_comm, add_left_comm, add_assoc] using (add_lt_add_right hab' T0)

/-- Every grid point with `(k : ℝ) < M` lies in `[T0, T0 + H]`. -/
lemma gridPoint_mem_Icc {T0 : ℝ} (hH : 0 < H) {M : ℕ} (hM : 0 < M) {k : ℕ}
    (hk : k < M) :
    T0 ≤ gridPoint T0 H M k ∧ gridPoint T0 H M k ≤ T0 + H := by
  unfold gridPoint
  have hnonneg : 0 ≤ ((k : ℝ) + 1 / 2) * H / M := by
    positivity
  have hleM : ((k : ℝ) + 1 / 2) ≤ M := by
    have hk' : (k : ℝ) + 1 ≤ M := by exact_mod_cast hk
    linarith
  have hle : ((k : ℝ) + 1 / 2) * H / M ≤ H := by
    calc
      ((k : ℝ) + 1 / 2) * H / M ≤ M * H / M := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hleM hH.le)
          (by exact_mod_cast hM.le)
      _ = H := by
        field_simp [show (M : ℝ) ≠ 0 by exact_mod_cast hM.ne']
  exact ⟨by linarith [hnonneg], by linarith [hle]⟩

/-- Grid indices. -/
def gridIndices (M : ℕ) : Finset ℕ := Finset.range M

/-- Indices whose grid point lies in the open interval `(c - r, c + r)`. -/
noncomputable def coveredIndices (T0 H M : ℝ) (c r : ℝ) (K : Finset ℕ) : Finset ℕ :=
  K.filter fun k => |gridPoint T0 H M k - c| < r

/-- KEY COUNT LEMMA (real form): an interval of length `2r` contains at
most `2 r M / H + 1` grid points. -/
lemma coveredIndices_card_le (hH : 0 < H) (hM : 0 < M)
    (T0 c r : ℝ) (K : Finset ℕ) (hr : 0 ≤ r) :
    ((coveredIndices T0 H M c r K).card : ℝ) ≤ 2 * r * M / H + 1 := by
  classical
  by_cases hr0 : r = 0
  · subst hr0
    have hempty : coveredIndices T0 H M c 0 K = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hne
      rcases hne with ⟨k, hk⟩
      have hlt : |gridPoint T0 H M k - c| < (0 : ℝ) := (Finset.mem_filter.mp hk).2
      linarith [abs_nonneg (gridPoint T0 H M k - c)]
    simp [hempty]
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  let a : ℝ := (c - r - T0) * M / H - 1 / 2
  let b : ℝ := (c + r - T0) * M / H - 1 / 2
  have hkLower {k : ℕ} (hk : k ∈ coveredIndices T0 H M c r K) : a < (k : ℝ) := by
    rcases Finset.mem_filter.mp hk with ⟨_, hlt⟩
    unfold gridPoint at hlt
    have h1 : c - r < T0 + ((k : ℝ) + 1 / 2) * H / M := by
      linarith [(abs_lt.mp hlt).1]
    dsimp [a]
    field_simp [hH.ne', hM.ne'] at h1 ⊢
    ring_nf at h1 ⊢
    nlinarith
  have hkUpper {k : ℕ} (hk : k ∈ coveredIndices T0 H M c r K) : (k : ℝ) < b := by
    rcases Finset.mem_filter.mp hk with ⟨_, hlt⟩
    unfold gridPoint at hlt
    have h1 : T0 + ((k : ℝ) + 1 / 2) * H / M < c + r := by
      linarith [(abs_lt.mp hlt).2]
    dsimp [b]
    field_simp [hH.ne', hM.ne'] at h1 ⊢
    ring_nf at h1 ⊢
    nlinarith

  -- integer count inside the open real interval (a, b)
  have himage :
      ∀ k ∈ coveredIndices T0 H M c r K, (k : ℤ) ∈ Finset.Ioo (Int.floor a) (Int.ceil b) := by
    intro k hk
    exact Finset.mem_Ioo.mpr
      ⟨Int.floor_lt.mpr (by exact_mod_cast hkLower hk),
       Int.lt_ceil.mpr (by exact_mod_cast hkUpper hk)⟩
  have hcard_le_int :
      (coveredIndices T0 H M c r K).card ≤ (Finset.Ioo (Int.floor a) (Int.ceil b)).card := by
    classical
    refine Finset.card_le_card_of_injOn (fun k : ℕ => (k : ℤ)) ?_ ?_
    · intro k hk
      exact himage k hk
    · intro x hx y hy hxy
      exact Nat.cast_inj.mp hxy
  have hcard_iio_bound :
      ((Finset.Ioo (Int.floor a) (Int.ceil b)).card : ℝ) ≤ b - a + 1 := by
    have hba_pos : a < b := by
      dsimp [a, b]
      field_simp [hH.ne', hM.ne']
      ring_nf
      nlinarith [hrpos, hH, hM]
    have hab : Int.floor a < Int.ceil b := Int.floor_lt_ceil_of_lt hba_pos
    have hcard := Int.card_Ioo_of_lt (a := Int.floor a) (b := Int.ceil b) hab
    have hcardR : (↑(Finset.Ioo (Int.floor a) (Int.ceil b)).card : ℝ) =
        ((Int.ceil b - Int.floor a - 1 : ℤ) : ℝ) := by
      exact_mod_cast hcard
    rw [hcardR]
    have hz : (Int.ceil b - Int.floor a - 1 : ℤ) ≤ Int.ceil (b - a) := by
      have h1 : (Int.ceil b : ℤ) ≤ Int.ceil (b - a) + Int.ceil a := by
        have hce := Int.ceil_add_le (b - a) a
        simpa [add_comm, add_left_comm, add_assoc] using hce
      have h2 : (Int.ceil a : ℤ) ≤ Int.floor a + 1 := Int.ceil_le_floor_add_one a
      omega
    have hzR : ((Int.ceil b - Int.floor a - 1 : ℤ) : ℝ) ≤ b - a + 1 := by
      have h3 : ((Int.ceil (b - a) : ℤ) : ℝ) ≤ b - a + 1 := by
        have h4 : (Int.ceil (b - a) : ℤ) < (b - a) + 1 := Int.ceil_lt_add_one (b - a)
        linarith
      have h5 : ((Int.ceil b - Int.floor a - 1 : ℤ) : ℝ) ≤ ((Int.ceil (b - a) : ℤ) : ℝ) := by
        exact_mod_cast hz
      linarith
    simpa [hcardR] using hzR
  have hcard_le_real :
      ((coveredIndices T0 H M c r K).card : ℝ) ≤ b - a + 1 := by
    have h1 : ((coveredIndices T0 H M c r K).card : ℝ) ≤
        ((Finset.Ioo (Int.floor a) (Int.ceil b)).card : ℝ) := by
      exact_mod_cast hcard_le_int
    exact h1.trans hcard_iio_bound
  have hba : b - a = 2 * r * M / H := by
    dsimp [a, b]
    ring
  linarith

/-- MAIN TARGET (Appendix A): a finite family of open intervals of total
length at most `H / 2` cannot cover `[T0, T0+H]`. -/
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
    exact gridPoint_mem_Icc hH (by dsimp [M]; omega) (Finset.mem_range.mp hk)
  by_contra hnocover
  push_neg at hnocover
  have hcover {k : ℕ} (hk : k ∈ K) :
      k ∈ I.biUnion fun i => coveredIndices T0 H M (c i) (r i) K := by
    rcases hgrid hk with ⟨hT0, hT0H⟩
    rcases hnocover (gridPoint T0 H M k) hT0 hT0H with ⟨i, hi, hlt⟩
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hk, hlt⟩⟩
  have hKsub : K ⊆ I.biUnion fun i => coveredIndices T0 H M (c i) (r i) K := by
    intro k hk
    exact hcover hk
  have hcount :
      (M : ℝ) ≤ ∑ i ∈ I, ((coveredIndices T0 H M (c i) (r i) K).card : ℝ) := by
    calc
      (M : ℝ) = (K.card : ℝ) := by simp [K, gridIndices]
      _ ≤ (I.biUnion fun i => coveredIndices T0 H M (c i) (r i) K).card := by
        exact_mod_cast Finset.card_le_card hKsub
      _ ≤ (∑ i ∈ I, (coveredIndices T0 H M (c i) (r i) K).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
  have hper {i : ι} :
      ((coveredIndices T0 H M (c i) (r i) K).card : ℝ) ≤ 2 * r i * M / H + 1 :=
    coveredIndices_card_le hH hMpos T0 (c i) (r i) K (hr i)
  have hfinal : (M : ℝ) ≤ M / 2 + I.card := by
    calc
      (M : ℝ) ≤ ∑ i ∈ I, ((coveredIndices T0 H M (c i) (r i) K).card : ℝ) := hcount
      _ ≤ ∑ i ∈ I, (2 * r i * M / H + 1) := by
        exact Finset.sum_le_sum (fun i _ => hper)
      _ = (M / H) * (I.sum fun i => 2 * r i) + I.card := by
        have h1 : (∑ i ∈ I, (2 * r i * M / H + 1)) =
            (∑ i ∈ I, 2 * r i * M / H) + I.card := by
          rw [Finset.sum_add_distrib]
          simp
        rw [h1]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        field_simp
      _ ≤ (M / H) * (H / 2) + I.card := by
        gcongr
      _ = M / 2 + I.card := by
        field_simp [hH.ne']
  have hM_eq : (M : ℝ) = 2 * I.card + 1 := by simp [M, n]
  have hMhalf : M / 2 = (I.card : ℝ) + 1 / 2 := by
    rw [hM_eq]
    ring
  nlinarith

/-! ## Appendix B: windowed zero count (proved) -/

/-- The main-term difference over `[T0, T0+H]` is bounded by `H` times a
logarithmic factor, for `8 <= T0`. -/
lemma abs_mainTerm_sub_le_mul_log_of_interval
    {T0 H : ℝ} (hT0 : 8 ≤ T0) (hH : 0 ≤ H) :
    |riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0| ≤
      H * (1 + Real.log (T0 + H + 6)) := by
  by_cases hH0 : H = 0
  · subst hH0; simp
  · have hHpos : 0 < H := lt_of_le_of_ne hH (Ne.symm hH0)
    have hT0pos : 0 < T0 := by linarith
    let C : ℝ := 1 + Real.log (T0 + H + 6)
    have hC0 : 0 ≤ C := by
      dsimp [C]
      have hlog : 0 ≤ Real.log (T0 + H + 6) := Real.log_nonneg (by linarith)
      linarith
    have hdiff : DifferentiableOn ℝ riemannVonMangoldtMainTerm (Icc T0 (T0 + H)) := by
      intro x hx
      have hx0 : x ≠ 0 := by
        have : 8 ≤ x := le_trans hT0 hx.1
        linarith
      exact (hasDerivAt_riemannVonMangoldtMainTerm hx0).differentiableAt.differentiableWithinAt
    have hbound : ∀ x ∈ Ico T0 (T0 + H),
        ‖(fun y : ℝ => Real.log (y / (2 * Real.pi)) / (2 * Real.pi)) x‖ ≤ C := by
      intro x hx
      have hxpi : 1 ≤ x / (2 * Real.pi) := by
        have h1 : 8 / (2 * Real.pi) ≤ x / (2 * Real.pi) :=
          div_le_div_of_nonneg_right (le_trans hT0 hx.1) (by positivity : 0 ≤ (2 * Real.pi))
        have h2 : 1 ≤ 8 / (2 * Real.pi) := by
          have : (2 : ℝ) * Real.pi ≤ 8 := by nlinarith [Real.pi_le_four]
          exact (one_le_div (by positivity : 0 < 2 * Real.pi)).mpr this
        calc
          (1 : ℝ) ≤ 8 / (2 * Real.pi) := h2
          _ ≤ x / (2 * Real.pi) := h1
      have hlog_nonneg : 0 ≤ Real.log (x / (2 * Real.pi)) := Real.log_nonneg hxpi
      have hlog_le : Real.log (x / (2 * Real.pi)) ≤ Real.log (T0 + H + 6) := by
        apply Real.log_le_log
        · positivity
        · calc
            x / (2 * Real.pi) ≤ x := by
              exact div_le_self (show 0 ≤ x by linarith [hT0, hx.1])
                (show 1 ≤ 2 * Real.pi by nlinarith [Real.pi_gt_three])
            _ ≤ T0 + H + 6 := by linarith [hx.2]
      calc
        ‖Real.log (x / (2 * Real.pi)) / (2 * Real.pi)‖
            = Real.log (x / (2 * Real.pi)) / (2 * Real.pi) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlog_nonneg (by positivity))]
        _ ≤ Real.log (T0 + H + 6) := by
          calc
            Real.log (x / (2 * Real.pi)) / (2 * Real.pi) ≤ Real.log (x / (2 * Real.pi)) := by
              exact div_le_self hlog_nonneg (show 1 ≤ 2 * Real.pi by nlinarith [Real.pi_gt_three])
            _ ≤ Real.log (T0 + H + 6) := hlog_le
        _ ≤ C := by
          dsimp [C]
          linarith [Real.log_nonneg (show 1 ≤ T0 + H + 6 by linarith [hT0])]
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := riemannVonMangoldtMainTerm)
      (f' := fun y : ℝ => Real.log (y / (2 * Real.pi)) / (2 * Real.pi))
      (a := T0) (b := T0 + H) (C := C)
      (by
        intro x hx
        have hx0 : x ≠ 0 := by
          have : 8 ≤ x := le_trans hT0 hx.1
          linarith
        exact (hasDerivAt_riemannVonMangoldtMainTerm hx0).hasDerivWithinAt)
      hbound (T0 + H) (by exact ⟨le_of_lt (lt_add_of_pos_right T0 hHpos), le_rfl⟩)
    simpa [C, mul_comm, mul_left_comm, mul_assoc] using hmv

/-- Windowed positive-side zero count: `N(T0+H) - N(T0)` is bounded by
`C (H log + log)`.  This replaces the former I2 axiom (Appendix B). -/
theorem exists_windowedZeroMultiplicity_le
    (T0 H : ℝ) (hT0 : 8 ≤ T0) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧
      ((riemannZeroCount (T0 + H) : ℝ) - riemannZeroCount T0) ≤
        C * (H * (1 + Real.log (T0 + H + 6)) + (1 + Real.log (T0 + H + 6))) := by
  rcases exists_abs_riemannZeroCount_sub_mainTerm_le_log with ⟨C0, hC0, hb⟩
  let L : ℝ := 1 + Real.log (T0 + H + 6)
  have hlogL : 0 ≤ Real.log (T0 + H + 6) := Real.log_nonneg (by linarith)
  have hL0 : 0 ≤ L := by dsimp [L]; linarith [hlogL]
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [hlogL]
  have hT0H : 8 ≤ T0 + H := le_trans hT0 (by linarith [hH])
  have hNsub :
      ((riemannZeroCount (T0 + H) : ℝ) - riemannZeroCount T0) ≤
        |riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0|
          + C0 * L + C0 * (1 + Real.log (T0 + 6)) := by
    have hbH := hb (T0 + H) hT0H
    have hb0 := hb T0 hT0
    have hdiff_eq :
        (riemannZeroCount (T0 + H) : ℝ) - riemannZeroCount T0 =
          (riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0)
            + ((riemannZeroCount (T0 + H) : ℝ) - riemannVonMangoldtMainTerm (T0 + H))
            - ((riemannZeroCount T0 : ℝ) - riemannVonMangoldtMainTerm T0) := by
      ring
    rw [hdiff_eq]
    have h1 : (riemannZeroCount (T0 + H) : ℝ) - riemannVonMangoldtMainTerm (T0 + H)
        ≤ |(riemannZeroCount (T0 + H) : ℝ) - riemannVonMangoldtMainTerm (T0 + H)| :=
      le_abs_self _
    have h2 : -((riemannZeroCount T0 : ℝ) - riemannVonMangoldtMainTerm T0)
        ≤ |(riemannZeroCount T0 : ℝ) - riemannVonMangoldtMainTerm T0| :=
      neg_le_abs _
    calc
      (riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0)
            + ((riemannZeroCount (T0 + H) : ℝ) - riemannVonMangoldtMainTerm (T0 + H))
            - ((riemannZeroCount T0 : ℝ) - riemannVonMangoldtMainTerm T0)
        ≤ |riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0|
            + |(riemannZeroCount (T0 + H) : ℝ) - riemannVonMangoldtMainTerm (T0 + H)|
            + |(riemannZeroCount T0 : ℝ) - riemannVonMangoldtMainTerm T0| := by
          have hm : riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0
              ≤ |riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0| :=
            le_abs_self _
          linarith [hm, h1, h2]
        _ ≤ |riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0|
            + C0 * L + C0 * (1 + Real.log (T0 + 6)) := by
          linarith [hbH, hb0]
  have hmain : |riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0| ≤
      H * L := by
    simpa [L] using abs_mainTerm_sub_le_mul_log_of_interval hT0 hH
  have hlog : 1 + Real.log (T0 + 6) ≤ L := by
    dsimp [L]
    gcongr
    all_goals linarith
  refine ⟨2 * C0 + 1, by positivity, ?_⟩
  calc
    (riemannZeroCount (T0 + H) : ℝ) - riemannZeroCount T0 ≤
        |riemannVonMangoldtMainTerm (T0 + H) - riemannVonMangoldtMainTerm T0|
          + C0 * L + C0 * (1 + Real.log (T0 + 6)) := hNsub
    _ ≤ H * L + C0 * L + C0 * L := by
      have hlog_mul : C0 * (1 + Real.log (T0 + 6)) ≤ C0 * L :=
        mul_le_mul_of_nonneg_left hlog hC0
      linarith [hmain, hlog_mul]
    _ = H * L + 2 * C0 * L := by ring
    _ ≤ (2 * C0 + 1) * (H * L + L) := by
      have hC0HL : 0 ≤ C0 * (H * L) := mul_nonneg hC0 (mul_nonneg hH hL0)
      nlinarith [hC0HL, hL0]
/-- Uniform windowed count: for every window `[a, b]` with `8 ≤ a`, the
difference `N(b) - N(a)` is bounded by a single constant times
`(b-a) log + log`.  Same proof as `exists_windowedZeroMultiplicity_le`
with `T0 ↦ a`, `H ↦ b - a`, so the constant is the same explicit
`2 C0 + 1`. -/
theorem exists_windowedZeroMultiplicity_le_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, 8 ≤ a → a ≤ b →
      (riemannZeroCount b : ℝ) - riemannZeroCount a ≤
        C * ((b - a) * (1 + Real.log (b + 6)) + (1 + Real.log (b + 6))) := by
  rcases exists_abs_riemannZeroCount_sub_mainTerm_le_log with ⟨C0, hC0, hb⟩
  refine ⟨2 * C0 + 1, by positivity, ?_⟩
  intro a b ha hab
  have hH : 0 ≤ b - a := sub_nonneg.mpr hab
  let L : ℝ := 1 + Real.log (b + 6)
  have hlogL : 0 ≤ Real.log (b + 6) := Real.log_nonneg (by linarith)
  have hL0 : 0 ≤ L := by dsimp [L]; linarith [hlogL]
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [hlogL]
  have hb8 : 8 ≤ b := le_trans ha hab
  have hNsub :
      ((riemannZeroCount b : ℝ) - riemannZeroCount a) ≤
        |riemannVonMangoldtMainTerm b - riemannVonMangoldtMainTerm a|
          + C0 * L + C0 * (1 + Real.log (a + 6)) := by
    have hbH := hb b hb8
    have hb0 := hb a ha
    have hdiff_eq :
        (riemannZeroCount b : ℝ) - riemannZeroCount a =
          (riemannVonMangoldtMainTerm b - riemannVonMangoldtMainTerm a)
            + ((riemannZeroCount b : ℝ) - riemannVonMangoldtMainTerm b)
            - ((riemannZeroCount a : ℝ) - riemannVonMangoldtMainTerm a) := by
      ring
    rw [hdiff_eq]
    have h1 : (riemannZeroCount b : ℝ) - riemannVonMangoldtMainTerm b
        ≤ |(riemannZeroCount b : ℝ) - riemannVonMangoldtMainTerm b| :=
      le_abs_self _
    have h2 : -((riemannZeroCount a : ℝ) - riemannVonMangoldtMainTerm a)
        ≤ |(riemannZeroCount a : ℝ) - riemannVonMangoldtMainTerm a| :=
      neg_le_abs _
    calc
      (riemannVonMangoldtMainTerm b - riemannVonMangoldtMainTerm a)
            + ((riemannZeroCount b : ℝ) - riemannVonMangoldtMainTerm b)
            - ((riemannZeroCount a : ℝ) - riemannVonMangoldtMainTerm a)
        ≤ |riemannVonMangoldtMainTerm b - riemannVonMangoldtMainTerm a|
            + |(riemannZeroCount b : ℝ) - riemannVonMangoldtMainTerm b|
            + |(riemannZeroCount a : ℝ) - riemannVonMangoldtMainTerm a| := by
          have hm : riemannVonMangoldtMainTerm b - riemannVonMangoldtMainTerm a
              ≤ |riemannVonMangoldtMainTerm b - riemannVonMangoldtMainTerm a| :=
            le_abs_self _
          linarith [hm, h1, h2]
        _ ≤ |riemannVonMangoldtMainTerm b - riemannVonMangoldtMainTerm a|
            + C0 * L + C0 * (1 + Real.log (a + 6)) := by
          linarith [hbH, hb0]
  have hmain : |riemannVonMangoldtMainTerm b - riemannVonMangoldtMainTerm a| ≤
      (b - a) * L := by
    simpa [L] using abs_mainTerm_sub_le_mul_log_of_interval ha hH
  have hlog : 1 + Real.log (a + 6) ≤ L := by
    dsimp [L]
    gcongr
    all_goals linarith
  calc
    (riemannZeroCount b : ℝ) - riemannZeroCount a ≤
        |riemannVonMangoldtMainTerm b - riemannVonMangoldtMainTerm a|
          + C0 * L + C0 * (1 + Real.log (a + 6)) := hNsub
    _ ≤ (b - a) * L + C0 * L + C0 * L := by
      have hlog_mul : C0 * (1 + Real.log (a + 6)) ≤ C0 * L :=
        mul_le_mul_of_nonneg_left hlog hC0
      linarith [hmain, hlog_mul]
    _ = (b - a) * L + 2 * C0 * L := by ring
    _ ≤ (2 * C0 + 1) * ((b - a) * L + L) := by
      have hC0HL : 0 ≤ C0 * ((b - a) * L) := mul_nonneg hC0 (mul_nonneg hH hL0)
      nlinarith [hC0HL, hL0]


/-! ## Main assembly (proved, replaces the last axiom) -/

/-- Ring mass: for a ring `2^k η ≤ |γ - Im ρ| < 2^(k+1) η`, the total
multiplicity inside is bounded by the windowed count on the enclosing
height window `[max(T0/2, γ - 2^(k+1) η), γ + 2^(k+1) η]`.  Members enter
`positiveNontrivialZerosBetween` through the strict lower endpoint
`T0/2 < Im ρ`, so no boundary slab is needed. -/
lemma ringMass_le_windowedCount
    {T0 T1 : ℝ} (Cw : ℝ) (γ η : ℝ) (k : ℕ)
    (hwin : ∀ a b : ℝ, T0 / 2 ≤ a → a ≤ b →
      (riemannZeroCount b : ℝ) - riemannZeroCount a ≤
        Cw * ((b - a) * (1 + Real.log (b + 6)) + (1 + Real.log (b + 6))))
    (hCw : 0 ≤ Cw) (hη : 0 < η) (ring : Finset ℂ)
    (hT0 : 16 ≤ T0)
    (hzero : ∀ ρ ∈ ring, RiemannHypothesis.IsNontrivialZero ρ)
    (hhigh : ∀ ρ ∈ ring, T0 / 2 < ρ.im)
    (hγ : T0 ≤ γ) (hγle : γ ≤ T1)
    (hk : 2 ^ (k + 1) * η ≤ 8 * T1 + 48)
    (hringmem : ∀ ρ ∈ ring, 2 ^ k * η ≤ |γ - ρ.im| ∧ |γ - ρ.im| < 2 ^ (k + 1) * η) :
    (ring.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
      Cw * (1 + Real.log 9) * (4 * 2 ^ k * η * (1 + Real.log (T1 + 6)) + 3 * (1 + Real.log (T1 + 6))) := by
  let a : ℝ := max (T0 / 2) (γ - 2 ^ (k + 1) * η)
  let b : ℝ := γ + 2 ^ (k + 1) * η
  have ha : T0 / 2 ≤ a := by
    dsimp [a]
    exact le_max_left _ _
  have ha_pos : 0 ≤ a := by
    dsimp [a]
    exact (by linarith : 0 ≤ T0 / 2).trans (le_max_left _ _)
  have hmem_between {ρ : ℂ} (hρ : ρ ∈ ring) :
      ρ ∈ positiveNontrivialZerosBetween a b := by
    have hmem := hringmem ρ hρ
    refine (mem_positiveNontrivialZerosBetween ha_pos).mpr ⟨hzero ρ hρ, ?_, ?_⟩
    · -- a < ρ.im
      have h1 : γ - 2 ^ (k + 1) * η < ρ.im := by
        nlinarith [(abs_lt.mp hmem.2).2]
      have h2 : T0 / 2 < ρ.im := hhigh ρ hρ
      dsimp [a]
      rw [max_lt_iff]
      exact ⟨h2, h1⟩
    · -- ρ.im ≤ b
      have hlt : ρ.im - γ < 2 ^ (k + 1) * η := by
        nlinarith [(abs_lt.mp hmem.2).1]
      dsimp [b]
      nlinarith [hlt]
  have hsum_le :
      (ring.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        ∑ ρ ∈ positiveNontrivialZerosBetween a b,
          (analyticOrderNatAt riemannZeta ρ : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => hmem_between hρ)
      (fun ρ _ _ => by exact_mod_cast Nat.zero_le _)
  have hab' : a ≤ b := by
    dsimp [a, b]
    exact max_le (by nlinarith [hT0, hγ, (by positivity : 0 ≤ 2 ^ (k + 1) * η)])
      (by linarith [(by positivity : 0 ≤ 2 ^ (k + 1) * η)])
  have hsub_eq := riemannZeroCount_sub_eq_between (U := a) (T := b) (by
    dsimp [a, b]
    nlinarith [hT0, hγ, (by positivity : 0 ≤ 2 ^ (k + 1) * η)])
  have hwin' := hwin a b ha hab'
  have hb_a : b - a ≤ 4 * 2 ^ k * η := by
    dsimp [a, b]
    have h1 : b - a ≤ (γ + 2 ^ (k + 1) * η) - (γ - 2 ^ (k + 1) * η) := by
      have ha' : γ - 2 ^ (k + 1) * η ≤ a := le_max_right _ _
      nlinarith [ha']
    have hpow' : (2 : ℝ) ^ (k + 2) = 4 * 2 ^ k := by
      rw [show k + 2 = k + 1 + 1 by omega, pow_succ, pow_succ]
      ring
    calc
      b - a ≤ (γ + 2 ^ (k + 1) * η) - (γ - 2 ^ (k + 1) * η) := h1
      _ = 2 ^ (k + 2) * η := by ring
      _ = 4 * 2 ^ k * η := by rw [hpow']
  have hbT1 : b + 6 ≤ 9 * (T1 + 6) := by
    dsimp [b]
    have h1 : γ + 2 ^ (k + 1) * η ≤ T1 + (8 * T1 + 48) := by
      nlinarith [hγle, hk]
    nlinarith [h1]
  have hLb_le : 1 + Real.log (b + 6) ≤ (1 + Real.log 9) * (1 + Real.log (T1 + 6)) := by
    have hbpos : 0 < b + 6 := by
      dsimp [b]
      linarith [hγ, hT0, (by positivity : 0 ≤ 2 ^ (k + 1) * η)]
    have hlog : Real.log (b + 6) ≤ Real.log (9 * (T1 + 6)) :=
      Real.log_le_log hbpos hbT1
    have hlog9 : Real.log (9 * (T1 + 6)) = Real.log 9 + Real.log (T1 + 6) := by
      rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) (by linarith [hγ, hγle, hT0] : (T1 + 6) ≠ 0)]
    have hlog' : Real.log (b + 6) ≤ Real.log 9 + Real.log (T1 + 6) := by
      simpa [hlog9] using hlog
    have hlogT : 0 ≤ Real.log (T1 + 6) := Real.log_nonneg (by linarith [hγ, hγle, hT0] : 1 ≤ T1 + 6)
    have hlog9nn : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num : 1 ≤ (9 : ℝ))
    nlinarith [hlog', hlogT, hlog9nn]
  calc
    (ring.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        ∑ ρ ∈ positiveNontrivialZerosBetween a b,
          (analyticOrderNatAt riemannZeta ρ : ℝ) := hsum_le
    _ = (riemannZeroCount b : ℝ) - riemannZeroCount a := by
      rw [← Nat.cast_sub (riemannZeroCount_mono (by
        dsimp [a, b]
        nlinarith [hT0, hγ, (by positivity : 0 ≤ 2 ^ (k + 1) * η)]))]
      simpa using (congrArg (fun n : ℕ => (n : ℝ)) hsub_eq.symm)
    _ ≤ Cw * ((b - a) * (1 + Real.log (b + 6)) + (1 + Real.log (b + 6))) := hwin'
    _ ≤ Cw * ((1 + Real.log 9) * (4 * 2 ^ k * η * (1 + Real.log (T1 + 6)) + 3 * (1 + Real.log (T1 + 6)))) := by
      have hL : 0 ≤ 1 + Real.log (T1 + 6) := by
        linarith [Real.log_nonneg (by linarith [hγ, hγle, hT0] : 1 ≤ T1 + 6)]
      have hLb : 0 ≤ 1 + Real.log (b + 6) := by
        linarith [Real.log_nonneg (by
          dsimp [b]
          linarith [hT0, hγ, (by positivity : 0 ≤ 2 ^ (k + 1) * η)] : 1 ≤ b + 6)]
      have hA : (b - a) * (1 + Real.log (b + 6)) ≤
          (1 + Real.log 9) * (4 * 2 ^ k * η * (1 + Real.log (T1 + 6))) := by
        calc
          (b - a) * (1 + Real.log (b + 6)) ≤ (4 * 2 ^ k * η) * (1 + Real.log (b + 6)) := by
            exact mul_le_mul_of_nonneg_right hb_a hLb
          _ ≤ (4 * 2 ^ k * η) * ((1 + Real.log 9) * (1 + Real.log (T1 + 6))) := by
            exact mul_le_mul_of_nonneg_left hLb_le (by positivity : 0 ≤ 4 * 2 ^ k * η)
          _ = (1 + Real.log 9) * (4 * 2 ^ k * η * (1 + Real.log (T1 + 6))) := by ring
      have hB : 1 + Real.log (b + 6) ≤
          (1 + Real.log 9) * (3 * (1 + Real.log (T1 + 6))) := by
        have h1 : (1 + Real.log 9) * (1 + Real.log (T1 + 6)) ≤
            (1 + Real.log 9) * (3 * (1 + Real.log (T1 + 6))) := by
          have hlog9nn : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num : 1 ≤ (9 : ℝ))
          nlinarith [hL, hlog9nn]
        linarith [hLb_le, h1]
      have hsum : (b - a) * (1 + Real.log (b + 6)) + (1 + Real.log (b + 6)) ≤
          (1 + Real.log 9) * (4 * 2 ^ k * η * (1 + Real.log (T1 + 6)) + 3 * (1 + Real.log (T1 + 6))) := by
        nlinarith [hA, hB]
      exact mul_le_mul_of_nonneg_left hsum hCw
    _ = Cw * (1 + Real.log 9) * (4 * 2 ^ k * η * (1 + Real.log (T1 + 6)) + 3 * (1 + Real.log (T1 + 6))) := by
      ring

/-- Dyadic distance-sum bound (high region). -/
lemma dyadic_distance_sum_le
    (T0 H : ℝ) (complementary : Finset ℂ) (γ : ℝ) (η : ℝ)
    (hT0 : 16 ≤ T0) (hH1 : 1 ≤ H) (hHle : H ≤ T0)
    (hη : 0 < η) (hηle : η ≤ T0 + H)
    (havoid : ∀ ρ ∈ complementary, η ≤ |γ - ρ.im|)
    (hzero : ∀ ρ ∈ complementary, RiemannHypothesis.IsNontrivialZero ρ)
    (hhigh : ∀ ρ ∈ complementary, T0 / 2 < ρ.im)
    (him_le : ∀ ρ ∈ complementary, ρ.im ≤ T0 + H)
    (hγ : T0 ≤ γ) (hγle : γ ≤ T0 + H)
    (hwin :
      ∃ C, 0 ≤ C ∧ ∀ a b : ℝ, T0 / 2 ≤ a → a ≤ b →
        (riemannZeroCount b : ℝ) - riemannZeroCount a ≤
          C * ((b - a) * (1 + Real.log (b + 6)) + (1 + Real.log (b + 6)))) :
    ∃ C, 0 ≤ C ∧
      (complementary.sum fun ρ =>
        (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤
        C * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / H := by
  rcases hwin with ⟨Cw, hCw, hwin'⟩
  let T1 : ℝ := T0 + H
  let L : ℝ := 1 + Real.log (T1 + 6)
  have hT1pos : 0 < T1 := by dsimp [T1]; linarith
  have hLpos : 0 < L := by
    dsimp [L]
    linarith [Real.log_nonneg (by linarith : 1 ≤ T1 + 6)]
  have hL1 : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg (by linarith : 1 ≤ T1 + 6)]
  let K : ℕ := Nat.ceil (Real.log (T1 / η) / Real.log 2) + 2
  have hringMass {k : ℕ} (hk : k < K) :
      ((complementary.filter fun ρ => 2 ^ k * η ≤ |γ - ρ.im| ∧ |γ - ρ.im| < 2 ^ (k + 1) * η).sum
        (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ))) ≤
        Cw * (1 + Real.log 9) * (4 * 2 ^ k * η * L + 3 * L) := by
    have hk' : 2 ^ (k + 1) * η ≤ 8 * T1 + 48 := by
      have hk_le : k + 1 ≤ Nat.ceil (Real.log (T1 / η) / Real.log 2) + 2 := by
        dsimp [K] at hk
        omega
      have hpow1 : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (Nat.ceil (Real.log (T1 / η) / Real.log 2) + 2) := by
        exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hk_le
      have hpow2 : (2 : ℝ) ^ (Nat.ceil (Real.log (T1 / η) / Real.log 2) + 2) ≤
          (2 : ℝ) ^ (Real.log (T1 / η) / Real.log 2 + 3) := by
        have h1 : ((Nat.ceil (Real.log (T1 / η) / Real.log 2) + 2 : ℕ) : ℝ) ≤
            Real.log (T1 / η) / Real.log 2 + 3 := by
          have hc : ((Nat.ceil (Real.log (T1 / η) / Real.log 2) : ℕ) : ℝ) ≤
              Real.log (T1 / η) / Real.log 2 + 1 := by
            have hx : 0 ≤ Real.log (T1 / η) / Real.log 2 := by
              apply div_nonneg _ (Real.log_nonneg (by norm_num : 1 ≤ (2 : ℝ)))
              exact Real.log_nonneg ((one_le_div hη).mpr (by dsimp [T1]; exact hηle))
            exact (Nat.ceil_lt_add_one hx).le
          norm_num
          linarith
        have hpow2' : (2 : ℝ) ^ ((Nat.ceil (Real.log (T1 / η) / Real.log 2) + 2 : ℕ) : ℝ) ≤
            (2 : ℝ) ^ (Real.log (T1 / η) / Real.log 2 + 3) := by
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2 : ℝ)) h1
        simpa only [Real.rpow_natCast] using hpow2'
      have hpow3 : (2 : ℝ) ^ (Real.log (T1 / η) / Real.log 2 + 3) = 8 * (T1 / η) := by
        rw [Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
        have htwo : (2 : ℝ) ^ (Real.log (T1 / η) / Real.log 2) = T1 / η := by
          rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ))]
          have hm : Real.log 2 * (Real.log (T1 / η) / Real.log 2) = Real.log (T1 / η) := by
            field_simp [Real.log_pos (by norm_num : 1 < (2 : ℝ)) |>.ne']
          rw [hm, Real.exp_log (div_pos hT1pos hη)]
        rw [htwo]
        norm_num
        ring
      calc
        2 ^ (k + 1) * η ≤ (2 : ℝ) ^ (Nat.ceil (Real.log (T1 / η) / Real.log 2) + 2) * η :=
          mul_le_mul_of_nonneg_right hpow1 hη.le
        _ ≤ (2 : ℝ) ^ (Real.log (T1 / η) / Real.log 2 + 3) * η :=
          mul_le_mul_of_nonneg_right hpow2 hη.le
        _ = 8 * (T1 / η) * η := by rw [hpow3]
        _ = 8 * T1 := by field_simp [hη.ne']
        _ ≤ 8 * T1 + 48 := by linarith
    have hring := ringMass_le_windowedCount (T0 := T0) (T1 := T1) Cw γ η k
      hwin' hCw hη (complementary.filter fun ρ => 2 ^ k * η ≤ |γ - ρ.im| ∧ |γ - ρ.im| < 2 ^ (k + 1) * η)
      hT0 (fun ρ hρ => hzero ρ (Finset.mem_filter.mp hρ).1)
      (fun ρ hρ => hhigh ρ (Finset.mem_filter.mp hρ).1)
      hγ (by dsimp [T1]; exact hγle) hk'
      (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
    simpa [L] using hring
  -- pointwise dyadic bound with the base-2 weight:
  -- 1/|γ-ρ.im| ≤ (1/η) 2^(-⌊log₂(|γ-ρ.im|/η)⌋)
  have hpoint {ρ : ℂ} (hρ : ρ ∈ complementary) :
      (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im| ≤
        (1 / η) * (analyticOrderNatAt riemannZeta ρ : ℝ) *
          (1 / 2 : ℝ) ^ Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2) := by
    let x : ℝ := |γ - ρ.im| / η
    have hx1 : 1 ≤ x := by
      dsimp [x]
      exact (one_le_div hη).mpr (havoid ρ hρ)
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
    have hpow : (2 : ℝ) ^ Nat.floor (Real.log x / Real.log 2) ≤ x := by
      have hfl : ((Nat.floor (Real.log x / Real.log 2) : ℕ) : ℝ) ≤ Real.log x / Real.log 2 := by
        exact Nat.floor_le (div_nonneg hlogx hlog2pos.le)
      have hmul : ((Nat.floor (Real.log x / Real.log 2) : ℕ) : ℝ) * Real.log 2 ≤ Real.log x := by
        exact (le_div_iff₀ hlog2pos).mp hfl
      have hexp : Real.exp (((Nat.floor (Real.log x / Real.log 2) : ℕ) : ℝ) * Real.log 2) ≤
          Real.exp (Real.log x) := Real.exp_le_exp.mpr hmul
      have hleft : Real.exp (((Nat.floor (Real.log x / Real.log 2) : ℕ) : ℝ) * Real.log 2) =
          (2 : ℝ) ^ Nat.floor (Real.log x / Real.log 2) := by
        rw [Real.exp_nat_mul]
        rw [Real.exp_log (by norm_num : 0 < (2 : ℝ))]
      simpa [hleft, Real.exp_log hxpos] using hexp
    have hgpos : 0 < |γ - ρ.im| := lt_of_lt_of_le hη (havoid ρ hρ)
    have hbound : 1 / |γ - ρ.im| ≤ (1 / η) * (1 / 2 : ℝ) ^ Nat.floor (Real.log x / Real.log 2) := by
      have hrewrite : 1 / |γ - ρ.im| = (1 / η) * (1 / x) := by
        dsimp [x]
        field_simp [hη.ne', hgpos.ne']
      rw [hrewrite]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h2kpos : 0 < (2 : ℝ) ^ Nat.floor (Real.log x / Real.log 2) := by positivity
      have hinv : (1 / x) ≤ 1 / (2 : ℝ) ^ Nat.floor (Real.log x / Real.log 2) := by
        exact one_div_le_one_div_of_le h2kpos hpow
      simpa [one_div, inv_pow] using hinv
    have hm : 0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := by
      exact_mod_cast Nat.zero_le _
    calc
      (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im| =
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / |γ - ρ.im|) := by ring
      _ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) *
          ((1 / η) * (1 / 2 : ℝ) ^ Nat.floor (Real.log x / Real.log 2)) := by
        exact mul_le_mul_of_nonneg_left hbound hm
      _ = (1 / η) * (analyticOrderNatAt riemannZeta ρ : ℝ) *
          (1 / 2 : ℝ) ^ Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2) := by
        dsimp [x]
        ring
  -- the class index of every high point lies below K
  have hfK (ρ : ℂ) (hρ : ρ ∈ complementary) :
      Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2) < K := by
    have hdist : |γ - ρ.im| ≤ T1 := by
      by_cases hγρ : γ ≤ ρ.im
      · have h1 : ρ.im - γ ≤ T1 - T0 := sub_le_sub (him_le ρ hρ) hγ
        have h2 : T1 - T0 ≤ T1 := by dsimp [T1]; linarith
        calc
          |γ - ρ.im| = |ρ.im - γ| := abs_sub_comm γ ρ.im
          _ = ρ.im - γ := abs_of_nonneg (sub_nonneg.mpr hγρ)
          _ ≤ T1 := h1.trans h2
      · have h1 : γ - ρ.im ≤ T1 - T0 / 2 := sub_le_sub hγle (le_of_lt (hhigh ρ hρ))
        have h2 : T1 - T0 / 2 ≤ T1 := by dsimp [T1]; linarith
        calc
          |γ - ρ.im| = γ - ρ.im := abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hγρ))
          _ ≤ T1 := h1.trans h2
    have hdiv : |γ - ρ.im| / η ≤ T1 / η := div_le_div_of_nonneg_right hdist hη.le
    have hpos1 : 0 < |γ - ρ.im| / η := div_pos (lt_of_lt_of_le hη (havoid ρ hρ)) hη
    have hlog : Real.log (|γ - ρ.im| / η) ≤ Real.log (T1 / η) :=
      Real.log_le_log hpos1 hdiv
    have hlog2 : Real.log (|γ - ρ.im| / η) / Real.log 2 ≤ Real.log (T1 / η) / Real.log 2 := by
      exact div_le_div_of_nonneg_right hlog (Real.log_nonneg (by norm_num : 1 ≤ (2 : ℝ)))
    have hfl : (Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2) : ℝ) ≤
        (Nat.ceil (Real.log (T1 / η) / Real.log 2) : ℝ) := by
      have h1 : (Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2) : ℝ) ≤
          Real.log (T1 / η) / Real.log 2 := by
        exact (Nat.floor_le (div_nonneg
          (Real.log_nonneg ((one_le_div hη).mpr (havoid ρ hρ)))
          (Real.log_nonneg (by norm_num : 1 ≤ (2 : ℝ))))).trans hlog2
      exact h1.trans (Nat.le_ceil _)
    have hlt : Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2) <
        Nat.ceil (Real.log (T1 / η) / Real.log 2) + 2 := by
      have hcast : (Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2) : ℝ) <
          ((Nat.ceil (Real.log (T1 / η) / Real.log 2) + 2 : ℕ) : ℝ) := by
        have hc : (Nat.ceil (Real.log (T1 / η) / Real.log 2) : ℝ) <
            ((Nat.ceil (Real.log (T1 / η) / Real.log 2) + 2 : ℕ) : ℝ) := by norm_num
        linarith [hfl, hc]
      exact_mod_cast hcast
    simpa [K] using hlt
  -- floor log2(x) = k  ↔  x ∈ dyadic ring k
  have hiff {k : ℕ} {ρ : ℂ} (hρ : ρ ∈ complementary) :
      (Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2) = k) ↔
        (2 ^ k * η ≤ |γ - ρ.im| ∧ |γ - ρ.im| < 2 ^ (k + 1) * η) := by
    let x : ℝ := |γ - ρ.im| / η
    have hx1 : 1 ≤ x := by dsimp [x]; exact (one_le_div hη).mpr (havoid ρ hρ)
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
    have hy : 0 ≤ Real.log x / Real.log 2 := div_nonneg hlogx hlog2pos.le
    have hpowk : ∀ k : ℕ, Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
      intro k
      rw [Real.exp_nat_mul]
      rw [Real.exp_log (by norm_num : 0 < (2 : ℝ))]
    constructor
    · intro hf
      have hle_lt := (Nat.floor_eq_iff hy).mp hf
      have hk1 : (k : ℝ) * Real.log 2 ≤ Real.log x := by
        exact (le_div_iff₀ hlog2pos).mp hle_lt.1
      have hk2 : Real.log x < ((k : ℝ) + 1) * Real.log 2 := by
        exact (div_lt_iff₀ hlog2pos).mp hle_lt.2
      have hxle2 : 2 ^ k ≤ x := by
        have hexp : Real.exp ((k : ℝ) * Real.log 2) ≤ Real.exp (Real.log x) :=
          Real.exp_le_exp.mpr hk1
        simpa [hpowk k, Real.exp_log hxpos] using hexp
      have hxlt2 : x < 2 ^ (k + 1) := by
        have hexp : Real.exp (Real.log x) < Real.exp (((k : ℝ) + 1) * Real.log 2) :=
          Real.exp_lt_exp.mpr hk2
        have hk1' : Real.exp (((k : ℝ) + 1) * Real.log 2) = (2 : ℝ) ^ (k + 1) := by
          simpa using hpowk (k + 1)
        simpa [Real.exp_log hxpos, hk1'] using hexp
      constructor
      · exact (le_div_iff₀ hη).mp (by simpa [x] using hxle2)
      · exact (div_lt_iff₀ hη).mp (by simpa [x] using hxlt2)
    · intro hring
      have hxle2 : 2 ^ k ≤ x := by
        exact (le_div_iff₀ hη).mpr (by simpa [x] using hring.1)
      have hxlt2 : x < 2 ^ (k + 1) := by
        exact (div_lt_iff₀ hη).mpr (by simpa [x] using hring.2)
      have hk1 : (k : ℝ) ≤ Real.log x / Real.log 2 := by
        have hexp : Real.exp ((k : ℝ) * Real.log 2) ≤ Real.exp (Real.log x) := by
          simpa [hpowk k, Real.exp_log hxpos] using hxle2
        exact (le_div_iff₀ hlog2pos).mpr (Real.exp_le_exp.mp hexp)
      have hk2 : Real.log x / Real.log 2 < (k : ℝ) + 1 := by
        have hexp : Real.exp (Real.log x) < Real.exp (((k : ℝ) + 1) * Real.log 2) := by
          have hk1' : Real.exp (((k : ℝ) + 1) * Real.log 2) = (2 : ℝ) ^ (k + 1) := by
            simpa using hpowk (k + 1)
          simpa [Real.exp_log hxpos, hk1'] using hxlt2
        exact (div_lt_iff₀ hlog2pos).mpr (Real.exp_lt_exp.mp hexp)
      exact (Nat.floor_eq_iff hy).mpr ⟨hk1, hk2⟩
  have hsum_rings :
      (complementary.sum fun ρ =>
        (analyticOrderNatAt riemannZeta ρ : ℝ) *
          (1 / 2 : ℝ) ^ Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2)) ≤
        Cw * (1 + Real.log 9) * (4 * η * L * (K : ℝ) + 6 * L) := by
    have hsum_eq := Finset.sum_fiberwise_of_maps_to
      (s := complementary) (t := Finset.range K)
      (g := fun ρ => Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2))
      (f := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) *
        (1 / 2 : ℝ) ^ Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2))
      (by intro ρ hρ; exact Finset.mem_range.mpr (hfK ρ hρ))
    rw [← hsum_eq]
    calc
      (∑ k ∈ Finset.range K,
          ∑ ρ ∈ complementary.filter (fun ρ => Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2) = k),
            (analyticOrderNatAt riemannZeta ρ : ℝ) *
              (1 / 2 : ℝ) ^ Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2)) ≤
          ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k *
            ((complementary.filter fun ρ => 2 ^ k * η ≤ |γ - ρ.im| ∧ |γ - ρ.im| < 2 ^ (k + 1) * η).sum
              fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hfilt : (complementary.filter fun ρ => Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2) = k) =
            complementary.filter fun ρ => 2 ^ k * η ≤ |γ - ρ.im| ∧ |γ - ρ.im| < 2 ^ (k + 1) * η := by
          apply Finset.ext
          intro ρ
          by_cases hρ : ρ ∈ complementary
          · simp [hρ, hiff hρ]
          · simp [hρ]
        have hk_eq : (∑ ρ ∈ complementary.filter (fun ρ => Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2) = k),
              (analyticOrderNatAt riemannZeta ρ : ℝ) *
                (1 / 2 : ℝ) ^ Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2)) =
            ∑ ρ ∈ complementary.filter (fun ρ => 2 ^ k * η ≤ |γ - ρ.im| ∧ |γ - ρ.im| < 2 ^ (k + 1) * η),
              (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / 2 : ℝ) ^ k := by
          rw [hfilt]
          apply Finset.sum_congr rfl
          intro ρ hρ
          congr 1
          have hmem : 2 ^ k * η ≤ |γ - ρ.im| ∧ |γ - ρ.im| < 2 ^ (k + 1) * η :=
            (Finset.mem_filter.mp hρ).2
          exact congrArg (fun m : ℕ => (1 / 2 : ℝ) ^ m) ((hiff (Finset.mem_filter.mp hρ).1).mpr hmem)
        have hk_eq2 : (∑ ρ ∈ complementary.filter (fun ρ => 2 ^ k * η ≤ |γ - ρ.im| ∧ |γ - ρ.im| < 2 ^ (k + 1) * η),
              (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / 2 : ℝ) ^ k) =
            (1 / 2 : ℝ) ^ k * ((complementary.filter fun ρ => 2 ^ k * η ≤ |γ - ρ.im| ∧ |γ - ρ.im| < 2 ^ (k + 1) * η).sum
              fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ρ hρ
          ring
        exact le_of_eq (hk_eq.trans hk_eq2)
      _ ≤ ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k *
          (Cw * (1 + Real.log 9) * (4 * 2 ^ k * η * L + 3 * L)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left (hringMass (Finset.mem_range.mp hk))
          (by positivity : 0 ≤ (1 / 2 : ℝ) ^ k)
      _ = ∑ k ∈ Finset.range K, Cw * (1 + Real.log 9) * (4 * η * L + 3 * L * (1 / 2 : ℝ) ^ k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hp : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by
          rw [← mul_pow]
          field_simp [show (2 : ℝ) ≠ 0 by norm_num]
          simp
        calc
          (1 / 2 : ℝ) ^ k * (Cw * (1 + Real.log 9) * (4 * 2 ^ k * η * L + 3 * L))
              = ((1 / 2 : ℝ) ^ k * 2 ^ k) * (Cw * (1 + Real.log 9) * (4 * η * L))
                  + (1 / 2 : ℝ) ^ k * (Cw * (1 + Real.log 9) * (3 * L)) := by ring
          _ = Cw * (1 + Real.log 9) * (4 * η * L)
              + Cw * (1 + Real.log 9) * (3 * L) * (1 / 2 : ℝ) ^ k := by rw [hp]; ring
          _ = Cw * (1 + Real.log 9) * (4 * η * L + 3 * L * (1 / 2 : ℝ) ^ k) := by ring
      _ = Cw * (1 + Real.log 9) * (4 * η * L * (K : ℝ) + 3 * L * (∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k)) := by
        rw [Finset.mul_sum]
        have hsum1 : (∑ k ∈ Finset.range K, Cw * (1 + Real.log 9) * (4 * η * L + 3 * L * (1 / 2 : ℝ) ^ k)) =
            (∑ k ∈ Finset.range K, Cw * (1 + Real.log 9) * (4 * η * L))
              + (∑ k ∈ Finset.range K, Cw * (1 + Real.log 9) * (3 * L * (1 / 2 : ℝ) ^ k)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        rw [hsum1]
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      _ ≤ Cw * (1 + Real.log 9) * (4 * η * L * (K : ℝ) + 6 * L) := by
        have hgeom : (∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k) ≤ 2 := by
          have hg := sum_le_hasSum (Finset.range K) (fun k hk => by positivity) summable_geometric_two.hasSum
          rwa [tsum_geometric_two] at hg
        have h3 : 3 * L * (∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k) ≤ 6 * L := by
          have hm : 3 * L * (∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k) ≤ 3 * L * 2 := by
            exact mul_le_mul_of_nonneg_left hgeom (by positivity : 0 ≤ 3 * L)
          linarith
        have hinner : 0 ≤ 4 * η * L * (K : ℝ) + 3 * L * (∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k) := by
          positivity
        have htarget : 0 ≤ 4 * η * L * (K : ℝ) + 6 * L := by positivity
        have hcoef : 0 ≤ Cw * (1 + Real.log 9) := by
          exact mul_nonneg hCw (by linarith [Real.log_nonneg (by norm_num : 1 ≤ (9 : ℝ))])
        exact mul_le_mul_of_nonneg_left (by linarith [h3, hinner, htarget]) hcoef
  refine ⟨Cw * (1 + Real.log 9) * (4 * (K : ℝ) + 6 / η), ?_, ?_⟩
  · have hlog9 : 0 ≤ 1 + Real.log 9 := by
      linarith [Real.log_nonneg (by norm_num : 1 ≤ (9 : ℝ))]
    positivity
  · calc
      (complementary.sum fun ρ =>
          (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤
          (1 / η) * (complementary.sum fun ρ =>
            (analyticOrderNatAt riemannZeta ρ : ℝ) *
              (1 / 2 : ℝ) ^ Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2)) := by
        have h1 := Finset.sum_le_sum (fun ρ hρ => hpoint hρ)
        calc
          (complementary.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|)
              ≤ complementary.sum (fun ρ => (1 / η) * (analyticOrderNatAt riemannZeta ρ : ℝ) *
                (1 / 2 : ℝ) ^ Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2)) := h1
          _ = (1 / η) * (complementary.sum fun ρ =>
              (analyticOrderNatAt riemannZeta ρ : ℝ) *
                (1 / 2 : ℝ) ^ Nat.floor (Real.log (|γ - ρ.im| / η) / Real.log 2)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ρ hρ
            ring
      _ ≤ (1 / η) * (Cw * (1 + Real.log 9) * (4 * η * L * (K : ℝ) + 6 * L)) := by
        exact mul_le_mul_of_nonneg_left hsum_rings (by positivity : 0 ≤ 1 / η)
      _ = Cw * (1 + Real.log 9) * (4 * L * (K : ℝ) + 6 * L / η) := by
        field_simp [hη.ne']
      _ ≤ (Cw * (1 + Real.log 9) * (4 * (K : ℝ) + 6 / η)) * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / H := by
        have hT1H : 1 ≤ T1 / H := (one_le_div (by linarith : 0 < H)).mpr (by dsimp [T1]; linarith)
        have hLsq : L ≤ L ^ 2 := by nlinarith [hL1, hLpos]
        have hLfactor : L ≤ L ^ 2 * (T1 / H) := by
          have h2 : L ^ 2 ≤ L ^ 2 * (T1 / H) := by
            exact le_mul_of_one_le_right (by positivity : 0 ≤ L ^ 2) hT1H
          linarith [hLsq, h2]
        have h1 : 4 * L * (K : ℝ) ≤ (4 * (K : ℝ)) * (L ^ 2 * (T1 / H)) := by
          have h1' : (4 * (K : ℝ)) * L ≤ (4 * (K : ℝ)) * (L ^ 2 * (T1 / H)) :=
            mul_le_mul_of_nonneg_left hLfactor (by positivity : 0 ≤ 4 * (K : ℝ))
          simpa [mul_comm, mul_left_comm, mul_assoc] using h1'
        have h2 : 6 * L / η ≤ (6 / η) * (L ^ 2 * (T1 / H)) := by
          have hle : L / η ≤ (L ^ 2 * (T1 / H)) / η := by
            exact div_le_div_of_nonneg_right hLfactor hη.le
          have h2' : 6 * L / η = 6 * (L / η) := by ring
          have h2'' : 6 * (L / η) ≤ 6 * ((L ^ 2 * (T1 / H)) / η) := by
            exact mul_le_mul_of_nonneg_left hle (by norm_num)
          have h2''' : 6 * ((L ^ 2 * (T1 / H)) / η) = (6 / η) * (L ^ 2 * (T1 / H)) := by ring
          linarith [h2', h2'', h2''']
        have hsum : 4 * L * (K : ℝ) + 6 * L / η ≤
            ((4 * (K : ℝ)) + 6 / η) * (L ^ 2 * (T1 / H)) := by
          have h1' : (4 * (K : ℝ)) * (L ^ 2 * (T1 / H)) ≤
              ((4 * (K : ℝ)) + 6 / η) * (L ^ 2 * (T1 / H)) := by
            exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity : 0 ≤ 6 / η))
              (mul_nonneg (by positivity : 0 ≤ L ^ 2) (by linarith : 0 ≤ T1 / H))
          linarith [h1, h1', h2]
        have hmult : Cw * (1 + Real.log 9) * (4 * L * (K : ℝ) + 6 * L / η) ≤
            Cw * (1 + Real.log 9) * (((4 * (K : ℝ)) + 6 / η) * (L ^ 2 * (T1 / H))) := by
          exact mul_le_mul_of_nonneg_left hsum (mul_nonneg hCw (by
            linarith [Real.log_nonneg (by norm_num : 1 ≤ (9 : ℝ))]))
        have hfin : Cw * (1 + Real.log 9) * (((4 * (K : ℝ)) + 6 / η) * (L ^ 2 * (T1 / H))) =
            (Cw * (1 + Real.log 9) * (4 * (K : ℝ) + 6 / η)) * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / H := by
          dsimp [L, T1]
          ring
        simpa [hfin] using hmult

/-- L1 MAIN: a good detection point exists in `[T0, T0 + H]` with the
frequency-weighted mass bounded by `C (1 + log(T0+H+6))^2 (T0+H) / (T0 H)`.

This replaces the former axiom. -/
theorem exists_good_detection_point
    (T0 H : ℝ) (complementary : Finset ℂ)
    (hT0 : 16 ≤ T0) (hH1 : 1 ≤ H) (hHleT0 : H ≤ T0)
    (hzero : ∀ ρ ∈ complementary, RiemannHypothesis.IsNontrivialZero ρ)
    (him_pos : ∀ ρ ∈ complementary, 0 < ρ.im)
    (him_le : ∀ ρ ∈ complementary, ρ.im ≤ T0 + H) :
    ∃ C γ : ℝ, 0 ≤ C ∧ T0 ≤ γ ∧ γ ≤ T0 + H ∧
      frequencyWeightedMass complementary γ ≤
        C * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / (T0 * H) := by
  classical
  rcases exists_card_nontrivialZerosFinset_le_mul_log with ⟨C0, hC0, hcard⟩
  let N0 : ℝ := (C0 + 1) * (T0 + H) * (1 + Real.log (T0 + H + 6))
  have hN0 : (complementary.card : ℝ) ≤ N0 := by
    have hsub : complementary ⊆ nontrivialZerosFinset (T0 + H) := by
      intro ρ hρ
      exact mem_nontrivialZerosFinset.mpr ⟨hzero ρ hρ, by
        rw [abs_of_pos (him_pos ρ hρ)]
        exact him_le ρ hρ⟩
    have hT : 4 ≤ T0 + H := by linarith
    have hcard' := hcard (T0 + H) hT
    calc
      (complementary.card : ℝ) ≤ (nontrivialZerosFinset (T0 + H)).card := by
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ C0 * (T0 + H) * (1 + Real.log (T0 + H + 6)) := hcard'
      _ ≤ (C0 + 1) * (T0 + H) * (1 + Real.log (T0 + H + 6)) := by
        have hT0H : 0 ≤ T0 + H := by linarith
        have hlog : 0 ≤ 1 + Real.log (T0 + H + 6) := by
          linarith [Real.log_nonneg (by linarith : 1 ≤ T0 + H + 6)]
        nlinarith [hC0, hT0H, hlog]
      _ = N0 := by dsimp [N0]
  have hN0pos : 0 < N0 := by
    dsimp [N0]
    have hlog : 0 ≤ Real.log (T0 + H + 6) := Real.log_nonneg (by linarith)
    positivity
  let η : ℝ := H / (4 * N0)
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (by linarith) (mul_pos (by norm_num) hN0pos)
  have hN01 : 1 ≤ N0 := by
    dsimp [N0]
    have hlog : 0 ≤ Real.log (T0 + H + 6) := Real.log_nonneg (by linarith)
    have h1 : 1 ≤ C0 + 1 := by linarith
    have h2 : 1 ≤ T0 + H := by linarith
    have h3 : 1 ≤ 1 + Real.log (T0 + H + 6) := by linarith
    have hab : 1 ≤ (C0 + 1) * (T0 + H) := by
      have hm : (1 : ℝ) * 1 ≤ (C0 + 1) * (T0 + H) :=
        mul_le_mul h1 h2 (by norm_num : 0 ≤ (1 : ℝ)) (by linarith : 0 ≤ C0 + 1)
      simpa using hm
    have hfin : (1 : ℝ) * 1 ≤ (C0 + 1) * (T0 + H) * (1 + Real.log (T0 + H + 6)) :=
      mul_le_mul hab h3 (by norm_num : 0 ≤ (1 : ℝ))
        (by linarith [h1, h2] : 0 ≤ (C0 + 1) * (T0 + H))
    simpa using hfin
  have hT1N0 : T0 + H ≤ N0 := by
    dsimp [N0]
    have h1 : 1 ≤ C0 + 1 := by linarith
    have h2 : 1 ≤ T0 + H := by linarith
    have h3 : 1 ≤ 1 + Real.log (T0 + H + 6) := by
      linarith [Real.log_nonneg (by linarith : 1 ≤ T0 + H + 6)]
    have hm : (1 : ℝ) * (T0 + H) ≤ (C0 + 1) * (T0 + H) := by
      exact mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ T0 + H)
    have hm' : (C0 + 1) * (T0 + H) * 1 ≤ (C0 + 1) * (T0 + H) * (1 + Real.log (T0 + H + 6)) := by
      exact mul_le_mul_of_nonneg_left h3 (by linarith [h1, h2] : 0 ≤ (C0 + 1) * (T0 + H))
    nlinarith [hm, hm']
  have hηle : η ≤ T0 + H := by
    dsimp [η]
    calc
      η = H / (4 * N0) := rfl
      _ ≤ H / (4 * (T0 + H)) := by
        exact div_le_div_of_nonneg_left (by linarith : 0 ≤ H) (by positivity : 0 < 4 * (T0 + H))
          (by nlinarith [hT1N0] : (4 : ℝ) * (T0 + H) ≤ 4 * N0)
      _ ≤ 1 / 4 := by
        exact (div_le_iff₀ (by positivity : 0 < 4 * (T0 + H))).mpr
          (by nlinarith : H ≤ (1 / 4 : ℝ) * (4 * (T0 + H)))
      _ ≤ T0 + H := by linarith
  have hsum_radii :
      (complementary.sum fun ρ => 2 * η) ≤ H / 2 := by
    calc
      (complementary.sum fun ρ => 2 * η) = 2 * η * complementary.card := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
      _ ≤ 2 * η * N0 := mul_le_mul_of_nonneg_left hN0 (mul_nonneg (by norm_num) hη.le)
      _ = H / 2 := by
        dsimp [η]
        field_simp [hN0pos.ne', (by linarith : (4 : ℝ) ≠ 0)]
        ring
  have havoid :=
    exists_point_avoiding_small_intervals
      (T0 := T0) (H := H) (I := complementary)
      (c := fun ρ => ρ.im) (r := fun _ => η)
      (by linarith) (fun _ => le_of_lt hη) hsum_radii
  have havoid_main := havoid
  rcases havoid_main with ⟨γ, hγT0, hγT1, hγavoid⟩
  have hwin :
      ∃ C, 0 ≤ C ∧ ∀ a b : ℝ, T0 / 2 ≤ a → a ≤ b →
        (riemannZeroCount b : ℝ) - riemannZeroCount a ≤
          C * ((b - a) * (1 + Real.log (b + 6)) + (1 + Real.log (b + 6))) := by
    rcases exists_windowedZeroMultiplicity_le_uniform with ⟨Cw, hCw, hwu⟩
    refine ⟨Cw, hCw, ?_⟩
    intro a b ha hab
    exact hwu a b (by linarith) hab
  -- high/low split
  let high : Finset ℂ := complementary.filter fun ρ => T0 / 2 < ρ.im
  let low : Finset ℂ := complementary.filter fun ρ => ρ.im ≤ T0 / 2
  have hsplit : frequencyWeightedMass complementary γ =
      frequencyWeightedMass high γ + frequencyWeightedMass low γ := by
    simpa [frequencyWeightedMass, high, low, not_lt] using
      (Finset.sum_filter_add_sum_filter_not complementary (fun ρ => T0 / 2 < ρ.im)
        (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / (‖ρ‖ * |γ - ρ.im|))).symm
  have hdyadic :
      ∃ C, 0 ≤ C ∧ (high.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤
        C * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / H := by
    refine dyadic_distance_sum_le T0 H high γ η hT0 hH1 hHleT0 hη hηle ?_ ?_ ?_ ?_ hγT0 hγT1 ?_
    · intro ρ hρ
      exact hγavoid ρ (Finset.mem_filter.mp hρ).1
    · intro ρ hρ
      exact hzero ρ (Finset.mem_filter.mp hρ).1
    · intro ρ hρ
      exact (Finset.mem_filter.mp hρ).2
    · intro ρ hρ
      exact him_le ρ (Finset.mem_filter.mp hρ).1
    · exact hwin
  rcases hdyadic with ⟨Cdy, hCdy, hdy⟩
  have hhigh_bound :
      frequencyWeightedMass high γ ≤
        (2 * Cdy / T0) * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / H := by
    calc
      frequencyWeightedMass high γ
          = ∑ ρ ∈ high, (analyticOrderNatAt riemannZeta ρ : ℝ) / (‖ρ‖ * |γ - ρ.im|) := rfl
      _ ≤ ∑ ρ ∈ high, ((2 / T0) * (analyticOrderNatAt riemannZeta ρ : ℝ)) / |γ - ρ.im| := by
        apply Finset.sum_le_sum
        intro ρ hρ
        have hnorm : T0 / 2 ≤ ‖ρ‖ := by
          have him : T0 / 2 < ρ.im := (Finset.mem_filter.mp hρ).2
          have him' : |ρ.im| = ρ.im := abs_of_pos (lt_of_lt_of_le (by linarith : 0 < T0 / 2) him.le)
          calc
            T0 / 2 ≤ |ρ.im| := by rw [him']; exact le_of_lt him
            _ ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
        have hd : 0 < |γ - ρ.im| := lt_of_lt_of_le hη (hγavoid ρ (Finset.mem_filter.mp hρ).1)
        have hprod : (T0 / 2) * |γ - ρ.im| ≤ ‖ρ‖ * |γ - ρ.im| := by
          exact mul_le_mul_of_nonneg_right hnorm (abs_nonneg _)
        have h1 : 1 / (‖ρ‖ * |γ - ρ.im|) ≤ 1 / ((T0 / 2) * |γ - ρ.im|) := by
          exact one_div_le_one_div_of_le (by
            exact mul_pos (by linarith : 0 < T0 / 2) hd) hprod
        have h2 : 1 / ((T0 / 2) * |γ - ρ.im|) = (2 / T0) / |γ - ρ.im| := by
          field_simp [show (T0 / 2) ≠ 0 by linarith, hd.ne']
        calc
          (analyticOrderNatAt riemannZeta ρ : ℝ) / (‖ρ‖ * |γ - ρ.im|)
              = (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / (‖ρ‖ * |γ - ρ.im|)) := by ring
          _ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / ((T0 / 2) * |γ - ρ.im|)) := by
            exact mul_le_mul_of_nonneg_left h1 (by exact_mod_cast Nat.zero_le _)
          _ = ((2 / T0) * (analyticOrderNatAt riemannZeta ρ : ℝ)) / |γ - ρ.im| := by
            rw [h2]
            ring
      _ = (2 / T0) * (high.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ hρ
        ring
      _ ≤ (2 / T0) * (Cdy * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / H) := by
        exact mul_le_mul_of_nonneg_left hdy (div_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (by linarith : 0 ≤ T0))
      _ = (2 * Cdy / T0) * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / H := by ring
  rcases exists_globalReciprocalZeroMultiplicity_le_log_sq with ⟨Crec, hCrec, hrec⟩
  have hlow_bound :
      frequencyWeightedMass low γ ≤
        (2 * Crec / T0) * (1 + Real.log (T0 + H + 6)) ^ 2 := by
    have hlowdist : ∀ ρ ∈ low, T0 / 2 ≤ |γ - ρ.im| := by
      intro ρ hρ
      have him : ρ.im ≤ T0 / 2 := (Finset.mem_filter.mp hρ).2
      have hpos : 0 ≤ γ - ρ.im := by
        exact sub_nonneg.mpr (le_trans him (by linarith : T0 / 2 ≤ γ))
      have hmain : T0 - T0 / 2 ≤ γ - ρ.im := sub_le_sub hγT0 him
      rw [abs_of_nonneg hpos]
      nlinarith [hmain]
    have hsub' : low ⊆ nontrivialZerosFinset (T0 + H) := by
      intro ρ hρ
      exact mem_nontrivialZerosFinset.mpr ⟨hzero ρ (Finset.mem_filter.mp hρ).1, by
        rw [abs_of_pos (him_pos ρ (Finset.mem_filter.mp hρ).1)]
        exact him_le ρ (Finset.mem_filter.mp hρ).1⟩
    have hsum' : (low.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) ≤
        globalReciprocalZeroMultiplicity (T0 + H) := by
      simpa [globalReciprocalZeroMultiplicity] using
        (Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => hsub' hρ)
          (fun ρ hρ _ => div_nonneg (by exact_mod_cast Nat.zero_le _) (norm_nonneg ρ)))
    calc
      frequencyWeightedMass low γ
          = ∑ ρ ∈ low, (analyticOrderNatAt riemannZeta ρ : ℝ) / (‖ρ‖ * |γ - ρ.im|) := rfl
      _ ≤ ∑ ρ ∈ low, (analyticOrderNatAt riemannZeta ρ : ℝ) * (2 / T0) / ‖ρ‖ := by
        apply Finset.sum_le_sum
        intro ρ hρ
        have hd : 0 < |γ - ρ.im| := lt_of_lt_of_le hη (hγavoid ρ (Finset.mem_filter.mp hρ).1)
        have h1 : 1 / |γ - ρ.im| ≤ 2 / T0 := by
          have h1' : 1 / |γ - ρ.im| ≤ 1 / (T0 / 2) :=
            one_div_le_one_div_of_le (by linarith : 0 < T0 / 2) (hlowdist ρ hρ)
          have h2' : 1 / (T0 / 2) = 2 / T0 := by
            field_simp [show (T0 / 2) ≠ 0 by linarith]
          simpa [h2'] using h1'
        have hnormpos : 0 < ‖ρ‖ := by
          have himpos : 0 < ρ.im := him_pos ρ (Finset.mem_filter.mp hρ).1
          have h1' : 0 < |ρ.im| := by rwa [abs_of_pos himpos]
          exact lt_of_lt_of_le h1' (Complex.abs_im_le_norm ρ)
        calc
          (analyticOrderNatAt riemannZeta ρ : ℝ) / (‖ρ‖ * |γ - ρ.im|)
              = (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / |γ - ρ.im|) / ‖ρ‖ := by
            field_simp [hnormpos.ne', hd.ne']
          _ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * (2 / T0) / ‖ρ‖ := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left h1 (by exact_mod_cast Nat.zero_le _)) (norm_nonneg ρ)
      _ = (2 / T0) * (low.sum fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ hρ
        ring
      _ ≤ (2 / T0) * globalReciprocalZeroMultiplicity (T0 + H) := by
        exact mul_le_mul_of_nonneg_left hsum' (div_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (by linarith : 0 ≤ T0))
      _ ≤ (2 / T0) * (Crec * (1 + Real.log (T0 + H + 6)) ^ 2) := by
        exact mul_le_mul_of_nonneg_left (hrec (T0 + H) (by linarith))
          (div_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (by linarith : 0 ≤ T0))
      _ = (2 * Crec / T0) * (1 + Real.log (T0 + H + 6)) ^ 2 := by ring
  refine ⟨2 * Cdy + 2 * Crec, γ, by positivity, hγT0, hγT1, ?_⟩
  have hLsq : 0 ≤ (1 + Real.log (T0 + H + 6)) ^ 2 := by positivity
  have hCrec' : 0 ≤ 2 * Crec := by positivity
  have hHleT1 : H ≤ T0 + H := by linarith
  have h2 : (2 * Crec / T0) * (1 + Real.log (T0 + H + 6)) ^ 2 ≤
          (2 * Crec) * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / (T0 * H) := by
        have h2' : (2 * Crec / T0) * (1 + Real.log (T0 + H + 6)) ^ 2 =
            ((2 * Crec) * (1 + Real.log (T0 + H + 6)) ^ 2) / T0 := by ring
        have h2'' : (2 * Crec) * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / (T0 * H) =
            (((2 * Crec) * (1 + Real.log (T0 + H + 6)) ^ 2) / T0) * (T0 + H) / H := by ring
        rw [h2', h2'']
        have hT1H : 1 ≤ (T0 + H) / H := (one_le_div (by linarith : 0 < H)).mpr hHleT1
        have hnonneg : 0 ≤ ((2 * Crec) * (1 + Real.log (T0 + H + 6)) ^ 2) / T0 := by positivity
        have hmain : ((2 * Crec) * (1 + Real.log (T0 + H + 6)) ^ 2) / T0 ≤
            (((2 * Crec) * (1 + Real.log (T0 + H + 6)) ^ 2) / T0) * ((T0 + H) / H) := by
          exact le_mul_of_one_le_right hnonneg hT1H
        simpa [div_eq_mul_inv, mul_assoc] using hmain
  have h1 : (2 * Cdy / T0) * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / H ≤
          (2 * Cdy) * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / (T0 * H) := by
        have h1' : (2 * Cdy / T0) * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / H =
            (2 * Cdy) * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / (T0 * H) := by
          field_simp [show (T0 : ℝ) ≠ 0 by linarith, show H ≠ 0 by linarith]
        exact le_of_eq h1'
  calc
    frequencyWeightedMass complementary γ
        = frequencyWeightedMass high γ + frequencyWeightedMass low γ := hsplit
    _ ≤ (2 * Cdy / T0) * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / H
          + (2 * Crec / T0) * (1 + Real.log (T0 + H + 6)) ^ 2 := by
      linarith [hhigh_bound, hlow_bound]
    _ ≤ (2 * Cdy) * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / (T0 * H)
          + (2 * Crec) * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / (T0 * H) := by
      linarith [h1, h2]
    _ = (2 * Cdy + 2 * Crec) * (1 + Real.log (T0 + H + 6)) ^ 2 * (T0 + H) / (T0 * H) := by ring

end

end HalfIsolatedZeroDichotomy
end PrimeNumberTheorem
