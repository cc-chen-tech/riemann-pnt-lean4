/-
# DRAFT (uncompiled): L1 main assembly, complete proof

Paper: `docs/research/detection-point-choice-proof-draft.md`
(revision 2, Steps 0-2).  Uncompiled; tactic details may need adjustment.

Assumes the two structural drafts are proved:
- Appendix A: `exists_point_avoiding_small_intervals`
- Appendix B: `exists_windowedRiemannZeroCount_le`

-/
import PrimeNumberTheorem.HalfIsolatedZeroDichotomy.DetectionPointChoice
import PrimeNumberTheorem.GlobalZeroCount
import PrimeNumberTheorem.RiemannVonMangoldt.AllHeightAsymptotic

namespace PrimeNumberTheorem
namespace HalfIsolatedZeroDichotomy
namespace DetectionPointChoiceMain

open scoped BigOperators

/-- Dyadic distance-sum bound.  For `γ` at distance at least `η` from every
center, the reciprocal-distance sum is `O((1 + log T1)^2 * T1 / H)` once
`η = H / (4 N0)` with `N0` the global count majorant.  The windowed count
input `hwin` is Appendix B. -/
lemma dyadic_distance_sum_le
    (T0 H : ℝ) (complementary : Finset ℂ) (γ : ℝ) (η : ℝ)
    (hT0 : 16 ≤ T0) (hH1 : 1 ≤ H) (hHle : H ≤ T0)
    (hη : 0 < η) (havoid : ∀ ρ ∈ complementary, η ≤ |γ - ρ.im|)
    (hhigh : ∀ ρ ∈ complementary, T0 / 2 ≤ ρ.im)
    (hwin :
      ∃ C, 0 ≤ C ∧ ∀ a b : ℝ, T0 / 2 ≤ a → a ≤ b →
        (riemannZeroCount b : ℝ) - riemannZeroCount a ≤
          C * ((b - a) * (1 + Real.log (b + 6)) + (1 + Real.log (b + 6)))) :
    ∃ C, 0 ≤ C ∧
      (complementary.sum fun ρ =>
        (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤
        C * (1 + Real.log (T0 + H)) ^ 2 * (T0 + H) / H := by
  rcases hwin with ⟨Cw, hCw, hwin'⟩
  let T1 : ℝ := T0 + H
  let K : ℕ := Nat.ceil (Real.log (T1 / η)) + 2
  have hKpos : 0 < K := by dsimp [K]; omega
  -- ring decomposition: distances in [2^k η, 2^(k+1) η), k < K, plus the tail
  have hdist_bound : (complementary.sum fun ρ =>
      (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤
      (1 / η) * (complementary.sum fun ρ =>
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / 2 ^ Nat.floor (Real.log (|γ - ρ.im| / η)))) := by
    sorry
    -- pointwise: 1/|γ-ρ.im| ≤ (1/η) · 2^(-⌊log(|γ-ρ.im|/η)⌋) since
    -- 2^⌊log x⌋ ≤ x; sum monotonicity
  have hring_count {k : ℕ} :
      (complementary.filter fun ρ => 2 ^ k * η ≤ |γ - ρ.im| ∧ |γ - ρ.im| < 2 ^ (k + 1) * η)
        .sum (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        Cw * (4 * 2 ^ k * η * (1 + Real.log (T1 + 6)) + (1 + Real.log (T1 + 6))) := by
    -- all zeros in the ring have |Im ρ| within 2^(k+1)η of γ, and γ ∈ [T0,T1];
    -- the ring is contained in a height window of width 4·2^k η,
    -- counted by hwin' with a = max(T0/2, γ - 2^(k+1)η) ... the window
    -- [γ - 2^(k+1)η, γ + 2^(k+1)η] has width 2^(k+2)η; positivity handled by
    -- summing multiplicities of zeros inside it (positive side count).
    sorry
    -- details: zeros have Im > 0 (hypothesis of the main theorem), and the
    -- window is above T0/2 because γ ≥ T0 and η ≤ T0; use hwin'.
  have hsum_rings :
      (complementary.sum fun ρ =>
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / 2 ^ Nat.floor (Real.log (|γ - ρ.im| / η)))) ≤
        Cw * (16 * (1 + Real.log (T1 + 6)) * K + (1 + Real.log (T1 + 6)) * (2 / η) * K) := by
    sorry
    -- split by floor value k; each class contributes ring mass / 2^k,
    -- ring mass ≤ Cw(4·2^k η log + log) ⟹ ≤ Cw(4η log + log/2^k);
    -- sum over k < K: ≤ Cw(4Kη log + 2 log/η·... ) — keep the draft-level
    -- constant shape; final cleaning absorbs everything into C (1+logT1)^2 T1/H.
  refine ⟨?_, by positivity, ?_⟩
  · -- explicit constant: Cw * 64 * (1 + ...) composition; placeholder shape
    sorry
  · sorry -- final assembly with η = H/(4 N0), N0 = C0 T1 (1 + log T1)

/- PRE-REVIEW RISK LIST (2026-08-16, to fix at first compile):

1. SIGNATURE GAP (real): the main theorem assumes `0 < T0`, but the
   Appendix B input `exists_windowedRiemannZeroCount_le` needs `8 ≤ T0`.
   FIX: strengthen the main theorem hypothesis to `8 ≤ T0` (harmless in
   the detector regime where T0 is enormous).  The dyadic-shell windows
   then always satisfy `8 ≤ a` once `a = max (T0/2) (γ - 2^(k+1) η)` is
   chosen with the ring contained in `[T0/2, T1]` (γ ≥ T0 ≥ 8 and η ≤ T0).
2. `hwin` (Step 2): applying Appendix B at `(a, b-a)` requires `0 ≤ b-a`
   and `8 ≤ a`; the `a = T0/2` case needs `16 ≤ T0`, so the dyadic
   shells starting below `T0/2` must instead be folded into the global
   reciprocal-mass low part (Step 4's low split already reserves
   `Im ρ < T0/2` — keep the shells only on `[T0/2, T1]`).
3. `dyadic_distance_sum_le` ring decomposition: the floor/`2^k` chain
   `2^⌊log(x/η)⌋ ≤ x/η` uses `Nat.floor` lemmas; expect `nlinarith` +
   `Real.log` monotonicity churn.  The ring count `hring_count` applies
   `hwin'` with a window of width `2^(k+2) η`; the `+ log` term in the
   windowed bound is what forces the `K ≤ log(T1/η)` cap and the
   `(1/η)` tail — keep the draft's constant shape `C (1+log T1)^2 T1/H`.
4. `hN0` needs the membership bridge `complementary ⊆ nontrivialZerosFinset
   (T0+H)` from `him_pos`/`him_le` (zeros counted by
   `exists_card_nontrivialZerosFinset_le_mul_log` have `|Im| ≤ T`, positive
   imaginary part included).
5. The `8 ≤ T0` strengthening also simplifies `hHleT0 : H ≤ T0`
   (kept as is; `1 ≤ H` unchanged).
-/

/-- MAIN TARGET (matches the axiom; promotion plan: prove this and delete
the axiom).  Strengthened hypothesis `8 ≤ T0` per risk list item 1. -/
theorem exists_good_detection_point
    (T0 H : ℝ) (complementary : Finset ℂ)
    (hT0 : 16 ≤ T0) (hH1 : 1 ≤ H) (hHleT0 : H ≤ T0)
    (him_pos : ∀ ρ ∈ complementary, 0 < ρ.im)
    (him_le : ∀ ρ ∈ complementary, ρ.im ≤ T0 + H) :
    ∃ C γ : ℝ, 0 ≤ C ∧ T0 ≤ γ ∧ γ ≤ T0 + H ∧
      frequencyWeightedMass complementary γ ≤
        C * (1 + Real.log (T0 + H)) ^ 2 * (T0 + H) / (T0 * H) := by
  classical
  -- Step 0: avoidance radius
  rcases exists_card_nontrivialZerosFinset_le_mul_log with ⟨C0, hC0, hcard⟩
  let N0 : ℝ := C0 * (T0 + H) * (1 + Real.log (T0 + H + 6))
  have hN0 : (complementary.card : ℝ) ≤ N0 := by
    -- complementary is a subfamily of the global nontrivial zeros finset
    -- at height T0+H (needs him_le and the membership bridge)
    sorry
  have hN0pos : 0 < N0 := by dsimp [N0]; positivity
  let η : ℝ := H / (4 * N0)
  have hη : 0 < η := by dsimp [η]; positivity
  have hsum_radii :
      (complementary.sum fun ρ => 2 * η) ≤ H / 2 := by
    calc
      (complementary.sum fun ρ => 2 * η) = 2 * η * complementary.card := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
      _ ≤ 2 * η * N0 := mul_le_mul_of_nonneg_left hN0 (by positivity)
      _ = H / 2 := by
        dsimp [η]
        field_simp [hN0pos.ne']
        ring
  -- Step 1: avoidance point (Appendix A)
  have havoid :=
    exists_point_avoiding_small_intervals
      (T0 := T0) (H := H) (I := complementary)
      (c := fun ρ => ρ.im) (r := fun _ => η)
      (by linarith) (fun _ => le_of_lt hη) hsum_radii
  rcases havoid with ⟨γ, hγT0, hγT1, hγavoid⟩
  -- Step 2: windowed count input (Appendix B)
  have hwin :
      ∃ C, 0 ≤ C ∧ ∀ a b : ℝ, T0 / 2 ≤ a → a ≤ b →
        (riemannZeroCount b : ℝ) - riemannZeroCount a ≤
          C * ((b - a) * (1 + Real.log (b + 6)) + (1 + Real.log (b + 6))) := by
    -- from exists_windowedRiemannZeroCount_le: apply at (a, b-a) with 8 ≤ a
    sorry
  -- Step 3: dyadic bound
  rcases dyadic_distance_sum_le T0 H complementary γ η
      (by linarith) hH1 hHleT0 hη hγavoid hwin with ⟨C1, hC1, hdyadic⟩
  -- Step 4: divide by height
  have hhigh : (complementary.sum fun ρ =>
      (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) ≤
      (2 / T0) * (complementary.sum fun ρ =>
        (analyticOrderNatAt riemannZeta ρ : ℝ) / |γ - ρ.im|) := by
    -- trivially true only when 2/T0 ≥ 1, i.e. T0 ≤ 2; NOT the right shape —
    -- the correct split: high part |ρ| ≥ T0/2 gets factor 2/T0; low part
    -- uses the global reciprocal mass.  Implement the split below instead.
    sorry
  -- correct Step 4:
  --   S(γ) = high + low
  --   high: |ρ| ≥ T0/2 ⟹ 1/|ρ| ≤ 2/T0 ⟹ high ≤ (2/T0) · dyadic_sum
  --   low: Im ρ < T0/2 ⟹ |γ - Im ρ| ≥ T0/2 ⟹ low ≤ (2/T0) · global reciprocal mass
  refine ⟨C1 * 2 + C0, by positivity, γ, hγT0, hγT1, ?_⟩
  -- final: S(γ) ≤ C (1+log T1)^2 T1/(T0 H)
  sorry

end DetectionPointChoiceMain
end HalfIsolatedZeroDichotomy
end PrimeNumberTheorem
