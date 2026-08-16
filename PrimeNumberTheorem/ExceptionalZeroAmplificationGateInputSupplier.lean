import PrimeNumberTheorem.ExceptionalZeroAmplificationGateInstantiation
import PrimeNumberTheorem.AmplificationGateExponentBudget
import PrimeNumberTheorem.ZeroDensityAmplificationAuditIteration

/-!
# Gate input supplier: packet data → full `AmplificationGateInputs` bundle

Assembles the six gate inputs from the per-layer windowed-detector packet
data.  The *only* analytic content this module consumes is

- the layer-growth data `hroots`/`hbranch`/`hdisjoint` (the directed
  half-isolated iteration, supplied by the L3 windowed detector),
- the per-window packet data `windows`/`cluster`/`windowStart` with the
  start-separation, per-window lower bound, ambient-membership and
  layer-card facts,
- the exponent budget from `AmplificationGateExponentBudget` (round 36).

Everything else — the `IterativeLocalBranchCertificate` construction, the
`hlower` bridge through `disjointWindowFamilyLowerCount_eventually_le_zeroDensity`,
and the `hgap` instantiation — is proved here.  When the detector line
discharges `GateAssemblyInput` for every feasible tuple (the capstone
`windowedDetector_topLayerMass_exceeds` + the packet count lemma
`topLayerPacket_card_le_of_mass` + the vk-edge signal witness + the cubic-line
`hexplicit`/`herr`), the terminal exclusion follows.

Axiom audit: only `propext`, `Classical.choice`, `Quot.sound` plus the
already-audited gate/budget/bridge modules.
-/

namespace PrimeNumberTheorem
namespace ExceptionalZeroAmplificationGate

open Filter
open HalfIsolatedZeroDichotomy
open scoped BigOperators

/-- Everything the windowed-detector line supplies per feasible parameter
tuple, in addition to the seed-layer growth data.  `windows n T` are the
separated detector windows above layer `n` (identified by their start
markers), `cluster n i` is the packet of forced top-layer zeros in window
`i`, and `windowStart n i` is the window's lower edge. -/
structure GateAssemblyInput (β δ sigma H : ℝ) (depth : ℕ) where
  hσ : (1 / 2 : ℝ) < sigma
  hσ1 : sigma < 1
  hH : 0 ≤ H
  roots : ℝ → Finset ℂ
  q : ℝ → ℕ
  windows : ℕ → ℝ → Finset ℂ
  cluster : ℕ → ℂ → Finset ℂ
  windowStart : ℕ → ℂ → ℝ
  -- 1. seed: every height has at least one root
  hroots : ∀ᶠ T in atTop, 1 ≤ (roots T).card
  -- 2. branching: each directed half-isolated zero has `q T` successors
  hbranch :
    ∀ n < depth, ∀ᶠ T in atTop,
      ∀ z ∈ halfIsolatedDirectedIteration T β δ n (roots T),
        q T ≤ (halfIsolatedDirectedNext T β δ z).card
  -- 3. separation: successor sets are pairwise disjoint layer by layer
  hdisjoint :
    ∀ n < depth, ∀ᶠ T in atTop,
      ((↑(halfIsolatedDirectedIteration T β δ n (roots T)) : Set ℂ)).PairwiseDisjoint
        (halfIsolatedDirectedNext T β δ)
  -- 4. the layer at depth is covered by the window count
  hbranch_le :
    ∀ᶠ T in atTop,
      (iterativeWindowLayer roots (fun _ T ρ => halfIsolatedDirectedNext T β δ ρ) depth T).card ≤
        (windows depth T).card
  -- window structure
  hadjacent :
    ∀ n < depth + 1, ∀ᶠ T in atTop,
      windowStartPairwiseSeparated (windows n T) (windowStart n) H
  hlocal :
    ∀ n < depth + 1, ∀ᶠ T in atTop, ∀ i ∈ windows n T,
      1 ≤ localClusterLowerBound (cluster n i) (fun z : ℂ => z.re) (fun z : ℂ => z.im)
        sigma (windowStart n i) H
  hinside :
    ∀ᶠ T in atTop, ∀ i ∈ windows depth T,
      disjointWindowClusterSlice (cluster depth i) (fun z : ℂ => z.re) (fun z : ℂ => z.im)
          sigma (windowStart depth i) H ⊆
        ZeroDensity.zeroDensityZerosFinset sigma (T + H)
  -- 6. exponent budget data
  h' : ℝ
  hq : ∀ᶠ T in atTop, T ^ h' ≤ (q T : ℝ)
  hqexp : 4 * sigma * (1 - sigma) < h' * depth

/-- The local-branch certificate built from the assembly data: windows at
each layer with the packet clusters, `branchCount` the window count and
`localContribution = 1`. -/
noncomputable def assemblyCertificate {β δ sigma H : ℝ} {depth : ℕ}
    (A : GateAssemblyInput β δ sigma H depth) :
    IterativeLocalBranchCertificate (ι := ℂ) (ρ := ℂ)
      (fun z : ℂ => z.re) (fun z : ℂ => z.im) sigma H where
  depth := depth + 1
  windows := A.windows
  cluster := A.cluster
  windowStart := A.windowStart
  branchCount := fun n T => (A.windows n T).card
  localContribution := 1
  hdepth_pos := by omega
  hlocalContribution_pos := by norm_num
  hadjacent := A.hadjacent
  hbranches := by
    intro n hn
    filter_upwards with T
    rfl
  hlocal := A.hlocal

/-- The ambient count bound: the density zero finset's cardinality (without
multiplicity) is dominated by the multiplicity-counted `zeroDensityCount`. -/
theorem zeroDensityZerosFinset_card_le_zeroDensityCount {sigma T : ℝ}
    (hσ1 : sigma < 1) :
    ((ZeroDensity.zeroDensityZerosFinset sigma T).card : ℝ) ≤
      (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
  unfold ZeroDensity.zeroDensityCount
  have hper {ρ : ℂ} (hρ : ρ ∈ ZeroDensity.zeroDensityZerosFinset sigma T) :
      1 ≤ analyticOrderNatAt riemannZeta ρ := by
    rcases ZeroDensity.mem_zeroDensityZerosFinset.mp hρ with ⟨hz, him, hheight, hre⟩
    have hρ1 : ρ ≠ 1 := by
      intro h1
      have hlt := hz.2.2
      rw [h1] at hlt
      norm_num at hlt
    exact Nat.succ_le_iff.mpr
      (ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero hρ1 hz.1)
  calc
    ((ZeroDensity.zeroDensityZerosFinset sigma T).card : ℝ) =
        (∑ ρ ∈ ZeroDensity.zeroDensityZerosFinset sigma T, (1 : ℕ) : ℝ) := by
      simp
    _ ≤ (∑ ρ ∈ ZeroDensity.zeroDensityZerosFinset sigma T,
          (analyticOrderNatAt riemannZeta ρ : ℝ)) := by
      exact Finset.sum_le_sum (fun ρ hρ => by exact_mod_cast hper hρ)
    _ = ((∑ rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T,
          analyticOrderNatAt riemannZeta rho : ℕ) : ℝ) := by
      exact_mod_cast (by rfl)

/-- Gate input 5 (`hlower`) from the assembly data: the certified window
count is realized by genuine zeta zeros counted by `zeroDensityCount`. -/
theorem amplificationGateInputs_hlower {β δ sigma H : ℝ} {depth : ℕ}
    (A : GateAssemblyInput β δ sigma H depth) :
    ∀ᶠ T in atTop,
      disjointWindowFamilyLowerCount ((assemblyCertificate A).windows depth)
          ((assemblyCertificate A).cluster depth) ((assemblyCertificate A).windowStart depth)
          (fun z : ℂ => z.re) (fun z : ℂ => z.im) sigma H T ≤
        (ZeroDensity.zeroDensityCount sigma (T + H) : ℝ) := by
  dsimp [assemblyCertificate]
  have hdisj_slices : ∀ᶠ T in atTop,
      ((A.windows depth T : Set ℂ).PairwiseDisjoint fun i =>
        disjointWindowClusterSlice (A.cluster depth i) (fun z : ℂ => z.re) (fun z : ℂ => z.im)
          sigma (A.windowStart depth i) H) := by
    have hcert := IterativeLocalBranchCertificate.disjointWindowClusterSlices
      (ι := ℂ) (ρ := ℂ) (realPart := fun z : ℂ => z.re) (ordinate := fun z : ℂ => z.im)
      (sigma := sigma) (H := H) (assemblyCertificate A) depth
        (by dsimp [assemblyCertificate]; omega)
    simpa [assemblyCertificate] using hcert
  have hambient : ∀ᶠ T in atTop,
      ((ZeroDensity.zeroDensityZerosFinset sigma (T + H)).card : ℝ) ≤
        (ZeroDensity.zeroDensityCount sigma (T + H) : ℝ) := by
    filter_upwards with T
    exact zeroDensityZerosFinset_card_le_zeroDensityCount (sigma := sigma) (T := T + H) A.hσ1
  have hb := disjointWindowFamilyLowerCount_eventually_le_zeroDensity
    (windows := A.windows depth) (cluster := A.cluster depth)
    (windowStart := A.windowStart depth)
    (realPart := fun z : ℂ => z.re) (ordinate := fun z : ℂ => z.im)
    (sigma := sigma) (H := H)
    hdisj_slices (ambient := fun T => ZeroDensity.zeroDensityZerosFinset sigma T)
    (hinside := by
      simpa using A.hinside) hambient
  simpa using hb

/-- Gate input 6 (`hgap`) from the assembly data: the growth budget via
`AmplificationGateExponentBudget.tendsto_qPower_sub_carlsonMajorant_atTop`. -/
theorem amplificationGateInputs_hgap {β δ sigma H : ℝ} {depth : ℕ}
    (A : GateAssemblyInput β δ sigma H depth) :
    Filter.Tendsto
      (fun T =>
        ((assemblyCertificate A).localContribution : ℝ) * (A.q T ^ depth) -
          ((Classical.choice (exists_carlsonEventualMajorant A.hσ A.hσ1)).C *
            ‖(T + H) ^ (4 * sigma * (1 - sigma)) * (Real.log (T + H)) ^ 4‖))
      Filter.atTop Filter.atTop := by
  dsimp [assemblyCertificate]
  have hσ0 : 0 < sigma := lt_trans (by norm_num : 0 < (1 / 2 : ℝ)) A.hσ
  have hC : 0 ≤ (Classical.choice (exists_carlsonEventualMajorant A.hσ A.hσ1)).C :=
    (Classical.choice (exists_carlsonEventualMajorant A.hσ A.hσ1)).C_nonneg
  have hb := tendsto_qPower_sub_carlsonMajorant_atTop
    (σ := sigma) (C := (Classical.choice (exists_carlsonEventualMajorant A.hσ A.hσ1)).C)
    (H := H) (h' := A.h') (cl := (1 : ℝ)) (q := A.q) (depth := depth)
    hσ0 A.hσ1 hC A.hH (by norm_num : 0 < (1 : ℝ)) A.hq A.hqexp
  simpa [one_mul] using hb

/-- The full gate bundle from the assembly data. -/
noncomputable def amplificationGateInputs_of_assembly {β δ sigma H : ℝ} {depth : ℕ}
    (A : GateAssemblyInput β δ sigma H depth) :
    AmplificationGateInputs β δ sigma H depth where
  hσ := A.hσ
  hσ1 := A.hσ1
  roots := A.roots
  q := A.q
  certificate := assemblyCertificate A
  hdepth := by dsimp [assemblyCertificate]; omega
  hroots := A.hroots
  hbranch := A.hbranch
  hdisjoint := A.hdisjoint
  hbranch_le := by
    filter_upwards [A.hbranch_le] with T hT
    dsimp [assemblyCertificate]
    exact hT
  hlower := amplificationGateInputs_hlower A
  hgap := amplificationGateInputs_hgap A

/--
Terminal interface through the assembly: if the windowed-detector line
supplies `GateAssemblyInput` for every feasible parameter tuple, then no
non-trivial zero has real part `> 2/3`.
-/
theorem no_nontrivial_zero_re_gt_two_thirds_of_assembly
    (hAssembly : ∀ β δ σ H : ℝ, ∀ depth : ℕ,
      (2 / 3 : ℝ) < β → β < 1 → (1 / 2 : ℝ) < σ → σ < β → 0 < δ → 0 < H →
        GateAssemblyInput β δ σ H depth) :
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → ρ.re ≤ (2 / 3 : ℝ) := by
  refine no_nontrivial_zero_re_gt_two_thirds_of_gateInputs ?_
  intro β δ σ H depth hβ hβ1 hσ hσβ hδ hH
  exact amplificationGateInputs_of_assembly
    (hAssembly β δ σ H depth hβ hβ1 hσ hσβ hδ hH)

end ExceptionalZeroAmplificationGate
end PrimeNumberTheorem
