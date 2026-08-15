import PrimeNumberTheorem.ExceptionalZeroAmplificationIntegration

/-!
# The Amplification Gate: a single contract for the whole route

The gate is the one remaining unproved mechanism of the `β > 2/3` exclusion
route.  Its mathematical statement is:

    a seed zero `ρ₀` with `β = Re ρ₀ > 2/3`
    ⟹
    on some height sequence `T → ∞` the right-half-plane zero count grows
    faster than the Carlson upper bound.

Formally, the conclusion is `False` from six unproved inputs.  The
contradiction assembly itself is *already proved*: this file only instantiates
`iterativeWindowLayer_to_carlson_contradiction` with the directed
half-isolated successor relation.  Nothing here is an `axiom`; every
assumption is an explicit parameter, so the axiom audit prints exactly the
existing repository assumptions (in particular the Carlson density theorem
behind `exists_carlsonEventualMajorant`).

The six inputs, each a separate subproject:

1. `hroots`     — the seed: every layer height `T` has at least one root.
2. `hbranch`    — branching: every directed half-isolated zero at layer `n`
                  has at least `q T` strictly-higher-imaginary successors.
                  (`q : ℝ → ℕ` is height-dependent: the dynamic packet.)
3. `hdisjoint`  — separation: successor sets of distinct layer-`n` vertices
                  are pairwise disjoint (no shared-neighbor collapse).
4. `certificate`/`hdepth` — the iterative local-branch certificate `C`
                  packaging windows, clusters, and the per-window lower bound.
5. `hlower`     — the certified window count is realized by actual zeta
                  zeros: `disjointWindowFamilyLowerCount … ≤ N(σ, T+H)`.
6. `hgap`       — exponent budget: `localContribution · q(T)^depth` eventually
                  beats the Carlson upper bound
                  `C · (T+H)^{4σ(1-σ)} · log⁴(T+H)`.

The terminal interface `amplificationGate_excludes_seed` turns any `False`
obtained from the gate into the exclusion of non-trivial zeros with real part
strictly larger than `2/3`; the Mellin–Landau backend
`psiPowerErrorBound_excludes_riemannZeta_zero_right` supplies the remaining
link from a power error bound to that exclusion, as documented in
`docs/research` (direct-L2 cubic design).
-/

namespace PrimeNumberTheorem
namespace ExceptionalZeroAmplificationGate

open Filter
open HalfIsolatedZeroDichotomy
open ExceptionalZeroAmplification

/--
The single gate theorem.  All six unproved inputs are explicit parameters;
the conclusion is `False`, obtained from the already-proved iterative
Carlson contradiction by instantiating its layer certificate with the
directed half-isolated successor relation.

The branch-le counting input is stated in `iterativeWindowLayer` form so that
it is definitionally the hypothesis expected by the proved assembly; it is
equivalent to the directed-iteration form by
`iterativeWindowLayer_eq_halfIsolatedDirectedIteration`.
-/
theorem amplificationGate
    {β δ sigma H : ℝ}
    (hσ : (1 / 2 : ℝ) < sigma) (hσ1 : sigma < 1)
    (depth : ℕ)
    (roots : ℝ → Finset ℂ) (q : ℝ → ℕ)
    (C : IterativeLocalBranchCertificate (ι := ℂ) (ρ := ℂ)
      (realPart := fun z : ℂ => z.re) (ordinate := fun z : ℂ => z.im) sigma H)
    (hdepth : depth < C.depth)
    -- 1. seed: every height has at least one root
    (hroots : ∀ᶠ T in atTop, 1 ≤ (roots T).card)
    -- 2. branching: each directed half-isolated zero has `q T` successors
    (hbranch :
      ∀ n < depth, ∀ᶠ T in atTop,
        ∀ z ∈ halfIsolatedDirectedIteration T β δ n (roots T),
          q T ≤ (halfIsolatedDirectedNext T β δ z).card)
    -- 3. separation: successor sets are pairwise disjoint layer by layer
    (hdisjoint :
      ∀ n < depth, ∀ᶠ T in atTop,
        ((↑(halfIsolatedDirectedIteration T β δ n (roots T)) : Set ℂ)).PairwiseDisjoint
          (halfIsolatedDirectedNext T β δ))
    -- 4+5. the certified layer count is dominated by real zeta zeros
    (hbranch_le :
      ∀ᶠ T in atTop,
        (iterativeWindowLayer roots
            (fun _ T ρ => halfIsolatedDirectedNext T β δ ρ) depth T).card ≤
          C.branchCount depth T)
    (hlower :
      ∀ᶠ T in atTop,
        disjointWindowFamilyLowerCount (C.windows depth) (C.cluster depth)
            (C.windowStart depth) (fun z : ℂ => z.re) (fun z : ℂ => z.im)
            sigma H T ≤
          (ZeroDensity.zeroDensityCount sigma (T + H) : ℝ))
    -- 6. exponent budget: growth beats the Carlson upper bound
    (hgap :
      Filter.Tendsto
        (fun T =>
          (C.localContribution : ℝ) * (q T ^ depth) -
            ((Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
              ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
                (Real.log (T + H)) ^ 4‖))
        Filter.atTop Filter.atTop) :
    False := by
  exact
    iterativeWindowLayer_to_carlson_contradiction
      (ι := ℂ) (ρ := ℂ)
      (realPart := fun z : ℂ => z.re) (ordinate := fun z : ℂ => z.im)
      (C := C) depth hdepth
      (L := halfIsolatedDirectedWindowLayerCertificate depth roots q β δ
        hroots hbranch hdisjoint)
      (by dsimp [halfIsolatedDirectedWindowLayerCertificate]; exact le_rfl)
      hbranch_le hσ hσ1 hlower hgap

/--
The complete unproved-input bundle of the gate, packaged so that downstream
work can name "the remaining obligations" as a single object and the axiom
audit can track which inputs are still open.
-/
structure AmplificationGateInputs (β δ sigma H : ℝ) (depth : ℕ) where
  hσ : (1 / 2 : ℝ) < sigma
  hσ1 : sigma < 1
  roots : ℝ → Finset ℂ
  q : ℝ → ℕ
  certificate : IterativeLocalBranchCertificate (ι := ℂ) (ρ := ℂ)
    (fun z : ℂ => z.re) (fun z : ℂ => z.im) sigma H
  hdepth : depth < certificate.depth
  hroots : ∀ᶠ T in atTop, 1 ≤ (roots T).card
  hbranch :
    ∀ n < depth, ∀ᶠ T in atTop,
      ∀ z ∈ halfIsolatedDirectedIteration T β δ n (roots T),
        q T ≤ (halfIsolatedDirectedNext T β δ z).card
  hdisjoint :
    ∀ n < depth, ∀ᶠ T in atTop,
      ((↑(halfIsolatedDirectedIteration T β δ n (roots T)) : Set ℂ)).PairwiseDisjoint
        (halfIsolatedDirectedNext T β δ)
  hbranch_le :
    ∀ᶠ T in atTop,
      (iterativeWindowLayer roots
          (fun _ T ρ => halfIsolatedDirectedNext T β δ ρ) depth T).card ≤
        certificate.branchCount depth T
  hlower :
    ∀ᶠ T in atTop,
      disjointWindowFamilyLowerCount (certificate.windows depth)
          (certificate.cluster depth) (certificate.windowStart depth)
          (fun z : ℂ => z.re) (fun z : ℂ => z.im) sigma H T ≤
        (ZeroDensity.zeroDensityCount sigma (T + H) : ℝ)
  hgap :
    Filter.Tendsto
      (fun T =>
        (certificate.localContribution : ℝ) * (q T ^ depth) -
          ((Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
            ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
              (Real.log (T + H)) ^ 4‖))
      Filter.atTop Filter.atTop

/-- The gate applied to the packaged input bundle. -/
theorem amplificationGate_of_inputs {β δ sigma H : ℝ} {depth : ℕ}
    (G : AmplificationGateInputs β δ sigma H depth) : False :=
  amplificationGate G.hσ G.hσ1 depth G.roots G.q G.certificate G.hdepth
    G.hroots G.hbranch G.hdisjoint G.hbranch_le G.hlower G.hgap

/--
Terminal interface: any `False` obtained from the gate excludes non-trivial
zeta zeros with real part strictly larger than `2/3`.  This is pure
`exfalso`: the remaining work is to turn a hypothetical seed zero into the
six gate inputs, then apply this theorem.
-/
theorem amplificationGate_excludes_seed
    (hFalse : False) :
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → ρ.re ≤ (2 / 3 : ℝ) := by
  intro ρ hρ
  exact False.elim hFalse

end ExceptionalZeroAmplificationGate
end PrimeNumberTheorem
