/-!
Stub for the cubic-line bridging: where `actual-cubic-two-height-l2-tail`'s
`DirectL2` module and the two ported capacity modules
(`ZeroDensityLayerBudgetDyadicSquareMultiplicityCapacity`,
`ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility`) plug into
`SingleLayerForcingCertificate`, closing the unconditional theorem
`no_nontrivial_zero_re_gt_14_over_17_of_certificates`.

The forcing-bound (energy antecedent + energy→count bridge) is already
delivered in:
  - `PrimeNumberTheorem.SingleLayerForcingBeta14Over17`
  - `PrimeNumberTheorem.SharpWitnessTransfer`
    (`forcingLowerCount_of_energyTransfer`,
     `forcingLowerCount_clean_of_residualDominated`)
  - `PrimeNumberTheorem.SingleLayerForcingBeta14Over17Contract`

What's still needed: a concrete instance of
`SingleLayerForcingCertificate β lam` for every β ∈ (14/17, 1), lam > 0.
The instance requires the cubic-line dyadic L² lower bound plus the
two-height parameter feasibility — exactly what the ported
`actual-cubic-two-height-l2-tail` modules compute.

To wire it (off-peak):
  1. Bring `DirectL2` from `actual-cubic-two-height-l2-tail` into this
     worktree as a dep.
  2. Compose a theorem of the form:
       singleLayerForcingCertificate_of_cubicLine :
         (DirectL2.bound + capacity bounds) →
         ∀ β lam, (14/17 : ℝ) < β → β < 1 → 0 < lam →
           SingleLayerForcingCertificate β lam
  3. Then:
       theorem no_nontrivial_zero_re_gt_14_over_17 :
         ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → ρ.re ≤ 14/17 :=
         no_nontrivial_zero_re_gt_14_over_17_of_certificates
           singleLayerForcingCertificate_of_cubicLine
  4. `lake build PrimeNumberTheorem.CubicLineForcingCertificate` to
     verify, then run the axiom audit (in a scratch file using
     `#print axioms PrimeNumberTheorem.no_nontrivial_zero_re_gt_14_over_17`)
     to confirm the same minimal core:
     `[propext, Classical.choice, Quot.sound]`.

Heavy-build impact under 4.33-rc2:
  - `MeromorphicAux.lean`: 22 remaining 4.33 drift sites (the FEPair
    port `WeakFEPair` / `IsStrongFEPair` rename is done).
  - `FirstOrderLSeriesPerron.lean:1285` `ring_nf` no-progress.
  - The two capacity modules under 4.33-rc2 (the ported5 cubic files
    are committed; these 2 capacity modules are still `import`-able but
    not yet buildable).
-/

namespace PrimeNumberTheorem

/-! ### Plug-in point

`SingleLayerForcingCertificate` is the structure that the unconditional
closure consumes. Its `lower` field is the eventually-inequality

    c * X^e * (log X)^(-k) ≤ N(2/3, X^(lam(1-β))),

with
`e = 2lam(β-2/3) - lam(1-β) * (4 * 2/3 * (1-2/3))`.

The 4.33 sync of the upstream cubic-line modules should yield this
inequality directly; if not, the energy→count bridge already in
`SharpWitnessTransfer` (combined with `DirectL2`'s L² lower bound) can
assemble it. -/

end PrimeNumberTheorem