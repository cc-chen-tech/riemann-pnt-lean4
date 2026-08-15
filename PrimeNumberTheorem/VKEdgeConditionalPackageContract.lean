import PrimeNumberTheorem.VKEdgeConditionalPackage

open Complex Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgeConditionalPackage
/-- Contract invocation for the half-isolated regime. -/
theorem halfIsolatedEnvelopeBridge_contract
    (h : HalfIsolatedEnvelopeInput) :
    HalfIsolatedConclusion h :=
  halfIsolatedEnvelopeBridge h

/-- Contract invocation for the clustered regime bridge: all preconditions are explicit and
    checked in the theorem statement. -/
theorem clusteredEnvelopeBridge_contract
    (h : ClusteredEnvelopeInput) :
    ClusteredConclusion h :=
  clusteredEnvelopeBridge h

/-! Clustered-route contract is deferred in this branch.

Use `VKEdgeConditionalPackageAudit` for remaining explicit blockers.
-/

end VKEdgeConditionalPackage
end PrimeNumberTheorem
