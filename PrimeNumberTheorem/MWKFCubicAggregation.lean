import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas

open Filter Asymptotics
open scoped BigOperators Topology

namespace PrimeNumberTheorem
namespace MWKFCubic

/-!
# Finite aggregation and final MWKF reassembly

The analytic proof partitions the remainder into finitely many disjoint shell
types.  This module records the exact little-o bookkeeping and the final
algebraic implication independently of the deep local estimate.
-/

/-- A finite collection of local little-o bounds remains little-o after the
dyadic/shell pieces are summed. -/
theorem isLittleO_finset_sum
    {ι α E : Type*} [NormedAddCommGroup E]
    {l : Filter α} {s : Finset ι} {f : ι → α → E} {g : α → E}
    (h : ∀ i ∈ s, f i =o[l] g) :
    (fun x ↦ ∑ i ∈ s, f i x) =o[l] g := by
  exact IsLittleO.sum h

/-- Exact final reassembly: an exact `I = T*Q + R` decomposition, a
`Q = C + o(1)` main term, and `R = o(T)` imply `I = C*T + o(T)`.

This theorem deliberately accepts the three analytic facts as hypotheses.  It
does not turn an unformalized local spectral estimate into an axiom. -/
theorem long_mollifier_reassembly
    (I Q R : ℝ → ℝ) (C : ℝ)
    (hexact : ∀ T, I T = T * Q T + R T)
    (hmain : (fun T ↦ Q T - C) =o[atTop] (fun _T ↦ (1 : ℝ)))
    (hrem : R =o[atTop] (fun T : ℝ ↦ T)) :
    (fun T ↦ I T - C * T) =o[atTop] (fun T : ℝ ↦ T) := by
  have hscaled :
      (fun T ↦ (Q T - C) * T) =o[atTop] (fun T : ℝ ↦ T) := by
    have h := hmain.mul_isBigO (isBigO_refl (fun T : ℝ ↦ T) atTop)
    simpa using h
  have hsum :
      (fun T ↦ (Q T - C) * T + R T) =o[atTop] (fun T : ℝ ↦ T) :=
    hscaled.add hrem
  apply hsum.congr'
  filter_upwards [] with T
  rw [hexact]
  ring
  exact EventuallyEq.rfl

end MWKFCubic
end PrimeNumberTheorem
