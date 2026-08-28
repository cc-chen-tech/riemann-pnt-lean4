import PrimeNumberTheorem.MWKFCubicAggregation

open Filter Asymptotics
open scoped BigOperators Topology

namespace PrimeNumberTheorem.MWKFCubic

#check (@isLittleO_finset_sum :
  ∀ {ι α E : Type*} [NormedAddCommGroup E]
    {l : Filter α} {s : Finset ι} {f : ι → α → E} {g : α → E},
    (∀ i ∈ s, f i =o[l] g) →
      (fun x ↦ ∑ i ∈ s, f i x) =o[l] g)

#check (@long_mollifier_reassembly :
  ∀ (I Q R : ℝ → ℝ) (C : ℝ),
    (∀ T, I T = T * Q T + R T) →
    (fun T ↦ Q T - C) =o[atTop] (fun _T ↦ (1 : ℝ)) →
    R =o[atTop] (fun T : ℝ ↦ T) →
    (fun T ↦ I T - C * T) =o[atTop] (fun T : ℝ ↦ T))

end PrimeNumberTheorem.MWKFCubic
