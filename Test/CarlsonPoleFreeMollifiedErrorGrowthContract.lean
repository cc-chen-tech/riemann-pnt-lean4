import PrimeNumberTheorem.CarlsonPoleFreeMollifiedErrorGrowth

open Complex Set

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example (Y0 Y1 : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {x t : ℝ},
      x ∈ Icc (1 / 2 : ℝ) 4 → t ∈ Icc (-1 : ℝ) 1 →
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
          ((x : ℂ) + I * (t : ℂ))‖ ≤ M :=
  exists_norm_poleFreeTwoScaleMollifiedZetaError_le_on_compact_strip Y0 Y1

#print axioms
  exists_norm_poleFreeTwoScaleMollifiedZetaError_le_on_compact_strip

end CarlsonZeroDensity
end PrimeNumberTheorem
