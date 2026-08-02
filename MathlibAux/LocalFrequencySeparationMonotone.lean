import PrimeNumberTheorem.LocalSeparationKernel

/-!
# Monotonicity of local frequency separation

Removing frequencies from a finite family can only increase the distance from
a retained frequency to its nearest distinct neighbour.
-/

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- Local frequency separation is antitone in the finite frequency family at
an index retained by the smaller nontrivial family. -/
theorem localFrequencySeparation_mono_of_subset
    {ι : Type*} [DecidableEq ι] {S R : Finset ι} {omega : ι → ℝ} {n : ι}
    (hSR : S ⊆ R) (hS : S.Nontrivial) :
    localFrequencySeparation R omega n ≤
      localFrequencySeparation S omega n := by
  have hEraseS : (S.erase n).Nonempty := hS.erase_nonempty
  have hEraseSub : S.erase n ⊆ R.erase n := by
    intro m hm
    have hm' := Finset.mem_erase.mp hm
    exact Finset.mem_erase.mpr ⟨hm'.1, hSR hm'.2⟩
  have hEraseR : (R.erase n).Nonempty := hEraseS.mono hEraseSub
  simp only [localFrequencySeparation, dif_pos hEraseR, dif_pos hEraseS]
  rw [Finset.le_inf'_iff]
  intro m hm
  exact Finset.inf'_le _ (hEraseSub hm)

end DirichletPolynomial
end PrimeNumberTheorem
