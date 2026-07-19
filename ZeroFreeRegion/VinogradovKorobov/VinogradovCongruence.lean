import ZeroFreeRegion.VinogradovKorobov.VinogradovSymmetry
import Mathlib.Data.Int.ModEq

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- A tuple contained in one residue class modulo `q` has affine coordinates
with common offset and scale. -/
theorem exists_affineCoordinates_of_forall_modEq {s : ℕ}
    (x : Fin s → ℤ) (a q : ℤ)
    (h : ∀ i, Int.ModEq q a (x i)) :
    ∃ z : Fin s → ℤ, x = fun i => a + q * z i := by
  choose z hz using fun i => Int.modEq_iff_add_fac.mp (h i)
  exact ⟨z, funext hz⟩

/-- A common affine change with nonzero scale preserves and reflects the
integer Vinogradov system. -/
theorem isVinogradovSolutionInt_affine_iff {k s : ℕ}
    (x y : Fin s → ℤ) (a : ℤ) {q : ℤ} (hq : q ≠ 0) :
    IsVinogradovSolutionInt k s
        (fun i => a + q * x i) (fun i => a + q * y i) ↔
      IsVinogradovSolutionInt k s x y := by
  calc
    IsVinogradovSolutionInt k s
        (fun i => a + q * x i) (fun i => a + q * y i) ↔
      IsVinogradovSolutionInt k s
        (fun i => q * x i) (fun i => q * y i) := by
          simpa only [add_comm] using
            isVinogradovSolutionInt_translate_iff
              (fun i => q * x i) (fun i => q * y i) a
    _ ↔ IsVinogradovSolutionInt k s x y :=
      isVinogradovSolutionInt_scale_iff x y hq

/-- If both sides of an integer Vinogradov solution lie in one residue class
modulo a nonzero `q`, removing the common offset and scale produces another
integer Vinogradov solution. -/
theorem IsVinogradovSolutionInt.rescale_of_common_modEq {k s : ℕ}
    {x y : Fin s → ℤ} (h : IsVinogradovSolutionInt k s x y)
    (a q : ℤ) (hq : q ≠ 0)
    (hx : ∀ i, Int.ModEq q a (x i))
    (hy : ∀ i, Int.ModEq q a (y i)) :
    ∃ x' y' : Fin s → ℤ,
      x = (fun i => a + q * x' i) ∧
      y = (fun i => a + q * y' i) ∧
      IsVinogradovSolutionInt k s x' y' := by
  obtain ⟨x', hx'⟩ :=
    exists_affineCoordinates_of_forall_modEq x a q hx
  obtain ⟨y', hy'⟩ :=
    exists_affineCoordinates_of_forall_modEq y a q hy
  refine ⟨x', y', hx', hy', ?_⟩
  rw [hx', hy'] at h
  exact (isVinogradovSolutionInt_affine_iff x' y' a hq).mp h

end

end ZeroFreeRegion.VinogradovKorobov
