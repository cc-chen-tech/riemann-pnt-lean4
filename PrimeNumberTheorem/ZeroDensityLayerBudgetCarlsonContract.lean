import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlson

open scoped BigOperators

namespace PrimeNumberTheorem

def emptyZeroCount : ℝ → ℝ → ℕ := fun _ _ => 0

def emptyZeroMajorant : ℝ → ℝ → ℝ := fun _ _ => 0

example : ZeroDensityMajorant emptyZeroCount emptyZeroMajorant := by
  intro σ T
  simp [emptyZeroCount, emptyZeroMajorant]

noncomputable def emptyLayerCertificate : LayerCertificate ℕ ℝ where
  tail := ∅
  layerCount := 0
  layer := Fin.elim0
  pairwise_disjoint := by simp
  sum_decomposition := by simp

noncomputable def emptyLayerDensity :
    LayerDensityCertificate emptyLayerCertificate :=
  LayerDensityCertificate.ofMajorant
    emptyLayerCertificate
    emptyZeroCount
    emptyZeroMajorant
    (fun i => Fin.elim0 i)
    4
    (by
      intro σ T
      simp [emptyZeroCount, emptyZeroMajorant])
    (by
      intro i
      exact Fin.elim0 i)

example :
    layeredTailBudget emptyLayerCertificate emptyLayerDensity.occupancy
      Fin.elim0 = 0 := by
  unfold layeredTailBudget
  apply Finset.sum_eq_zero
  intro i _
  exact Fin.elim0 i

example {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    Nonempty (CarlsonEventualMajorant σ) :=
  exists_carlsonEventualMajorant hσ hσ1

end PrimeNumberTheorem
