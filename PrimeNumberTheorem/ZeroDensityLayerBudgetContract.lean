import PrimeNumberTheorem.ZeroDensityLayerBudget

open scoped BigOperators

namespace PrimeNumberTheorem

example :
    realPartLayer ({0, 1, 2} : Finset ℕ) (fun n => (n : ℝ)) 0 2 = {1, 2} := by
  ext n
  simp [realPartLayer]
  omega

example :
    layeredTailBudget
      ({
        tail := ∅
        layerCount := 0
        layer := Fin.elim0
        pairwise_disjoint := by simp
        sum_decomposition := by simp
      } : LayerCertificate ℕ ℝ)
      Fin.elim0 Fin.elim0 = 0 := by
  simp [layeredTailBudget]

example :
    1 ∈ realPartLayer ({1, 2} : Finset ℕ) (fun n => (n : ℝ)) 0 1 := by
  simp [realPartLayer]

example :
    1 ∉ realPartLayer ({1, 2} : Finset ℕ) (fun n => (n : ℝ)) 1 2 := by
  simp [realPartLayer]

noncomputable def twoStripLayering : RealPartLayering ℕ ℝ where
  tail := {1, 2}
  re := fun n => (n : ℝ)
  layerCount := 2
  lower := ![0, 1]
  upper := ![1, 2]
  strict_strip := by
    intro i
    fin_cases i <;> norm_num
  pairwise_disjoint := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro z hzi hzj
    fin_cases i <;> fin_cases j <;>
      simp_all [realPartLayer]
    all_goals omega
  sum_decomposition := by
    intro term
    have hfirst :
        realPartLayer ({1, 2} : Finset ℕ) (fun n => (n : ℝ)) 0 1 = {1} := by
      ext z
      simp [realPartLayer]
      omega
    have hsecond :
        realPartLayer ({1, 2} : Finset ℕ) (fun n => (n : ℝ)) 1 2 = {2} := by
      ext z
      simp [realPartLayer]
      omega
    rw [Fin.sum_univ_two]
    change
      (∑ z ∈ ({1, 2} : Finset ℕ), term z) =
        (∑ z ∈ realPartLayer ({1, 2} : Finset ℕ)
            (fun n => (n : ℝ)) 0 1, term z) +
          ∑ z ∈ realPartLayer ({1, 2} : Finset ℕ)
            (fun n => (n : ℝ)) 1 2, term z
    rw [hfirst, hsecond]
    simp

example :
    twoStripLayering.certificate.tail = ({1, 2} : Finset ℕ) := by
  rfl

end PrimeNumberTheorem
