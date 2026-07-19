import ZeroFreeRegion.VinogradovKorobov.RecursiveZetaBounds

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (t : ℝ) (m N depth : ℕ) : ℝ :=
  zetaAProcessUniformLeafDeltaLower t m N depth

noncomputable example (t : ℝ) (m N depth : ℕ) : ℝ :=
  zetaAProcessUniformLeafSquaredBound t m N depth

noncomputable example (t : ℝ) (m N depth : ℕ) (shifts : List ℕ) : ℝ :=
  zetaAProcessProductLeafSquaredBound t m N depth shifts

noncomputable example (t : ℝ) (m N depth : ℕ) (shifts : List ℕ) : ℝ :=
  zetaAProcessHybridProductLeafSquaredBound t m N depth shifts

example (t : ℝ) (m₁ N₁ m₂ N₂ depth : ℕ)
    (ht : 0 ≤ t) (hleft : 0 < m₁ + N₁)
    (hend : m₁ + N₁ ≤ m₂ + N₂) :
    zetaAProcessUniformLeafDeltaLower t m₂ N₂ depth ≤
      zetaAProcessUniformLeafDeltaLower t m₁ N₁ depth :=
  zetaAProcessUniformLeafDeltaLower_antitone_endpoint
    t m₁ N₁ m₂ N₂ depth ht hleft hend

example (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hR : 1 ≤ remainingAProcessLength N shifts)
    (hshifts : ∀ h ∈ shifts, 0 < h)
    (hdepth : shifts.length = depth) :
    zetaAProcessUniformLeafDeltaLower t m N depth ≤
      zetaAProcessLeafDelta t m N shifts :=
  zetaAProcessUniformLeafDeltaLower_le
    t m N depth shifts ht hm hR hshifts hdepth

example (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hR : 1 ≤ remainingAProcessLength N shifts)
    (hshifts : ∀ h ∈ shifts, 0 < h)
    (hdepth : shifts.length = depth) :
    zetaAProcessLeafSquaredBound t m N shifts ≤
      zetaAProcessUniformLeafSquaredBound t m N depth :=
  zetaAProcessLeafSquaredBound_le_uniform
    t m N depth shifts ht hm hR hshifts hdepth

example (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hR : 1 ≤ remainingAProcessLength N shifts)
    (hdepth : shifts.length = depth) :
    zetaAProcessUniformLeafDeltaLower t m N depth * (shifts.prod : ℝ) ≤
      zetaAProcessLeafDelta t m N shifts :=
  zetaAProcessUniformLeafDeltaLower_mul_prod_le
    t m N depth shifts ht hm hR hdepth

example (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hR : 1 ≤ remainingAProcessLength N shifts)
    (hshifts : ∀ h ∈ shifts, 0 < h)
    (hdepth : shifts.length = depth) :
    zetaAProcessLeafSquaredBound t m N shifts ≤
      zetaAProcessProductLeafSquaredBound t m N depth shifts :=
  zetaAProcessLeafSquaredBound_le_product
    t m N depth shifts ht hm hR hshifts hdepth

example (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hscale : ZetaAProcessScaleLeafValid t m N shifts)
    (hdepth : shifts.length = depth) :
    zetaAProcessHybridLeafSquaredBound t m N shifts ≤
      zetaAProcessHybridProductLeafSquaredBound t m N depth shifts :=
  zetaAProcessHybridLeafSquaredBound_le_productMin
    t m N depth shifts ht hm hscale hdepth

example (t : ℝ) (m N totalDepth depth : ℕ) (H : ℕ → ℕ)
    (shifts : List ℕ) (ht : 0 < t) (hm : 0 < m)
    (hlen : shifts.length + depth = totalDepth)
    (hvalid : RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth shifts) :
    RecursiveAProcessValid (shiftedZetaPhase t m) (fun s ↦ H s.length)
      (zetaAProcessHybridProductLeafSquaredBound t m N totalDepth)
      N depth shifts :=
  recursiveZetaAProcessScaleValid_to_hybridProductGeneric
    t m N totalDepth depth H shifts ht hm hlen hvalid

example (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      recursiveAProcessSquaredBound (fun s ↦ H s.length)
        (zetaAProcessHybridProductLeafSquaredBound t m N depth)
        N depth [] :=
  norm_zetaPhase_sum_sq_le_hybridProductRecursiveAProcess_of_scale
    t m N depth H ht hm hvalid

example (t : ℝ) (m N totalDepth depth : ℕ) (H : ℕ → ℕ)
    (shifts : List ℕ) (ht : 0 < t) (hm : 0 < m)
    (hlen : shifts.length + depth = totalDepth)
    (hvalid : RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth shifts) :
    RecursiveAProcessValid (shiftedZetaPhase t m) (fun s ↦ H s.length)
      (fun _ ↦ zetaAProcessUniformLeafSquaredBound t m N totalDepth)
      N depth shifts :=
  recursiveZetaAProcessScaleValid_to_uniformGeneric
    t m N totalDepth depth H shifts ht hm hlen hvalid

example (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      coarseRecursiveAProcessSquaredBound H N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 :=
  norm_zetaPhase_sum_sq_le_uniformCoarseRecursiveAProcess
    t m N depth H ht hm hvalid

end ZeroFreeRegion.VinogradovKorobov
