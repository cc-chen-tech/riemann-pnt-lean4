import MathlibAux.HadamardThreeLinesSquared

open Set Function Complex

namespace MathlibAux

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {z : ℂ} {a b l u : ℝ}
    (hul : l < u)
    (hz : z ∈ HadamardThreeLines.verticalClosedStrip l u)
    (hd : DiffContOnCl ℂ f (HadamardThreeLines.verticalStrip l u))
    (hB : BddAbove
      ((norm ∘ f) '' HadamardThreeLines.verticalClosedStrip l u))
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : ∀ w ∈ re ⁻¹' {l}, ‖f w‖ ≤ a)
    (hb : ∀ w ∈ re ⁻¹' {u}, ‖f w‖ ≤ b) :
    ‖f z‖ ^ 2 ≤
      (a ^ 2) ^ (1 - (z.re - l) / (u - l)) *
        (b ^ 2) ^ ((z.re - l) / (u - l)) :=
  norm_sq_le_interp_of_mem_verticalClosedStrip'
    hul hz hd hB ha0 hb0 ha hb

#print axioms norm_sq_le_interp_of_mem_verticalClosedStrip'

end MathlibAux
