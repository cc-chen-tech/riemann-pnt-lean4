import MathlibAux.MellinVerticalStripBound

open Complex

#check MathlibAux.mellinEndpointMajorant

#check (@MathlibAux.exists_norm_mellin_le_on_reIcc :
  ∀ {f : ℝ → ℂ} {a b : ℝ},
    MellinConvergent f (a : ℂ) →
    MellinConvergent f (b : ℂ) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
        a ≤ s.re → s.re ≤ b → ‖mellin f s‖ ≤ C)
