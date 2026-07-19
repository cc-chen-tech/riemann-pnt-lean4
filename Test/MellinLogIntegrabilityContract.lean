import MathlibAux.MellinLogIntegrability

open Complex MeasureTheory

namespace MathlibAux

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (f : ℝ → E) (sigma : ℝ)
    (hf : MellinConvergent f (sigma : ℂ)) :
    Integrable (logMellinKernel f sigma) :=
  integrable_logMellinKernel_of_mellinConvergent f sigma hf

end MathlibAux

#print axioms MathlibAux.integrable_logMellinKernel_of_mellinConvergent
