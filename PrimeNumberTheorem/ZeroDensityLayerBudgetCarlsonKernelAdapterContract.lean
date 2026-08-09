import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonKernelAdapter

namespace PrimeNumberTheorem

example
    {ι : Type*} [DecidableEq ι]
    {layers : Finset ι} {height : ℝ → ℝ}
    {layerTerm : ι → ℝ → ℝ → ℝ}
    (adapter :
      CarlsonKernelMajorantLayerAdapter layers height layerTerm) :
    CarlsonKernelLayerFactorization layers height layerTerm :=
  adapter.toKernelDensityFactorization

example
    {ι : Type*} [DecidableEq ι]
    {layers : Finset ι}
    {error main remainder height : ℝ → ℝ}
    {layerTerm : ι → ℝ → ℝ → ℝ} {amplitude : ℝ}
    (hamplitude : 0 < amplitude)
    (hmain : HasFarNormWitness main amplitude)
    (remainderCertificate :
      DynamicLayerRemainderCertificate remainder height
        (finiteLayerBudget layers layerTerm))
    (adapter :
      CarlsonKernelMajorantLayerAdapter layers height layerTerm)
    (hdecomp : ∀ x, error x = main x + remainder x) :
    HasFarNormWitness error (amplitude / 2) :=
  hasFarNormWitness_add_of_carlsonMajorant
    hamplitude hmain remainderCertificate adapter hdecomp

end PrimeNumberTheorem
