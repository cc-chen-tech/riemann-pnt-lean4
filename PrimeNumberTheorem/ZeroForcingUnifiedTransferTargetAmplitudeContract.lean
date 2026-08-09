import PrimeNumberTheorem.ZeroForcingUnifiedTransfer

namespace PrimeNumberTheorem

/-! Public contract for the same-error upper/lower PNT transfer. -/

example
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {amplitude main realAxis contour complement : ℝ → ℝ}
    (hamplitude :
      Filter.Eventually (fun x => 0 < amplitude x) Filter.atTop)
    (hrealAxis : TargetAmplitudeNegligible amplitude realAxis)
    (hcontour : TargetAmplitudeNegligible amplitude contour)
    (hcomplement : TargetAmplitudeNegligible amplitude complement)
    (hmain : HasFarTargetAmplitudeWitness main amplitude)
    (hdecomp :
      ∀ x : ℝ,
        relativeChebyshevPsi0Error x =
          main x + (realAxis x + contour x + complement x)) :
    (∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Filter.Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        Filter.atTop (nhds 0)) ∧
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => amplitude x / 2) :=
  unified_parametricPNTUpper_targetAmplitudeLower
    threshold hhalf hlt hamplitude hrealAxis hcontour hcomplement hmain hdecomp

end PrimeNumberTheorem
