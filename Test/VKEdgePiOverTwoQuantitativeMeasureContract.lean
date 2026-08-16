import PrimeNumberTheorem.VKEdgePiOverTwoQuantitativeMeasure

open Complex Filter MeasureTheory Set

open PrimeNumberTheorem.VKEdgePiOverTwo

example
    {alpha : Type*} [MeasurableSpace alpha] {mu : Measure alpha}
    {s : Set alpha} {f w : alpha -> Real} {C B : Real}
    (hs : MeasurableSet s) (hmus : mu s ≠ ⊤)
    (hf : Measurable f)
    (hwNonneg : ∀ x, 0 ≤ w x)
    (hweighted : IntegrableOn (fun x => f x ^ 2 * w x) s mu)
    (hweight : IntegrableOn w s mu)
    (hC : 0 ≤ C)
    (hbound : ∀ x ∈ s, f x ^ 2 * w x ≤ B) :
    (∫ x in s, f x ^ 2 * w x ∂mu) -
          C ^ 2 * ∫ x in s, w x ∂mu ≤
        B * mu.real {x ∈ s | C < |f x|} :=
  MathlibAux.weightedSecondMoment_sub_thresholdMass_le_envelope_mul_measure
    hs hmus hf hwNonneg hweighted hweight hC hbound

example
    {q d : Real} {rho : Complex} {multiplicity mean C : Real}
    (data : CenteredLocalizedContourData q d rho multiplicity mean)
    (hmultiplicity : 0 < multiplicity) (hmean : 0 < mean)
    (hC0 : 0 ≤ C) (hC : C < multiplicity / mean) :
    ∀ᶠ m : Real in atTop,
      centeredThresholdEnergyGap multiplicity mean C / 2 <
        centeredNormalizedWindowSecondMoment q d rho data.kernel m -
          C ^ 2 * data.coefficient m :=
  data.eventually_secondMoment_sub_thresholdMass_gt_half_gap
    hmultiplicity hmean hC0 hC

example
    {q d : Real} {rho : Complex} {k : Nat}
    (hq : 16 ≤ q) (hd : 0 < d) (hdq : d < q)
    (hmargin : 16 * (q + d) ≤ d ^ 2)
    (hrhoRe0 : 0 < rho.re) (hrhoRe1 : rho.re < 1)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hmissing :
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0) :
    ∀ᶠ m : Real in atTop,
      centeredStrictPiOverTwoMeasureLowerBound q d rho k m <
        volume.real
          {y ∈ localizedGaussianLogWindow q d m |
            (analyticOrderNatAt riemannZeta rho : Real) *
                  strictPiOverTwoOscillationConstant k <
              |normalizedPsiError rho y|} :=
  eventually_centeredSharpened_measure_gt_explicit_strictPiOverTwo
    hq hd hdq hmargin hrhoRe0 hrhoRe1 hgamma hzero hmissing

example
    {epsilon : Real} {rho : Complex} {sigma : Real}
    (hepsilon : 0 < epsilon)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hsigma : 1 / 2 < sigma)
    (hsigmaRho : sigma < rho.re)
    (hrhoRe1 : rho.re < 1) :
    exists k : Nat,
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
      Real.pi / 2 < strictPiOverTwoOscillationConstant k ∧
      ∀ᶠ Y : Real in atTop,
        0 < centeredStrictPiOverTwoMeasureLowerBound
              (epsilonCenterCoefficient epsilon)
              (epsilonRadiusCoefficient epsilon) rho k
              (epsilonGaussianScale epsilon Y) ∧
          centeredStrictPiOverTwoMeasureLowerBound
                (epsilonCenterCoefficient epsilon)
                (epsilonRadiusCoefficient epsilon) rho k
                (epsilonGaussianScale epsilon Y) <
            volume.real
              {y ∈ Set.Icc (Real.log Y) ((1 + epsilon) * Real.log Y) |
                (analyticOrderNatAt riemannZeta rho : Real) *
                      strictPiOverTwoOscillationConstant k <
                  |normalizedPsiError rho y|} :=
  exists_eventually_explicit_measure_in_epsilonLogWindow_gt_strictPiOverTwo
    hepsilon hgamma hzero hsigma hsigmaRho hrhoRe1
