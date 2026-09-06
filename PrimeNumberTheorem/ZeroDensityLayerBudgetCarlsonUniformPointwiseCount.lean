import PrimeNumberTheorem.CarlsonAsymptotic

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Carlson's contour argument with its quantifiers exposed in the order needed
for a moving boundary: one choice of ambient constants works pointwise for every
`sigma` and `T` satisfying the explicit parameter conditions. -/
theorem exists_carlson_uniform_pointwise_count_certificate :
    ∃ A C₁ C₂ : ℝ, 0 ≤ A ∧ 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ∀ {sigma T : ℝ},
        1 / 2 < sigma → sigma < 1 → 6 ≤ T →
        1 ≤ Real.log T →
        4 / Real.log T < sigma - 1 / 2 →
        1 ≤ T ^ (2 * sigma - 1) →
        C₁ ≤ T → C₂ ≤ T →
        (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
          (125 * carlsonFinalCoefficient A sigma) *
            (T ^ (4 * sigma * (1 - sigma)) * (Real.log T) ^ 4) := by
  obtain ⟨A, C₁, C₂, hA, hC₁, hC₂, hcertificate⟩ :=
    exists_carlson_parameterized_count_certificate
  refine ⟨A, C₁, C₂, hA, hC₁, hC₂, ?_⟩
  intro sigma T hσ hσ1 hT hlog hlarge hpower hC₁T hC₂T
  let K := carlsonFinalCoefficient A sigma
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact zero_le_carlsonFinalCoefficient hA hσ hσ1
  have hlogPos : 0 < Real.log T := zero_lt_one.trans_le hlog
  have hwindow : 2 / Real.log T < sigma - 1 / 2 :=
    (div_lt_div_of_pos_right (by norm_num : (2 : ℝ) < 4) hlogPos).trans hlarge
  rcases hcertificate hσ hσ1 hT hlogPos hwindow with
    ⟨x0, y0, y1, n,
      hgapLower, hgapUpper, hx0Half, hx0Sigma, hx04,
      hy0Lower, _hy0Upper, _hTy1, hy1Upper, _hy01,
      hnv, hvn, hcount⟩
  have hx0One : x0 < 1 := hx0Sigma.trans hσ1
  have hTOne : 1 ≤ T := by linarith
  have hXT : (carlsonMollifierLength sigma T : ℝ) ≤ T :=
    carlsonMollifierLength_le_height hσ hσ1 hTOne hpower
  have hgeom := carlson_parameterized_geometric_cover_optimized_le (A := A)
    hσ hσ1 hT hlogPos hlarge hpower hx0Half hx0One hx0Sigma hgapUpper
      (by linarith) hnv hvn hy1Upper
  have hbottom := regularizedCarlsonHorizontalLogDerivMajorant_le_ambientCube
    hC₁ hC₁T hC₂ hC₂T (one_le_carlsonMollifierLength sigma T) hXT hT
      (by norm_num : (0 : ℝ) ≤ 5) (by linarith)
  have htop := regularizedCarlsonHorizontalLogDerivMajorant_le_ambientCube
    hC₁ hC₁T hC₂ hC₂T (one_le_carlsonMollifierLength sigma T) hXT hT
      (by linarith : 0 ≤ T + 1 / 4) (by linarith)
  have hLone := one_le_carlsonAmbientLogCube hT
  have hL0 : 0 ≤ carlsonAmbientLogCube T := zero_le_one.trans hLone
  have hPone := one_le_carlson_target_rpow hσ hσ1 hT
  have hP0 : 0 ≤ T ^ (4 * sigma * (1 - sigma)) :=
    zero_le_one.trans hPone
  have hLPone :
      1 ≤ carlsonAmbientLogCube T * T ^ (4 * sigma * (1 - sigma)) := by
    nlinarith [mul_nonneg hL0 hP0]
  have hgapTwo : sigma - x0 ≤ 2 := by
    have htwoDiv : 2 / Real.log T ≤ 2 := by
      rw [div_le_iff₀ hlogPos]
      nlinarith
    exact hgapUpper.le.trans htwoDiv
  have hglobal0 :
      0 ≤ ExplicitFormulaAux.globalZeroMultiplicity 6 :=
    ExplicitFormulaAux.globalZeroMultiplicity_nonneg 6
  have hlow :
      (2 * Real.pi) * (sigma - x0) *
          ExplicitFormulaAux.globalZeroMultiplicity 6 ≤
        (4 * Real.pi * ExplicitFormulaAux.globalZeroMultiplicity 6) *
          (carlsonAmbientLogCube T *
            T ^ (4 * sigma * (1 - sigma))) := by
    have hfirst :
        (2 * Real.pi) * (sigma - x0) *
            ExplicitFormulaAux.globalZeroMultiplicity 6 ≤
          4 * Real.pi * ExplicitFormulaAux.globalZeroMultiplicity 6 := by
      have hpi : (2 * Real.pi) * (sigma - x0) ≤ 4 * Real.pi := by
        nlinarith [Real.pi_pos]
      exact mul_le_mul_of_nonneg_right hpi hglobal0
    have hcoefficient0 :
        0 ≤ 4 * Real.pi * ExplicitFormulaAux.globalZeroMultiplicity 6 := by
      positivity
    exact hfirst.trans (by
      calc
        _ = (4 * Real.pi * ExplicitFormulaAux.globalZeroMultiplicity 6) * 1 :=
          by ring
        _ ≤ (4 * Real.pi * ExplicitFormulaAux.globalZeroMultiplicity 6) *
            (carlsonAmbientLogCube T *
              T ^ (4 * sigma * (1 - sigma))) :=
          mul_le_mul_of_nonneg_left hLPone hcoefficient0)
  have hsquare : (4 - x0) ^ 2 ≤ 16 := by
    have hfour0 : 0 ≤ 4 - x0 := sub_nonneg.mpr hx04.le
    have hfour : 4 - x0 ≤ 4 := by linarith [hx0Half]
    convert pow_le_pow_left₀ hfour0 hfour 2 using 1 <;> (try rfl) <;> norm_num
  have hhorizontalSum :
      regularizedCarlsonHorizontalLogDerivMajorant
            C₁ C₂ (carlsonMollifierLength sigma T) 5 +
          regularizedCarlsonHorizontalLogDerivMajorant
            C₁ C₂ (carlsonMollifierLength sigma T) (T + 1 / 4) ≤
        2 * carlsonHorizontalMajorantCoefficient *
          carlsonAmbientLogCube T := by
    linarith
  have hhorizontal :
      (4 - x0) ^ 2 *
          (regularizedCarlsonHorizontalLogDerivMajorant
              C₁ C₂ (carlsonMollifierLength sigma T) 5 +
            regularizedCarlsonHorizontalLogDerivMajorant
              C₁ C₂ (carlsonMollifierLength sigma T) (T + 1 / 4)) ≤
        (32 * carlsonHorizontalMajorantCoefficient) *
          (carlsonAmbientLogCube T *
            T ^ (4 * sigma * (1 - sigma))) := by
    have hH0 := zero_le_carlsonHorizontalMajorantCoefficient
    by_cases hsum0 : 0 ≤
        regularizedCarlsonHorizontalLogDerivMajorant
              C₁ C₂ (carlsonMollifierLength sigma T) 5 +
            regularizedCarlsonHorizontalLogDerivMajorant
              C₁ C₂ (carlsonMollifierLength sigma T) (T + 1 / 4)
    · have hfirst := mul_le_mul hsquare hhorizontalSum hsum0
          (by norm_num : (0 : ℝ) ≤ 16)
      have hscale0 : 0 ≤ 32 * carlsonHorizontalMajorantCoefficient *
          carlsonAmbientLogCube T := by positivity
      calc
        _ ≤ 32 * carlsonHorizontalMajorantCoefficient *
              carlsonAmbientLogCube T := by
            convert hfirst using 1 <;> (try rfl) <;> ring
        _ ≤ (32 * carlsonHorizontalMajorantCoefficient) *
              (carlsonAmbientLogCube T *
                T ^ (4 * sigma * (1 - sigma))) := by
            calc
              _ = (32 * carlsonHorizontalMajorantCoefficient *
                  carlsonAmbientLogCube T) * 1 := by ring
              _ ≤ (32 * carlsonHorizontalMajorantCoefficient *
                  carlsonAmbientLogCube T) *
                    T ^ (4 * sigma * (1 - sigma)) :=
                mul_le_mul_of_nonneg_left hPone hscale0
              _ = _ := by ring
    · have hleftNonpos :
          (4 - x0) ^ 2 *
              (regularizedCarlsonHorizontalLogDerivMajorant
                  C₁ C₂ (carlsonMollifierLength sigma T) 5 +
                regularizedCarlsonHorizontalLogDerivMajorant
                  C₁ C₂ (carlsonMollifierLength sigma T) (T + 1 / 4)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_not_ge hsum0)
      exact hleftNonpos.trans (by positivity)
  have hboundary :
      (4 - x0) * (3 * Real.pi) + 125 / 18 ≤
        (12 * Real.pi + 125 / 18) *
          (carlsonAmbientLogCube T *
            T ^ (4 * sigma * (1 - sigma))) := by
    have hbasic :
        (4 - x0) * (3 * Real.pi) + 125 / 18 ≤
          12 * Real.pi + 125 / 18 := by
      have hfour : 4 - x0 ≤ 4 := by linarith [hx0Half]
      have hthreePi0 : 0 ≤ 3 * Real.pi := by positivity
      have hmul : (4 - x0) * (3 * Real.pi) ≤ 4 * (3 * Real.pi) :=
        mul_le_mul_of_nonneg_right hfour hthreePi0
      calc
        _ ≤ 4 * (3 * Real.pi) + 125 / 18 :=
          add_le_add hmul le_rfl
        _ = _ := by ring
    have hcoefficient0 : 0 ≤ 12 * Real.pi + 125 / 18 := by positivity
    exact hbasic.trans (by
      calc
        _ = (12 * Real.pi + 125 / 18) * 1 := by ring
        _ ≤ (12 * Real.pi + 125 / 18) *
            (carlsonAmbientLogCube T *
              T ^ (4 * sigma * (1 - sigma))) :=
          mul_le_mul_of_nonneg_left hLPone hcoefficient0)
  have hweighted :
      (2 * Real.pi) * (sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        K * (carlsonAmbientLogCube T *
          T ^ (4 * sigma * (1 - sigma))) := by
    have hgeom' :
        carlsonSharpGeometricCoverExplicitBound A
            (carlsonMollifierLength sigma T) x0 y0 y1 n ≤
          carlsonSharpAmbientCoefficient A sigma *
            (carlsonAmbientLogCube T *
              T ^ (4 * sigma * (1 - sigma))) := by
      simpa only [mul_assoc] using hgeom
    calc
      _ ≤ (2 * Real.pi) * (sigma - x0) *
              ExplicitFormulaAux.globalZeroMultiplicity 6 +
            carlsonSharpGeometricCoverExplicitBound A
              (carlsonMollifierLength sigma T) x0 y0 y1 n +
            (4 - x0) ^ 2 *
              (regularizedCarlsonHorizontalLogDerivMajorant
                  C₁ C₂ (carlsonMollifierLength sigma T) 5 +
                regularizedCarlsonHorizontalLogDerivMajorant
                  C₁ C₂ (carlsonMollifierLength sigma T) (T + 1 / 4)) +
            ((4 - x0) * (3 * Real.pi) + 125 / 18) := by
          convert hcount using 1 <;> ring
      _ ≤ (4 * Real.pi * ExplicitFormulaAux.globalZeroMultiplicity 6) *
              (carlsonAmbientLogCube T *
                T ^ (4 * sigma * (1 - sigma))) +
            (carlsonSharpAmbientCoefficient A sigma) *
              (carlsonAmbientLogCube T *
                T ^ (4 * sigma * (1 - sigma))) +
            (32 * carlsonHorizontalMajorantCoefficient) *
              (carlsonAmbientLogCube T *
                T ^ (4 * sigma * (1 - sigma))) +
            (12 * Real.pi + 125 / 18) *
              (carlsonAmbientLogCube T *
                T ^ (4 * sigma * (1 - sigma))) :=
          add_le_add (add_le_add (add_le_add hlow hgeom') hhorizontal) hboundary
      _ = K * (carlsonAmbientLogCube T *
            T ^ (4 * sigma * (1 - sigma))) := by
          dsimp [K, carlsonFinalCoefficient]
          ring
  have hN0 : 0 ≤ (ZeroDensity.zeroDensityCount sigma T : ℝ) :=
    Nat.cast_nonneg _
  have hgap0 : 0 ≤ sigma - x0 := sub_nonneg.mpr hx0Sigma.le
  have hgapN0 : 0 ≤ (sigma - x0) *
      (ZeroDensity.zeroDensityCount sigma T : ℝ) := mul_nonneg hgap0 hN0
  have hpiOne : 1 ≤ 2 * Real.pi := by
    nlinarith only [Real.pi_gt_three]
  have hgapCount :
      (sigma - x0) * (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        K * (carlsonAmbientLogCube T *
          T ^ (4 * sigma * (1 - sigma))) := by
    apply (show (sigma - x0) *
        (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
          (2 * Real.pi) * (sigma - x0) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ) by
      calc
        _ = 1 * ((sigma - x0) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) := by ring
        _ ≤ (2 * Real.pi) * ((sigma - x0) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) :=
          mul_le_mul_of_nonneg_right hpiOne hgapN0
        _ = _ := by ring).trans
    exact hweighted
  have hgapLog : 1 < (sigma - x0) * Real.log T :=
    (div_lt_iff₀ hlogPos).mp hgapLower
  have hcountScale :
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        Real.log T * ((sigma - x0) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ)) := by
    calc
      _ = 1 * (ZeroDensity.zeroDensityCount sigma T : ℝ) := by ring
      _ ≤ ((sigma - x0) * Real.log T) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) :=
        mul_le_mul_of_nonneg_right hgapLog.le hN0
      _ = _ := by ring
  have hambientCount :
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        K * carlsonAmbientLogCube T *
          T ^ (4 * sigma * (1 - sigma)) * Real.log T := by
    calc
      _ ≤ Real.log T * ((sigma - x0) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) := hcountScale
      _ ≤ Real.log T *
            (K * (carlsonAmbientLogCube T *
              T ^ (4 * sigma * (1 - sigma)))) :=
        mul_le_mul_of_nonneg_left hgapCount hlogPos.le
      _ = _ := by ring
  have hlogCube := carlsonAmbientLogCube_le_logCube hT hlog
  have hscale0 :
      0 ≤ K * T ^ (4 * sigma * (1 - sigma)) * Real.log T := by
    positivity
  calc
    _ ≤ K * carlsonAmbientLogCube T *
        T ^ (4 * sigma * (1 - sigma)) * Real.log T := hambientCount
    _ = carlsonAmbientLogCube T *
        (K * T ^ (4 * sigma * (1 - sigma)) * Real.log T) := by ring
    _ ≤ (125 * (Real.log T) ^ 3) *
        (K * T ^ (4 * sigma * (1 - sigma)) * Real.log T) :=
      mul_le_mul_of_nonneg_right hlogCube hscale0
    _ = (125 * K) *
        (T ^ (4 * sigma * (1 - sigma)) * (Real.log T) ^ 4) := by
      dsimp [K]
      ring

end CarlsonZeroDensity
end PrimeNumberTheorem
