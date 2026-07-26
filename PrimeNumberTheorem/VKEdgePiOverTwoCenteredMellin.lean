import PrimeNumberTheorem.VKEdgePiOverTwoConcreteContourAssembly

open Complex MeasureTheory Polynomial Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The polynomial-Gaussian multiplier with logarithmic center `q * m`. -/
def localizedGaussianWeightAtCenter
    (q : ℝ) (A : ℂ[X]) (w : ℂ) (m : ℝ) (z : ℂ) : ℂ :=
  A.eval (z - w) *
    Complex.exp
      ((m : ℂ) * (z - w) ^ 2 +
        ((q * m : ℝ) : ℂ) * (z - w))

/-- The Chebyshev-error Gaussian average with inverse kernel centered at
`q * m`. -/
def localizedPsiGaussianAverageAtCenter
    (q : ℝ) (A : ℂ[X]) (w : ℂ) (m : ℝ) : ℂ :=
  ∫ x in Set.Ioi (1 : ℝ),
    psiErrorAboveOneComplex x *
      ((2 * Real.pi : ℂ) *
        ((x : ℂ) ^ (-(w + 1)) *
          (w * polynomialGaussianKernel A m
              (q * m - Real.log x) +
            polynomialGaussianKernelDeriv A m
              (q * m - Real.log x))))

/-- The centered weight specializes to the original center at `q = 16`. -/
@[simp] theorem localizedGaussianWeightAtCenter_sixteen
    (A : ℂ[X]) (w : ℂ) (m : ℝ) :
    localizedGaussianWeightAtCenter 16 A w m =
      localizedGaussianWeight A w m := by
  rfl

/-- The centered Chebyshev average specializes to the original center at
`q = 16`. -/
@[simp] theorem localizedPsiGaussianAverageAtCenter_sixteen
    (A : ℂ[X]) (w : ℂ) (m : ℝ) :
    localizedPsiGaussianAverageAtCenter 16 A w m =
      localizedPsiGaussianAverage A w m := by
  rfl

/-- For fixed `x > 0`, the centered right-edge Gaussian transform is the
inverse polynomial-Gaussian kernel evaluated at `q * m - log x`. -/
theorem integral_rightEdgePolynomialGaussian_cpow_atCenter_eq
    (q : ℝ) (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    (w : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ,
        (w + ((2 : ℂ) + I * (t : ℂ))) *
          A.eval ((2 : ℂ) + I * (t : ℂ)) *
          Complex.exp
            ((m : ℂ) * ((2 : ℂ) + I * (t : ℂ)) ^ 2 +
              ((q * m : ℝ) : ℂ) *
                ((2 : ℂ) + I * (t : ℂ))) *
          (x : ℂ) ^
            (-((w + ((2 : ℂ) + I * (t : ℂ))) + 1))) =
      (2 * Real.pi : ℂ) *
        ((x : ℂ) ^ (-(w + 1)) *
          (w * polynomialGaussianKernel A m
              (q * m - Real.log x) +
            polynomialGaussianKernelDeriv A m
              (q * m - Real.log x))) := by
  let z : ℝ → ℂ := fun t => (2 : ℂ) + I * (t : ℂ)
  let r : ℝ := q * m - Real.log x
  have hintegrand :
      (fun t : ℝ =>
        (w + z t) * A.eval (z t) *
          Complex.exp
            ((m : ℂ) * (z t) ^ 2 +
              ((q * m : ℝ) : ℂ) * z t) *
          (x : ℂ) ^ (-((w + z t) + 1))) =
        fun t : ℝ =>
          (x : ℂ) ^ (-(w + 1)) *
            ((w + z t) * A.eval (z t) *
              Complex.exp
                ((m : ℂ) * (z t) ^ 2 +
                  (r : ℂ) * z t)) := by
    funext t
    rw [ofReal_cpow_neg_add_split hx w (z t)]
    calc
      (w + z t) * A.eval (z t) *
            Complex.exp
              ((m : ℂ) * (z t) ^ 2 +
                ((q * m : ℝ) : ℂ) * z t) *
            ((x : ℂ) ^ (-(w + 1)) *
              Complex.exp (-((Real.log x : ℝ) : ℂ) * z t)) =
          (x : ℂ) ^ (-(w + 1)) *
            ((w + z t) * A.eval (z t) *
              (Complex.exp
                  ((m : ℂ) * (z t) ^ 2 +
                    ((q * m : ℝ) : ℂ) * z t) *
                Complex.exp
                  (-((Real.log x : ℝ) : ℂ) * z t))) := by
        ring
      _ =
          (x : ℂ) ^ (-(w + 1)) *
            ((w + z t) * A.eval (z t) *
              Complex.exp
                ((m : ℂ) * (z t) ^ 2 +
                  (r : ℂ) * z t)) := by
        rw [← Complex.exp_add]
        dsimp [r]
        congr 1
        push_cast
        ring
  have hinner :
      (∫ t : ℝ,
          (w + z t) * A.eval (z t) *
            Complex.exp
              ((m : ℂ) * (z t) ^ 2 +
                (r : ℂ) * z t)) =
        (2 * Real.pi : ℂ) *
          (w * polynomialGaussianKernel A m r +
            polynomialGaussianKernelDeriv A m r) := by
    simpa [z] using
      integral_verticalPolynomialGaussian_add_mul_eq
        A hm w 2 r
  change
    (∫ t : ℝ,
        (w + z t) * A.eval (z t) *
          Complex.exp
            ((m : ℂ) * (z t) ^ 2 +
              ((q * m : ℝ) : ℂ) * z t) *
          (x : ℂ) ^ (-((w + z t) + 1))) = _
  rw [hintegrand]
  calc
    (∫ t : ℝ,
        (x : ℂ) ^ (-(w + 1)) *
          ((w + z t) * A.eval (z t) *
            Complex.exp
              ((m : ℂ) * (z t) ^ 2 +
                (r : ℂ) * z t))) =
        (x : ℂ) ^ (-(w + 1)) *
          (∫ t : ℝ,
            (w + z t) * A.eval (z t) *
              Complex.exp
                ((m : ℂ) * (z t) ^ 2 +
                  (r : ℂ) * z t)) :=
      integral_const_mul _ _
    _ =
        (x : ℂ) ^ (-(w + 1)) *
          ((2 * Real.pi : ℂ) *
            (w * polynomialGaussianKernel A m r +
              polynomialGaussianKernelDeriv A m r)) := by
      exact congrArg ((x : ℂ) ^ (-(w + 1)) * ·) hinner
    _ = _ := by
      dsimp [r]
      ring

private def rightEdgeGaussianFactorAtCenter
    (q : ℝ) (A : ℂ[X]) (m : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  (w + ((2 : ℂ) + I * (t : ℂ))) *
    A.eval ((2 : ℂ) + I * (t : ℂ)) *
    Complex.exp
      ((m : ℂ) * ((2 : ℂ) + I * (t : ℂ)) ^ 2 +
        ((q * m : ℝ) : ℂ) *
          ((2 : ℂ) + I * (t : ℂ)))

private theorem rightEdgeGaussianFactorAtCenter_eq_weight_mul
    (q : ℝ) (A : ℂ[X]) (m : ℝ) (w : ℂ) (t : ℝ) :
    rightEdgeGaussianFactorAtCenter q A m w t =
      localizedGaussianWeightAtCenter q A w m
          (w + ((2 : ℂ) + I * (t : ℂ))) *
        (w + ((2 : ℂ) + I * (t : ℂ))) := by
  unfold rightEdgeGaussianFactorAtCenter localizedGaussianWeightAtCenter
  ring_nf

private theorem weightAtCenter_mul_regularizedLogDeriv_rightEdge_eq_factor
    (q : ℝ) (A : ℂ[X]) {w : ℂ} (hw : 0 < w.re)
    (m t : ℝ) :
    localizedGaussianWeightAtCenter q A w m
        (w + ((2 : ℂ) + I * (t : ℂ))) *
        (-logDeriv riemannZeta
            (w + ((2 : ℂ) + I * (t : ℂ))) -
          (w + ((2 : ℂ) + I * (t : ℂ))) /
            (w + ((2 : ℂ) + I * (t : ℂ)) - 1)) =
      rightEdgeGaussianFactorAtCenter q A m w t *
        mellin psiErrorAboveOneComplex
          (-(w + ((2 : ℂ) + I * (t : ℂ)))) := by
  rw [neg_logDeriv_sub_pole_rightEdge_eq_mul_mellin hw t]
  rw [rightEdgeGaussianFactorAtCenter_eq_weight_mul]
  ring

private def rightEdgeMellinProductAtCenter
    (q : ℝ) (A : ℂ[X]) (m : ℝ) (w : ℂ)
    (p : ℝ × ℝ) : ℂ :=
  rightEdgeGaussianFactorAtCenter q A m w p.1 *
    psiErrorAboveOneComplex p.2 *
    Complex.exp
      (((Real.log p.2 : ℝ) : ℂ) *
        (-(w + ((2 : ℂ) + I * (p.1 : ℂ)) + 1)))

private theorem integrable_rightEdgeMellinProductAtCenter
    (q : ℝ) (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    {w : ℂ} (hw : 0 < w.re) :
    Integrable
      (rightEdgeMellinProductAtCenter q A m w)
      (volume.prod (volume.restrict (Set.Ioi (1 : ℝ)))) := by
  let s0 : ℂ := ((w.re + 2 : ℝ) : ℂ)
  let P : ℝ → ℂ := rightEdgeGaussianFactorAtCenter q A m w
  let Q : ℝ → ℂ := fun x =>
    psiErrorAboveOneComplex x *
      Complex.exp
        (((Real.log x : ℝ) : ℂ) * (-(s0 + 1)))
  have hP : Integrable P := by
    dsimp [P, rightEdgeGaussianFactorAtCenter]
    convert
      integrable_verticalPolynomialGaussian_add_mul
        A hm w 2 (q * m) using 1
  have hs0 : 1 < s0.re := by
    dsimp [s0]
    linarith
  have hQcpow :=
    integrableOn_psiErrorAboveOneComplex_mul_cpow hs0
  have hQ :
      Integrable Q (volume.restrict (Set.Ioi (1 : ℝ))) := by
    refine hQcpow.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := zero_lt_one.trans hx
    dsimp [Q]
    rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr hxpos.ne')]
    rw [Complex.ofReal_log hxpos.le]
  have hproductMeasurable :
      AEStronglyMeasurable
        (rightEdgeMellinProductAtCenter q A m w)
        (volume.prod (volume.restrict (Set.Ioi (1 : ℝ)))) := by
    have hPsi :
        AEStronglyMeasurable psiErrorAboveOneComplex
          (volume.restrict (Set.Ioi (1 : ℝ))) := by
      exact
        locallyIntegrableOn_psiErrorAboveOneComplex.aestronglyMeasurable.mono_measure
          (Measure.restrict_mono
            (Set.Ioi_subset_Ioi
              (show (0 : ℝ) ≤ 1 by norm_num))
            le_rfl)
    have hphase :
        AEStronglyMeasurable
          (fun p : ℝ × ℝ =>
            Complex.exp
              (((Real.log p.2 : ℝ) : ℂ) *
                (-(w + ((2 : ℂ) + I * (p.1 : ℂ)) + 1))))
          (volume.prod (volume.restrict (Set.Ioi (1 : ℝ)))) := by
      exact (by fun_prop : Measurable
        (fun p : ℝ × ℝ =>
          Complex.exp
            (((Real.log p.2 : ℝ) : ℂ) *
              (-(w + ((2 : ℂ) + I * (p.1 : ℂ)) + 1))))).aestronglyMeasurable
    exact
      ((hP.aestronglyMeasurable.comp_fst.mul hPsi.comp_snd).mul
        hphase)
  have hdom :
      Integrable
        (fun p : ℝ × ℝ => ‖P p.1‖ * ‖Q p.2‖)
        (volume.prod (volume.restrict (Set.Ioi (1 : ℝ)))) :=
    hP.norm.mul_prod hQ.norm
  refine hdom.mono' hproductMeasurable ?_
  filter_upwards with p
  dsimp [rightEdgeMellinProductAtCenter, P, Q]
  simp only [norm_mul]
  rw [Complex.norm_exp, Complex.norm_exp]
  dsimp [s0]
  norm_num [Complex.mul_re, Complex.add_re]
  rw [mul_assoc]

private theorem integral_rightEdgeGaussianFactorAtCenter_exp_eq
    (q : ℝ) (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    (w : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ,
        rightEdgeGaussianFactorAtCenter q A m w t *
          Complex.exp
            (((Real.log x : ℝ) : ℂ) *
              (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1)))) =
      (2 * Real.pi : ℂ) *
        ((x : ℂ) ^ (-(w + 1)) *
          (w * polynomialGaussianKernel A m
              (q * m - Real.log x) +
            polynomialGaussianKernelDeriv A m
              (q * m - Real.log x))) := by
  calc
    (∫ t : ℝ,
        rightEdgeGaussianFactorAtCenter q A m w t *
          Complex.exp
            (((Real.log x : ℝ) : ℂ) *
              (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1)))) =
        ∫ t : ℝ,
          rightEdgeGaussianFactorAtCenter q A m w t *
            (x : ℂ) ^
              (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1)) := by
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      rw [Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr hx.ne')]
      rw [Complex.ofReal_log hx.le]
    _ = _ := by
      simpa [rightEdgeGaussianFactorAtCenter] using
        integral_rightEdgePolynomialGaussian_cpow_atCenter_eq
          q A hm w hx

private theorem integral_rightEdgeMellinProductAtCenter_snd_eq
    (q : ℝ) (A : ℂ[X]) (m : ℝ) {w : ℂ} (t : ℝ) :
    (∫ x in Set.Ioi (1 : ℝ),
        rightEdgeMellinProductAtCenter q A m w (t, x)) =
      rightEdgeGaussianFactorAtCenter q A m w t *
        mellin psiErrorAboveOneComplex
          (-(w + ((2 : ℂ) + I * (t : ℂ)))) := by
  rw [mellin_psiErrorAboveOneComplex_neg_eq_integral]
  rw [show
      (fun x : ℝ =>
        rightEdgeMellinProductAtCenter q A m w (t, x)) =
        fun x : ℝ =>
          rightEdgeGaussianFactorAtCenter q A m w t *
            (psiErrorAboveOneComplex x *
              Complex.exp
                (((Real.log x : ℝ) : ℂ) *
                  (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1)))) by
    funext x
    unfold rightEdgeMellinProductAtCenter
    ring]
  calc
    (∫ x in Set.Ioi (1 : ℝ),
        rightEdgeGaussianFactorAtCenter q A m w t *
          (psiErrorAboveOneComplex x *
            Complex.exp
              (((Real.log x : ℝ) : ℂ) *
                (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1))))) =
        rightEdgeGaussianFactorAtCenter q A m w t *
          (∫ x in Set.Ioi (1 : ℝ),
            psiErrorAboveOneComplex x *
              Complex.exp
                (((Real.log x : ℝ) : ℂ) *
                  (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1)))) :=
      integral_const_mul _ _
    _ = rightEdgeGaussianFactorAtCenter q A m w t *
          (∫ x in Set.Ioi (1 : ℝ),
            ((chebyshevPsi x - x : ℝ) : ℂ) *
              (x : ℂ) ^
                (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1))) := by
      congr 1
      apply integral_congr_ae
      refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro x hx
      have hxpos : 0 < x := zero_lt_one.trans hx
      have hxone : (1 : ℝ) ≤ x := le_of_lt hx
      change
        psiErrorAboveOneComplex x *
            Complex.exp
              (((Real.log x : ℝ) : ℂ) *
                (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1))) =
          ((chebyshevPsi x - x : ℝ) : ℂ) *
            (x : ℂ) ^
              (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1))
      rw [Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr hxpos.ne')]
      rw [Complex.ofReal_log hxpos.le]
      simp [psiErrorAboveOneComplex, psiErrorAboveOne, hxone]

private theorem integral_rightEdgeMellinProductAtCenter_fst_eq
    (q : ℝ) (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    (w : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ,
        rightEdgeMellinProductAtCenter q A m w (t, x)) =
      psiErrorAboveOneComplex x *
        ((2 * Real.pi : ℂ) *
          ((x : ℂ) ^ (-(w + 1)) *
            (w * polynomialGaussianKernel A m
                (q * m - Real.log x) +
              polynomialGaussianKernelDeriv A m
                (q * m - Real.log x)))) := by
  rw [show
      (fun t : ℝ =>
        rightEdgeMellinProductAtCenter q A m w (t, x)) =
        fun t : ℝ =>
          psiErrorAboveOneComplex x *
            (rightEdgeGaussianFactorAtCenter q A m w t *
              Complex.exp
                (((Real.log x : ℝ) : ℂ) *
                  (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1)))) by
    funext t
    unfold rightEdgeMellinProductAtCenter
    ring]
  calc
    (∫ t : ℝ,
        psiErrorAboveOneComplex x *
          (rightEdgeGaussianFactorAtCenter q A m w t *
            Complex.exp
              (((Real.log x : ℝ) : ℂ) *
                (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1))))) =
        psiErrorAboveOneComplex x *
          (∫ t : ℝ,
            rightEdgeGaussianFactorAtCenter q A m w t *
              Complex.exp
                (((Real.log x : ℝ) : ℂ) *
                  (-(w + ((2 : ℂ) + I * (t : ℂ)) + 1)))) :=
      integral_const_mul _ _
    _ = _ := by
      rw [integral_rightEdgeGaussianFactorAtCenter_exp_eq
        q A hm w hx]

/-- The centered Chebyshev-error Mellin integrand is integrable on the
right-edge domain. -/
theorem integrableOn_localizedPsiGaussianAverageAtCenter_integrand
    (q : ℝ) (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn
      (fun x : ℝ =>
        psiErrorAboveOneComplex x *
          ((2 * Real.pi : ℂ) *
            ((x : ℂ) ^ (-(w + 1)) *
              (w * polynomialGaussianKernel A m
                  (q * m - Real.log x) +
                polynomialGaussianKernelDeriv A m
                  (q * m - Real.log x)))))
      (Set.Ioi 1) := by
  have hsections :
      Integrable
        (fun x : ℝ =>
          ∫ t : ℝ, rightEdgeMellinProductAtCenter q A m w (t, x))
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
    (integrable_rightEdgeMellinProductAtCenter q A hm hw).integral_prod_right
  change IntegrableOn
    (fun x : ℝ =>
      ∫ t : ℝ, rightEdgeMellinProductAtCenter q A m w (t, x))
    (Set.Ioi (1 : ℝ)) at hsections
  refine hsections.congr_fun ?_ measurableSet_Ioi
  intro x hx
  exact integral_rightEdgeMellinProductAtCenter_fst_eq
    q A hm w (zero_lt_one.trans hx)

private theorem integral_rightEdgeGaussianFactorAtCenter_mul_mellin_eq
    (q : ℝ) (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    {w : ℂ} (hw : 0 < w.re) :
    (∫ t : ℝ,
        rightEdgeGaussianFactorAtCenter q A m w t *
          mellin psiErrorAboveOneComplex
            (-(w + ((2 : ℂ) + I * (t : ℂ))))) =
      localizedPsiGaussianAverageAtCenter q A w m := by
  have hproduct :=
    integrable_rightEdgeMellinProductAtCenter q A hm hw
  calc
    (∫ t : ℝ,
        rightEdgeGaussianFactorAtCenter q A m w t *
          mellin psiErrorAboveOneComplex
            (-(w + ((2 : ℂ) + I * (t : ℂ))))) =
        ∫ t : ℝ, ∫ x in Set.Ioi (1 : ℝ),
          rightEdgeMellinProductAtCenter q A m w (t, x) := by
      apply integral_congr_ae
      filter_upwards with t
      exact (integral_rightEdgeMellinProductAtCenter_snd_eq
        q A m t).symm
    _ =
        ∫ x in Set.Ioi (1 : ℝ), ∫ t : ℝ,
          rightEdgeMellinProductAtCenter q A m w (t, x) := by
      exact integral_integral_swap hproduct
    _ = localizedPsiGaussianAverageAtCenter q A w m := by
      unfold localizedPsiGaussianAverageAtCenter
      apply integral_congr_ae
      refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro x hx
      exact integral_rightEdgeMellinProductAtCenter_fst_eq
        q A hm w (zero_lt_one.trans hx)

/-- The centered infinite right-edge regularized zeta integral equals the
centered Chebyshev-error Gaussian average. -/
theorem integral_localizedGaussianWeightAtCenter_mul_regularizedLogDeriv_rightEdge_eq
    (q : ℝ) (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    {w : ℂ} (hw : 0 < w.re) :
    (∫ t : ℝ,
        localizedGaussianWeightAtCenter q A w m
            (w + ((2 : ℂ) + I * (t : ℂ))) *
          (-logDeriv riemannZeta
              (w + ((2 : ℂ) + I * (t : ℂ))) -
            (w + ((2 : ℂ) + I * (t : ℂ))) /
              (w + ((2 : ℂ) + I * (t : ℂ)) - 1))) =
      localizedPsiGaussianAverageAtCenter q A w m := by
  calc
    (∫ t : ℝ,
        localizedGaussianWeightAtCenter q A w m
            (w + ((2 : ℂ) + I * (t : ℂ))) *
          (-logDeriv riemannZeta
              (w + ((2 : ℂ) + I * (t : ℂ))) -
            (w + ((2 : ℂ) + I * (t : ℂ))) /
              (w + ((2 : ℂ) + I * (t : ℂ)) - 1))) =
        ∫ t : ℝ,
          rightEdgeGaussianFactorAtCenter q A m w t *
            mellin psiErrorAboveOneComplex
              (-(w + ((2 : ℂ) + I * (t : ℂ)))) := by
      apply integral_congr_ae
      filter_upwards with t
      exact
        weightAtCenter_mul_regularizedLogDeriv_rightEdge_eq_factor
          q A hw m t
    _ = localizedPsiGaussianAverageAtCenter q A w m :=
      integral_rightEdgeGaussianFactorAtCenter_mul_mellin_eq
        q A hm hw

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
