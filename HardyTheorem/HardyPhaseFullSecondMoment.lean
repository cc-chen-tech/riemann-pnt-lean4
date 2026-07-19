import HardyTheorem.HardyPhaseSecondMoment
import HardyTheorem.HardyPhaseHilbertShiftIntegral

open Complex MeasureTheory Set

namespace HardyTheorem

private noncomputable def fullSecondMomentClampedPhase
    (T : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (I * OscillatoryIntegral.hardyPhase n (max T x))

private theorem continuous_fullSecondMomentClampedPhase
    {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : n ≠ 0) :
    Continuous (fullSecondMomentClampedPhase T n) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hmax : 0 < max T x := hT.trans_le (le_max_left T x)
  have harg : ContinuousAt (fun y : ℝ => max T y) x :=
    (continuous_const.max continuous_id).continuousAt
  have hphase : ContinuousAt
      (fun y : ℝ => OscillatoryIntegral.hardyPhase n (max T y)) x :=
    (OscillatoryIntegral.contDiffAt_hardyPhase_two hn hmax).continuousAt.comp' harg
  exact (continuousAt_const.mul
    (Complex.continuous_ofReal.continuousAt.comp hphase)).cexp

private noncomputable def fullSecondMomentClampedShortIntegral
    (T : ℝ) (n : ℕ) (delta t : ℝ) : ℂ :=
  ∫ v in 0..delta, fullSecondMomentClampedPhase T n (t + v)

private theorem continuous_fullSecondMomentClampedShortIntegral
    {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : n ≠ 0) (delta : ℝ) :
    Continuous (fullSecondMomentClampedShortIntegral T n delta) := by
  unfold fullSecondMomentClampedShortIntegral
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (continuous_fullSecondMomentClampedPhase hT hn).comp
    (continuous_fst.add continuous_snd)

private theorem hardyPhaseShortIntegral_eq_fullSecondMomentClamped
    (n : ℕ) {T delta t : ℝ} (hdelta : 0 ≤ delta) (ht : T ≤ t) :
    OscillatoryIntegral.hardyPhaseShortIntegral n delta t =
      fullSecondMomentClampedShortIntegral T n delta t := by
  unfold OscillatoryIntegral.hardyPhaseShortIntegral
    fullSecondMomentClampedShortIntegral fullSecondMomentClampedPhase
  apply intervalIntegral.integral_congr
  intro v hv
  have hvIcc : v ∈ Icc (0 : ℝ) delta := by
    simpa [uIcc_of_le hdelta] using hv
  have hmax : T ≤ t + v := ht.trans (le_add_of_nonneg_right hvIcc.1)
  change Complex.exp (I * OscillatoryIntegral.hardyPhase n (t + v)) =
    Complex.exp (I * OscillatoryIntegral.hardyPhase n (max T (t + v)))
  rw [max_eq_right hmax]

private theorem intervalIntegrable_weighted_hardyPhaseCrossTerm
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (coeff : ℕ → ℂ) {T delta B : ℝ} (hT : 0 < T)
    (hdelta : 0 ≤ delta) (hTB : T ≤ B) :
    IntervalIntegrable
      (fun t : ℝ =>
        (starRingEnd ℂ)
            (coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
          (coeff m * OscillatoryIntegral.hardyPhaseShortIntegral m delta t))
      volume T B := by
  let g : ℝ → ℂ := fun t =>
    (starRingEnd ℂ)
        (coeff n * fullSecondMomentClampedShortIntegral T n delta t) *
      (coeff m * fullSecondMomentClampedShortIntegral T m delta t)
  have hg : IntervalIntegrable g volume T B := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.mul
      (continuous_fullSecondMomentClampedShortIntegral hT hn delta)).star.mul
        (continuous_const.mul
          (continuous_fullSecondMomentClampedShortIntegral hT hm delta))
  apply hg.congr
  intro t ht
  have htIcc : t ∈ Icc T B := by
    simpa [uIcc_of_le hTB] using (uIoc_subset_uIcc ht)
  dsimp only [g]
  rw [hardyPhaseShortIntegral_eq_fullSecondMomentClamped n hdelta htIcc.1,
    hardyPhaseShortIntegral_eq_fullSecondMomentClamped m hdelta htIcc.1]

private theorem integral_weighted_hardyPhaseCrossTerm_eq
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (coeff : ℕ → ℂ) {T delta : ℝ} (hT : 0 < T)
    (hdelta : 0 ≤ delta) (hroom : delta ≤ T) :
    (∫ t in T..2 * T - delta,
      (starRingEnd ℂ)
          (coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
        (coeff m * OscillatoryIntegral.hardyPhaseShortIntegral m delta t)) =
      (starRingEnd ℂ) (coeff n) * coeff m *
        ∫ v in 0..delta, ∫ w in 0..delta,
          ∫ t in T..2 * T - delta,
            Complex.exp (I *
              OscillatoryIntegral.hardyPhaseCorrelation m n w v t) := by
  simp only [map_mul]
  rw [show (fun t : ℝ =>
      ((starRingEnd ℂ) (coeff n) *
          (starRingEnd ℂ)
            (OscillatoryIntegral.hardyPhaseShortIntegral n delta t)) *
        (coeff m * OscillatoryIntegral.hardyPhaseShortIntegral m delta t)) =
      fun t : ℝ =>
        ((starRingEnd ℂ) (coeff n) * coeff m) *
          ((starRingEnd ℂ)
              (OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
            OscillatoryIntegral.hardyPhaseShortIntegral m delta t) by
    funext t
    ring]
  calc
    (∫ t in T..2 * T - delta,
        ((starRingEnd ℂ) (coeff n) * coeff m) *
          ((starRingEnd ℂ)
              (OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
            OscillatoryIntegral.hardyPhaseShortIntegral m delta t)) =
        ((starRingEnd ℂ) (coeff n) * coeff m) *
          ∫ t in T..2 * T - delta,
            (starRingEnd ℂ)
                (OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
              OscillatoryIntegral.hardyPhaseShortIntegral m delta t :=
      intervalIntegral.integral_const_mul _ _
    _ = _ := by
      rw [integral_conj_hardyPhaseShortIntegral_mul_eq_triple_correlation
        hm hn hT hdelta hroom]

private noncomputable def swappedHardyOffDiagonalTerm
    (m n : ℕ) (coeff : ℕ → ℂ) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  if m = n then 0
  else (starRingEnd ℂ) (coeff n) * coeff m *
    Complex.exp (I * OscillatoryIntegral.hardyPhaseCorrelation
      m n p.1.2 p.1.1 p.2)

private theorem continuousAt_swappedHardyOffDiagonalTerm
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (coeff : ℕ → ℂ)
    {p : (ℝ × ℝ) × ℝ}
    (htm : 0 < p.2 + p.1.2) (htn : 0 < p.2 + p.1.1) :
    ContinuousAt (swappedHardyOffDiagonalTerm m n coeff) p := by
  unfold swappedHardyOffDiagonalTerm
  by_cases hmn : m = n
  · simp only [hmn, ↓reduceIte]
    exact continuousAt_const
  · simp only [hmn, ↓reduceIte]
    have hmphase : ContinuousAt
        (fun q : (ℝ × ℝ) × ℝ =>
          OscillatoryIntegral.hardyPhase m (q.2 + q.1.2)) p := by
      change ContinuousAt
        (OscillatoryIntegral.hardyPhase m ∘
          fun q : (ℝ × ℝ) × ℝ => q.2 + q.1.2) p
      exact ContinuousAt.comp_of_eq
        (f := fun q : (ℝ × ℝ) × ℝ => q.2 + q.1.2)
        (OscillatoryIntegral.contDiffAt_hardyPhase_two hm htm).continuousAt
        (continuous_snd.add continuous_fst.snd).continuousAt rfl
    have hnphase : ContinuousAt
        (fun q : (ℝ × ℝ) × ℝ =>
          OscillatoryIntegral.hardyPhase n (q.2 + q.1.1)) p := by
      change ContinuousAt
        (OscillatoryIntegral.hardyPhase n ∘
          fun q : (ℝ × ℝ) × ℝ => q.2 + q.1.1) p
      exact ContinuousAt.comp_of_eq
        (f := fun q : (ℝ × ℝ) × ℝ => q.2 + q.1.1)
        (OscillatoryIntegral.contDiffAt_hardyPhase_two hn htn).continuousAt
        (continuous_snd.add continuous_fst.fst).continuousAt rfl
    unfold OscillatoryIntegral.hardyPhaseCorrelation
    exact (continuousAt_const.mul continuousAt_const).mul <|
      (continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp
          (hmphase.sub hnphase))).cexp

private theorem integrable_swappedHardyOffDiagonalTerm
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (coeff : ℕ → ℂ)
    {T delta : ℝ} (hT : 0 < T) :
    Integrable (swappedHardyOffDiagonalTerm m n coeff)
      (((volume.restrict (Set.Ioc 0 delta)).prod
          (volume.restrict (Set.Ioc 0 delta))).prod
        (volume.restrict (Set.Ioc T (2 * T - delta)))) := by
  let box : Set ((ℝ × ℝ) × ℝ) :=
    (Set.Icc 0 delta ×ˢ Set.Icc 0 delta) ×ˢ
      Set.Icc T (2 * T - delta)
  have hcompact : IsCompact box :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hcontinuous : ContinuousOn
      (swappedHardyOffDiagonalTerm m n coeff) box := by
    intro p hp
    exact (continuousAt_swappedHardyOffDiagonalTerm hm hn coeff
      (by linarith [hT, hp.2.1, hp.1.2.1])
      (by linarith [hT, hp.2.1, hp.1.1.1])).continuousWithinAt
  have hbox : IntegrableOn (swappedHardyOffDiagonalTerm m n coeff) box
      ((volume.prod volume).prod volume) :=
    hcontinuous.integrableOn_compact hcompact
  have hsmall : IntegrableOn (swappedHardyOffDiagonalTerm m n coeff)
      ((Set.Ioc 0 delta ×ˢ Set.Ioc 0 delta) ×ˢ
        Set.Ioc T (2 * T - delta))
      ((volume.prod volume).prod volume) :=
    hbox.mono_set <| Set.prod_mono
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
      Ioc_subset_Icc_self
  simpa only [Measure.prod_restrict, IntegrableOn] using hsmall

private theorem triple_integral_hardyPhaseCorrelationOffDiagonal_eq_sum
    (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0)
    {T delta : ℝ} (hT : 0 < T) (hdelta : 0 ≤ delta)
    (hroom : delta ≤ T) :
    (∫ w in 0..delta, ∫ v in 0..delta,
      ∫ t in T..2 * T - delta,
        hardyPhaseCorrelationOffDiagonal s coeff v w t) =
      ∑ m ∈ s, ∑ n ∈ s,
        if m = n then 0 else
          (starRingEnd ℂ) (coeff n) * coeff m *
            ∫ v in 0..delta, ∫ w in 0..delta,
              ∫ t in T..2 * T - delta,
                Complex.exp (I *
                  OscillatoryIntegral.hardyPhaseCorrelation m n w v t) := by
  classical
  have hlong : T ≤ 2 * T - delta := by linarith
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 delta)
  let μ : Measure ℝ := volume.restrict (Set.Ioc T (2 * T - delta))
  let K : (ℝ × ℝ) × ℝ → ℂ := fun p =>
    ∑ m ∈ s, ∑ n ∈ s, swappedHardyOffDiagonalTerm m n coeff p
  have hterm (m : ℕ) (hm : m ∈ s) (n : ℕ) (hn : n ∈ s) :
      Integrable (swappedHardyOffDiagonalTerm m n coeff) ((ν.prod ν).prod μ) := by
    simpa only [ν, μ] using integrable_swappedHardyOffDiagonalTerm
      (hpositive m hm) (hpositive n hn) coeff hT
  have hinner (m : ℕ) (hm : m ∈ s) : Integrable
      (fun p => ∑ n ∈ s, swappedHardyOffDiagonalTerm m n coeff p)
      ((ν.prod ν).prod μ) := by
    have hsum := Finset.sum_induction
      (fun n => swappedHardyOffDiagonalTerm m n coeff)
      (fun f => Integrable f ((ν.prod ν).prod μ))
      (fun f g hf hg => hf.add hg)
      (by exact integrable_zero _ _ _)
      (fun n hn => hterm m hm n hn)
    apply hsum.congr
    exact Filter.Eventually.of_forall fun p =>
      Finset.sum_apply p s (fun n => swappedHardyOffDiagonalTerm m n coeff)
  have hK : Integrable K ((ν.prod ν).prod μ) := by
    have hsum := Finset.sum_induction
      (fun m => fun p => ∑ n ∈ s, swappedHardyOffDiagonalTerm m n coeff p)
      (fun f => Integrable f ((ν.prod ν).prod μ))
      (fun f g hf hg => hf.add hg)
      (by exact integrable_zero _ _ _)
      (fun m hm => hinner m hm)
    apply hsum.congr
    exact Filter.Eventually.of_forall fun p =>
      Finset.sum_apply p s
        (fun m p => ∑ n ∈ s, swappedHardyOffDiagonalTerm m n coeff p)
  calc
    (∫ w in 0..delta, ∫ v in 0..delta,
        ∫ t in T..2 * T - delta,
          hardyPhaseCorrelationOffDiagonal s coeff v w t) =
        ∫ p, K p ∂((ν.prod ν).prod μ) := by
      have hKleft : Integrable
          (fun p : ℝ × ℝ => ∫ t, K (p, t) ∂μ) (ν.prod ν) :=
        hK.integral_prod_left
      rw [integral_prod _ hK, integral_prod _ hKleft]
      simp only [ν, μ, intervalIntegral.integral_of_le hdelta,
        intervalIntegral.integral_of_le hlong, K]
      unfold hardyPhaseCorrelationOffDiagonal swappedHardyOffDiagonalTerm
      rfl
    _ = ∑ m ∈ s, ∑ n ∈ s,
        ∫ p, swappedHardyOffDiagonalTerm m n coeff p
          ∂((ν.prod ν).prod μ) := by
      unfold K
      rw [integral_finset_sum _ (fun m hm => hinner m hm)]
      apply Finset.sum_congr rfl
      intro m hm
      rw [integral_finset_sum _ (fun n hn => hterm m hm n hn)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hmn : m = n
      · simp only [hmn, swappedHardyOffDiagonalTerm, ↓reduceIte,
          integral_zero]
      · change
          (∫ p, swappedHardyOffDiagonalTerm m n coeff p
            ∂((ν.prod ν).prod μ)) = _
        have hmnInt := hterm m hm n hn
        have hmnLeft : Integrable
            (fun p : ℝ × ℝ =>
              ∫ t, swappedHardyOffDiagonalTerm m n coeff (p, t) ∂μ)
            (ν.prod ν) := hmnInt.integral_prod_left
        rw [integral_prod _ hmnInt, integral_prod _ hmnLeft]
        simp only [ν, μ, intervalIntegral.integral_of_le hdelta,
          intervalIntegral.integral_of_le hlong,
          swappedHardyOffDiagonalTerm, hmn, ↓reduceIte]
        have htPull (x y : ℝ) :
            (∫ t in Set.Ioc T (2 * T - delta),
              ((starRingEnd ℂ) (coeff n) * coeff m) *
                Complex.exp (I *
                  OscillatoryIntegral.hardyPhaseCorrelation m n y x t)
              ∂volume) =
              ((starRingEnd ℂ) (coeff n) * coeff m) *
                ∫ t in Set.Ioc T (2 * T - delta),
                  Complex.exp (I *
                    OscillatoryIntegral.hardyPhaseCorrelation m n y x t)
                  ∂volume := MeasureTheory.integral_const_mul _ _
        simp_rw [htPull]
        have hvPull (x : ℝ) :
            (∫ y in Set.Ioc 0 delta,
              ((starRingEnd ℂ) (coeff n) * coeff m) *
                (∫ t in Set.Ioc T (2 * T - delta),
                  Complex.exp (I *
                    OscillatoryIntegral.hardyPhaseCorrelation m n y x t)
                  ∂volume) ∂volume) =
              ((starRingEnd ℂ) (coeff n) * coeff m) *
                ∫ y in Set.Ioc 0 delta,
                  ∫ t in Set.Ioc T (2 * T - delta),
                    Complex.exp (I *
                      OscillatoryIntegral.hardyPhaseCorrelation m n y x t)
                    ∂volume ∂volume := MeasureTheory.integral_const_mul _ _
        simp_rw [hvPull]
        exact MeasureTheory.integral_const_mul _ _

/-- Exact full second-moment decomposition for a finite weighted Hardy-phase
sum.  The first term is the complete diagonal contribution; the second is
the real part of the shift-height integral of the full off-diagonal
correlation. -/
theorem integral_normSq_sum_hardyPhaseShortIntegral_eq_diagonal_add_offDiagonal
    (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0)
    {T delta : ℝ} (hT : 0 < T) (hdelta : 0 ≤ delta)
    (hroom : delta ≤ T) :
    (∫ t in T..2 * T - delta,
      Complex.normSq
        (∑ n ∈ s,
          coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t)) =
      (∑ n ∈ s, Complex.normSq (coeff n) *
        ∫ t in T..2 * T - delta,
          Complex.normSq
            (OscillatoryIntegral.hardyPhaseShortIntegral n delta t)) +
      (∫ w in 0..delta, ∫ v in 0..delta,
        ∫ t in T..2 * T - delta,
          hardyPhaseCorrelationOffDiagonal s coeff v w t).re := by
  classical
  have hlong : T ≤ 2 * T - delta := by linarith
  have hcross (m : ℕ) (hm : m ∈ s) (n : ℕ) (hn : n ∈ s) :
      IntervalIntegrable
        (fun t : ℝ =>
          ((starRingEnd ℂ)
              (coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
            (coeff m * OscillatoryIntegral.hardyPhaseShortIntegral m delta t)).re)
        volume T (2 * T - delta) := by
    have hint := intervalIntegrable_weighted_hardyPhaseCrossTerm
      (hpositive m hm) (hpositive n hn) coeff hT hdelta hlong
    exact ⟨Complex.reCLM.integrable_comp hint.1,
      Complex.reCLM.integrable_comp hint.2⟩
  have hinner (m : ℕ) (hm : m ∈ s) :
      IntervalIntegrable
        (fun t : ℝ => ∑ n ∈ s,
          ((starRingEnd ℂ)
              (coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
            (coeff m * OscillatoryIntegral.hardyPhaseShortIntegral m delta t)).re)
        volume T (2 * T - delta) := by
    have hsum := Finset.sum_induction
      (fun n => fun t : ℝ =>
        ((starRingEnd ℂ)
            (coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
          (coeff m * OscillatoryIntegral.hardyPhaseShortIntegral m delta t)).re)
      (fun f => IntervalIntegrable f volume T (2 * T - delta))
      (fun f g hf hg => hf.add hg) IntervalIntegrable.zero
      (fun n hn => hcross m hm n hn)
    apply hsum.congr
    intro t ht
    exact Finset.sum_apply t s (fun (n : ℕ) (t : ℝ) =>
      ((starRingEnd ℂ)
          (coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
        (coeff m * OscillatoryIntegral.hardyPhaseShortIntegral m delta t)).re)
  rw [show (fun t : ℝ =>
      Complex.normSq
        (∑ n ∈ s,
          coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t)) =
      fun t : ℝ => ∑ m ∈ s, ∑ n ∈ s,
        ((starRingEnd ℂ)
            (coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
          (coeff m * OscillatoryIntegral.hardyPhaseShortIntegral m delta t)).re by
    funext t
    exact MathlibAux.normSq_finset_sum_eq_sum_re_conj_mul s
      (fun n => coeff n *
        OscillatoryIntegral.hardyPhaseShortIntegral n delta t)]
  rw [intervalIntegral.integral_finset_sum]
  · have hinterchange :
        (∑ m ∈ s, ∫ t in T..2 * T - delta,
          ∑ n ∈ s,
            ((starRingEnd ℂ)
                (coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
              (coeff m * OscillatoryIntegral.hardyPhaseShortIntegral m delta t)).re) =
          ∑ m ∈ s, ∑ n ∈ s,
            ∫ t in T..2 * T - delta,
              ((starRingEnd ℂ)
                  (coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
                (coeff m * OscillatoryIntegral.hardyPhaseShortIntegral m delta t)).re := by
        apply Finset.sum_congr rfl
        intro m hm
        exact intervalIntegral.integral_finset_sum
          (fun n hn => hcross m hm n hn)
    rw [hinterchange]
    let D : ℕ → ℝ := fun n => Complex.normSq (coeff n) *
      ∫ t in T..2 * T - delta,
        Complex.normSq (OscillatoryIntegral.hardyPhaseShortIntegral n delta t)
    let O : ℕ → ℕ → ℝ := fun m n =>
      ((starRingEnd ℂ) (coeff n) * coeff m *
        ∫ v in 0..delta, ∫ w in 0..delta,
          ∫ t in T..2 * T - delta,
            Complex.exp (I *
              OscillatoryIntegral.hardyPhaseCorrelation m n w v t)).re
    have hterm (m : ℕ) (hm : m ∈ s) (n : ℕ) (hn : n ∈ s) :
        (∫ t in T..2 * T - delta,
          ((starRingEnd ℂ)
              (coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
            (coeff m * OscillatoryIntegral.hardyPhaseShortIntegral m delta t)).re) =
          if m = n then D n else O m n := by
      by_cases hmn : m = n
      · subst m
        simp only [if_pos, D]
        calc
          (∫ t in T..2 * T - delta,
            ((starRingEnd ℂ)
                (coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
              (coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t)).re) =
              ∫ t in T..2 * T - delta,
                Complex.normSq (coeff n) *
                  Complex.normSq
                    (OscillatoryIntegral.hardyPhaseShortIntegral n delta t) := by
            apply intervalIntegral.integral_congr
            intro t ht
            calc
              ((starRingEnd ℂ)
                  (coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
                (coeff n *
                  OscillatoryIntegral.hardyPhaseShortIntegral n delta t)).re =
                  Complex.normSq
                    (coeff n *
                      OscillatoryIntegral.hardyPhaseShortIntegral n delta t) := by
                have h := Complex.normSq_eq_conj_mul_self
                  (z := coeff n *
                    OscillatoryIntegral.hardyPhaseShortIntegral n delta t)
                exact (congrArg Complex.re h).symm
              _ = _ := Complex.normSq_mul _ _
          _ = _ := intervalIntegral.integral_const_mul _ _
      · simp only [if_neg hmn, O]
        have hint := intervalIntegrable_weighted_hardyPhaseCrossTerm
          (hpositive m hm) (hpositive n hn) coeff hT hdelta hlong
        calc
          (∫ t in T..2 * T - delta,
            ((starRingEnd ℂ)
                (coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
              (coeff m * OscillatoryIntegral.hardyPhaseShortIntegral m delta t)).re) =
              (∫ t in T..2 * T - delta,
                (starRingEnd ℂ)
                    (coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
                  (coeff m *
                    OscillatoryIntegral.hardyPhaseShortIntegral m delta t)).re :=
            Complex.reCLM.intervalIntegral_comp_comm hint
          _ = _ := by
            rw [integral_weighted_hardyPhaseCrossTerm_eq
              (hpositive m hm) (hpositive n hn) coeff hT hdelta hroom]
    have hsplit :
        (∑ m ∈ s, ∑ n ∈ s,
          ∫ t in T..2 * T - delta,
            ((starRingEnd ℂ)
                (coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t) *
              (coeff m * OscillatoryIntegral.hardyPhaseShortIntegral m delta t)).re) =
          (∑ n ∈ s, D n) +
            ∑ m ∈ s, ∑ n ∈ s, if m = n then 0 else O m n := by
      calc
        _ = ∑ m ∈ s, ∑ n ∈ s, if m = n then D n else O m n := by
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro n hn
          exact hterm m hm n hn
        _ = ∑ m ∈ s,
            (D m + ∑ n ∈ s \ {m}, O m n) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.sum_eq_add_sum_diff_singleton m
            (fun n => if m = n then D n else O m n)]
          · simp only [if_pos]
            congr 1
            apply Finset.sum_congr rfl
            intro n hn
            have hne : m ≠ n := by
              intro heq
              subst n
              exact (Finset.mem_sdiff.mp hn).2 (Finset.mem_singleton_self m)
            simp only [hne, ↓reduceIte]
          · intro hnot
            exact (hnot hm).elim
        _ = (∑ m ∈ s, D m) +
            ∑ m ∈ s, ∑ n ∈ s \ {m}, O m n := by
          rw [Finset.sum_add_distrib]
        _ = (∑ n ∈ s, D n) +
            ∑ m ∈ s, ∑ n ∈ s, if m = n then 0 else O m n := by
          congr 1
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.sum_eq_add_sum_diff_singleton m
            (fun n => if m = n then 0 else O m n)]
          · simp only [if_pos, zero_add]
            apply Finset.sum_congr rfl
            intro n hn
            have hne : m ≠ n := by
              intro heq
              subst n
              exact (Finset.mem_sdiff.mp hn).2 (Finset.mem_singleton_self m)
            simp only [hne, ↓reduceIte]
          · intro hnot
            exact (hnot hm).elim
    rw [hsplit]
    dsimp only [D, O]
    congr 1
    rw [triple_integral_hardyPhaseCorrelationOffDiagonal_eq_sum
      s coeff hpositive hT hdelta hroom]
    simp only [Complex.re_sum, apply_ite Complex.re, Complex.zero_re]
  · intro m hm
    exact hinner m hm

/-- The exact decomposition immediately bounds the off-diagonal real part by
the norm of the same triple integral. -/
theorem integral_normSq_sum_hardyPhaseShortIntegral_le_diagonal_add_offDiagonal_norm
    (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0)
    {T delta : ℝ} (hT : 0 < T) (hdelta : 0 ≤ delta)
    (hroom : delta ≤ T) :
    (∫ t in T..2 * T - delta,
      Complex.normSq
        (∑ n ∈ s,
          coeff n * OscillatoryIntegral.hardyPhaseShortIntegral n delta t)) ≤
      (∑ n ∈ s, Complex.normSq (coeff n) *
        ∫ t in T..2 * T - delta,
          Complex.normSq
            (OscillatoryIntegral.hardyPhaseShortIntegral n delta t)) +
      ‖∫ w in 0..delta, ∫ v in 0..delta,
        ∫ t in T..2 * T - delta,
          hardyPhaseCorrelationOffDiagonal s coeff v w t‖ := by
  rw [integral_normSq_sum_hardyPhaseShortIntegral_eq_diagonal_add_offDiagonal
    s coeff hpositive hT hdelta hroom]
  gcongr
  exact Complex.re_le_norm _

end HardyTheorem
