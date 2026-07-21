import HardyTheorem.SelbergGoodWindowMeasure
import MathlibAux.PaleyZygmund
import MathlibAux.SlidingIntervalCorrelation
import MathlibAux.SlidingWindowBadSet

open MeasureTheory Set

namespace HardyTheorem

/-!
# The signed Selberg bad set from second moments

This file reduces the exceptional set where a mollified Hardy short integral
is large to the square mass of the same function.  The final estimate uses a
single global `L²` mass on the enlarged interval containing all short windows.
-/

/-- Cauchy--Schwarz on an interval of length `H`, in the squared form used by
the signed-short-integral exceptional-set argument. -/
theorem abs_intervalIntegral_sq_le_length_mul_intervalIntegral_sq
    {F : ℝ → ℝ} (hF : Continuous F) {t H : ℝ} (hH : 0 ≤ H) :
    |∫ u in t..t + H, F u| ^ 2 ≤
      H * ∫ u in t..t + H, F u ^ 2 := by
  have hle : t ≤ t + H := by linarith
  have hfinite : volume (Ioc t (t + H)) ≠ ⊤ := measure_Ioc_lt_top.ne
  have hsq : IntegrableOn (fun u => F u ^ 2) (Ioc t (t + H)) volume :=
    (hF.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hcs := MathlibAux.sq_setIntegral_le_measureReal_mul_setIntegral_sq
    (s := Ioc t (t + H)) hfinite hF.measurable hsq
  rw [← intervalIntegral.integral_of_le hle] at hcs
  rw [← intervalIntegral.integral_of_le hle] at hcs
  simpa [Real.volume_Ioc, hH, sq_abs] using hcs

/-- The square mass in the length-`H` interval starting at `t`. -/
noncomputable def selbergMoebiusSquareWindowMass
    (X : ℕ) (H t : ℝ) : ℝ :=
  MathlibAux.slidingWindowMass
    (fun u => selbergMoebiusMollifiedHardyZ X u ^ 2) H t

/-- A large signed mollified short integral forces a large local `L²` mass. -/
theorem selbergExcessiveSignedMassStarts_subset_squareWindowMass
    {X : ℕ} {H eta : ℝ} (hH : 0 ≤ H) (heta : 0 ≤ eta) :
    selbergExcessiveSignedMassStarts X H eta ⊆
      {t | eta ^ 2 ≤ H * selbergMoebiusSquareWindowMass X H t} := by
  intro t ht
  have hcs := abs_intervalIntegral_sq_le_length_mul_intervalIntegral_sq
    (continuous_selbergMoebiusMollifiedHardyZ X) hH (t := t)
  have hthreshold : eta ^ 2 ≤
      |selbergMoebiusSignedShortIntegral X H t| ^ 2 := by
    have ht' : eta ≤ |selbergMoebiusSignedShortIntegral X H t| := by
      simpa [selbergExcessiveSignedMassStarts] using ht
    nlinarith [abs_nonneg (selbergMoebiusSignedShortIntegral X H t)]
  change eta ^ 2 ≤ H * selbergMoebiusSquareWindowMass X H t
  apply hthreshold.trans
  simpa [selbergMoebiusSignedShortIntegral,
    selbergMoebiusSquareWindowMass, MathlibAux.slidingWindowMass] using hcs

private theorem continuous_slidingWindowMass_of_continuous
    {g : ℝ → ℝ} (hg : Continuous g) (H : ℝ) :
    Continuous (MathlibAux.slidingWindowMass g H) := by
  let G : ℝ → ℝ := fun x => ∫ u in 0..x, g u
  have hG : Continuous G := by
    dsimp only [G]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (_x : ℝ) u => g u)
      (hg.comp continuous_snd) continuous_id
  have heq : MathlibAux.slidingWindowMass g H =
      fun t => G (t + H) - G t := by
    funext t
    have h0add : IntervalIntegrable g volume 0 (t + H) :=
      hg.intervalIntegrable _ _
    have h0t : IntervalIntegrable g volume 0 t :=
      hg.intervalIntegrable _ _
    dsimp only [MathlibAux.slidingWindowMass, G]
    exact (intervalIntegral.integral_interval_sub_left h0add h0t).symm
  rw [heq]
  exact (hG.comp (continuous_id.add continuous_const)).sub hG

/-- Averaging a nonnegative sliding mass over starts in `[A,B]` costs at
most the window length times the mass on the enlarged interval `[A,B+H]`. -/
theorem integral_slidingWindowMass_le_length_mul_globalMass
    {g : ℝ → ℝ} (hg : Continuous g) (hg_nonneg : ∀ u, 0 ≤ g u)
    {A B H : ℝ} (hAB : A ≤ B) (hH : 0 ≤ H) :
    (∫ t, MathlibAux.slidingWindowMass g H t
        ∂volume.restrict (Icc A B)) ≤
      H * ∫ u in A..B + H, g u := by
  let q : ℝ → ℝ → ℝ := fun t v => g (t + v)
  have hprodCompact :
      IsCompact (uIcc A B ×ˢ uIcc 0 H) :=
    isCompact_uIcc.prod isCompact_uIcc
  have hqcont : Continuous (Function.uncurry q) := by
    exact hg.comp (continuous_fst.add continuous_snd)
  have hqIntCompact : IntegrableOn (Function.uncurry q)
      (uIcc A B ×ˢ uIcc 0 H) (volume.prod volume) :=
    hqcont.continuousOn.integrableOn_compact hprodCompact
  have hqInt : Integrable (Function.uncurry q)
      ((volume.restrict (uIoc A B)).prod
        (volume.restrict (uIoc 0 H))) := by
    rw [Measure.prod_restrict]
    exact hqIntCompact.mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hswap := MeasureTheory.intervalIntegral_integral_swap
    (a := A) (b := B) (μ := volume.restrict (uIoc 0 H)) hqInt
  have hswap' :
      (∫ t in A..B, ∫ v in 0..H, q t v) =
        ∫ v in 0..H, ∫ t in A..B, q t v := by
    simpa [intervalIntegral.integral_of_le hH, uIoc_of_le hH] using hswap
  have hglobalInt : IntervalIntegrable g volume A (B + H) :=
    hg.intervalIntegrable _ _
  have hinner (v : ℝ) (hv : v ∈ Icc 0 H) :
      (∫ t in A..B, q t v) ≤ ∫ u in A..B + H, g u := by
    have hmono := intervalIntegral.integral_mono_interval
      (f := g) (μ := volume)
      (c := A) (a := A + v) (b := B + v) (d := B + H)
      (by linarith [hv.1]) (by linarith) (by linarith [hv.2])
      (Filter.Eventually.of_forall hg_nonneg) hglobalInt
    calc
      (∫ t in A..B, q t v) = ∫ u in A + v..B + v, g u := by
        simpa [q] using intervalIntegral.integral_comp_add_right g v
      _ ≤ ∫ u in A..B + H, g u := hmono
  have hconstInt : IntervalIntegrable
      (fun _v : ℝ => ∫ u in A..B + H, g u) volume 0 H :=
    continuous_const.intervalIntegrable _ _
  have hrightCont : Continuous (fun v : ℝ => ∫ t in A..B, q t v) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun v t => q t v)
      (by
        change Continuous (fun p : ℝ × ℝ => g (p.2 + p.1))
        exact hg.comp (continuous_snd.add continuous_fst)) A B
  have hrightInt : IntervalIntegrable
      (fun v : ℝ => ∫ t in A..B, q t v) volume 0 H :=
    hrightCont.intervalIntegrable _ _
  have houter :
      (∫ v in 0..H, ∫ t in A..B, q t v) ≤
        ∫ _v in 0..H, ∫ u in A..B + H, g u :=
    intervalIntegral.integral_mono_on hH hrightInt hconstInt hinner
  have hwindow (t : ℝ) :
      MathlibAux.slidingWindowMass g H t = ∫ v in 0..H, q t v := by
    dsimp only [MathlibAux.slidingWindowMass, q]
    calc
      (∫ u in t..t + H, g u) = ∫ u in 0 + t..H + t, g u := by ring_nf
      _ = ∫ v in 0..H, g (v + t) :=
        (intervalIntegral.integral_comp_add_right g t).symm
      _ = ∫ v in 0..H, g (t + v) := by
        apply intervalIntegral.integral_congr
        intro v _
        change g (v + t) = g (t + v)
        rw [add_comm]
  calc
    (∫ t, MathlibAux.slidingWindowMass g H t
        ∂volume.restrict (Icc A B)) =
        ∫ t in A..B, MathlibAux.slidingWindowMass g H t := by
      rw [intervalIntegral.integral_of_le hAB,
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ t in A..B, ∫ v in 0..H, q t v := by
      apply intervalIntegral.integral_congr
      intro t _
      exact hwindow t
    _ = ∫ v in 0..H, ∫ t in A..B, q t v := hswap'
    _ ≤ ∫ _v in 0..H, ∫ u in A..B + H, g u := houter
    _ = H * ∫ u in A..B + H, g u := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring

/-- The excessive-signed-integral bad starts are controlled by one global
`L²` mass on the enlarged interval. -/
theorem volume_selbergExcessiveSignedMassStarts_inter_Icc_le
    {X : ℕ} {A B H eta M : ℝ}
    (hAB : A ≤ B) (hH : 0 < H) (heta : 0 < eta)
    (hglobal :
      (∫ u in A..B + H, selbergMoebiusMollifiedHardyZ X u ^ 2) ≤ M) :
    volume.real (selbergExcessiveSignedMassStarts X H eta ∩ Icc A B) ≤
      H ^ 2 * M / eta ^ 2 := by
  let F : ℝ → ℝ := selbergMoebiusMollifiedHardyZ X
  let g : ℝ → ℝ := fun u => F u ^ 2
  have hF : Continuous F := continuous_selbergMoebiusMollifiedHardyZ X
  have hg : Continuous g := hF.pow 2
  have hg_nonneg : ∀ u, 0 ≤ g u := fun u => sq_nonneg (F u)
  have hmassInt : Integrable (MathlibAux.slidingWindowMass g H)
      (volume.restrict (Icc A B)) := by
    exact (continuous_slidingWindowMass_of_continuous hg H).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hmassBound :
      (∫ t, MathlibAux.slidingWindowMass g H t
          ∂volume.restrict (Icc A B)) ≤ H * M := by
    calc
      _ ≤ H * ∫ u in A..B + H, g u :=
        integral_slidingWindowMass_le_length_mul_globalMass
          hg hg_nonneg hAB hH.le
      _ ≤ H * M := mul_le_mul_of_nonneg_left (by simpa [g, F] using hglobal) hH.le
  have hmarkov := MathlibAux.volume_slidingWindowMass_ge_le
    hg.measurable hg_nonneg hH hmassInt hmassBound
    (show 0 < eta ^ 2 / H by positivity)
  have hsubset :
      selbergExcessiveSignedMassStarts X H eta ∩ Icc A B ⊆
        {t | eta ^ 2 / H ≤ MathlibAux.slidingWindowMass g H t} ∩ Icc A B := by
    intro t ht
    constructor
    · have hforce := selbergExcessiveSignedMassStarts_subset_squareWindowMass
        (X := X) hH.le heta.le ht.1
      change eta ^ 2 / H ≤ MathlibAux.slidingWindowMass g H t
      change eta ^ 2 ≤ H * MathlibAux.slidingWindowMass g H t at hforce
      exact (div_le_iff₀ hH).2 (by simpa [mul_comm] using hforce)
    · exact ht.2
  have hfinite :
      volume ({t | eta ^ 2 / H ≤ MathlibAux.slidingWindowMass g H t} ∩ Icc A B) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  calc
    volume.real (selbergExcessiveSignedMassStarts X H eta ∩ Icc A B) ≤
        volume.real ({t | eta ^ 2 / H ≤
          MathlibAux.slidingWindowMass g H t} ∩ Icc A B) :=
      measureReal_mono hsubset hfinite
    _ ≤ (H * M) / (eta ^ 2 / H) := hmarkov
    _ = H ^ 2 * M / eta ^ 2 := by
      field_simp [hH.ne', heta.ne']

end HardyTheorem
