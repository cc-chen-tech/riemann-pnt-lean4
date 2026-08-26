import HardyTheorem.SelbergFirstMomentBridge
import HardyTheorem.SelbergMollifierNonvanishing
import HardyTheorem.SelbergStrictCancellationPositiveMeasure
import MathlibAux.ContinuousLocalSignChange

open Complex MeasureTheory Set

namespace HardyTheorem

/-!
# Covering strict-cancellation starts by odd critical-line zeros

If a strict-cancellation window based at `t` contains an odd critical-line
zero at height `gamma`, then `t` belongs to `(gamma - H, gamma)`.  Hence all
good starts are covered by one interval of length `H` for each relevant odd
zero.  This avoids choosing a disjoint subfamily of windows and automatically
accounts for arbitrarily many starts detecting the same zero.
-/

/-- Selberg's completed mollified function is nonzero somewhere in every
nonempty real interval. -/
theorem exists_selbergCompletedMollifiedF_ne_zero_Ioo
    (delta : ℝ) (X : ℕ) (hX : 1 ≤ X) {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Set.Ioo a b, selbergCompletedMollifiedF delta X t ≠ 0 := by
  let coeff : ℕ → ℂ :=
    fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ)
  obtain ⟨t, ht, htM⟩ :=
    exists_selbergMollifiedHardyZ_ne_zero_Ioo X coeff hX
      (by simp [coeff]) hab
  have htSqrt : selbergSqrtZetaMollifiedHardyZ X t ≠ 0 := by
    simpa only [coeff, selbergSqrtZetaMollifiedHardyZ] using htM
  refine ⟨t, ht, ?_⟩
  have hGamma : 0 < ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ :=
    norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (by norm_num))
  have hcoeff : 0 < (1 / (2 * Real.sqrt (2 * Real.pi)) : ℝ) := by
    positivity
  have htilt : 0 < Real.exp ((Real.pi / 4 - delta / 2) * t) :=
    Real.exp_pos _
  have habsSqrt : 0 < |selbergSqrtZetaMollifiedHardyZ X t| :=
    abs_pos.mpr htSqrt
  have habsF : 0 < |selbergCompletedMollifiedF delta X t| := by
    rw [abs_selbergCompletedMollifiedF_eq_gamma_tilt_mul_abs_sqrtZeta]
    positivity
  exact abs_pos.mp habsF

/-- A strict-cancellation start for the completed Selberg function contains
a genuine local sign change of Hardy's `Z` function. -/
theorem exists_hardyZ_localSignChange_of_selbergCompleted_strictCancellationStart
    {delta : ℝ} {X : ℕ} (hX : 1 ≤ X) {H t : ℝ} (hH : 0 ≤ H)
    (ht : t ∈ MathlibAux.strictCancellationStarts
      (selbergCompletedMollifiedF delta X) H) :
    ∃ u ∈ Set.Ioo t (t + H), HasLocalSignChangeAt hardyZ u := by
  have hstrict :
      |∫ u in t..t + H, selbergCompletedMollifiedF delta X u| <
        ∫ u in t..t + H, |selbergCompletedMollifiedF delta X u| := by
    simpa only [MathlibAux.strictCancellationStarts, Set.mem_setOf_eq,
      MathlibAux.slidingSignedAbsMass, MathlibAux.slidingAbsoluteMass,
      MathlibAux.slidingWindowMass] using ht
  obtain ⟨u, hu, hchange⟩ :=
    MathlibAux.exists_local_sign_change_of_abs_intervalIntegral_lt_intervalIntegral_abs
      (continuous_selbergCompletedMollifiedF delta X)
      (show t ≤ t + H by linarith) hstrict
      (fun a b hab =>
        exists_selbergCompletedMollifiedF_ne_zero_Ioo delta X hX hab)
  have hchangeF : HasLocalSignChangeAt
      (selbergCompletedMollifiedF delta X) u := by
    simpa only [HasLocalSignChangeAt, HasNegToPosLocalSignChangeAt,
      HasPosToNegLocalSignChangeAt] using hchange
  exact ⟨u, hu,
    hasLocalSignChangeAt_hardyZ_of_selbergCompletedMollifiedF hchangeF⟩

/-- Every bounded family of strict-cancellation starts is covered backwards
by one interval of length `H` for each odd critical-line zero that can occur
in its forward windows. -/
theorem measure_strictCancellationStarts_selbergCompleted_le_oddZeroCount_mul
    {delta T H : ℝ} {X : ℕ} (hX : 1 ≤ X)
    (hH : 0 ≤ H) :
    volume.real
        (Set.Icc 0 T ∩ MathlibAux.strictCancellationStarts
          (selbergCompletedMollifiedF delta X) H) ≤
      (criticalLineOddZeroCount (T + H) : ℝ) * H := by
  classical
  let E : Set ℝ :=
    Set.Icc 0 T ∩ MathlibAux.strictCancellationStarts
      (selbergCompletedMollifiedF delta X) H
  let Z : Finset ℂ := criticalLineOddZerosFinset (T + H)
  let cover : Set ℝ :=
    ⋃ rho ∈ Z, Set.Ioo (rho.im - H) rho.im
  have hEcover : E ⊆ cover := by
    intro t ht
    obtain ⟨u, hu, hchange⟩ :=
      exists_hardyZ_localSignChange_of_selbergCompleted_strictCancellationStart
        hX hH ht.2
    have hzero : hardyZ u = 0 :=
      hchange.eq_zero hardyZ_continuous
    have hzeta : riemannZeta ((1 / 2 : ℂ) + I * u) = 0 := by
      convert hardyZ_zero_implies_zeta_zero u hzero using 1 <;> norm_num
    have hodd : Odd (analyticOrderNatAt riemannZeta
        ((1 / 2 : ℂ) + I * u)) := by
      rcases hchange with hchange | hchange
      · exact odd_analyticOrderNatAt_riemannZeta_of_hardyZ_local_sign_change
          hchange.1 hchange.2
      · exact
          odd_analyticOrderNatAt_riemannZeta_of_hardyZ_reverse_local_sign_change
            hchange.1 hchange.2
    have huNonneg : 0 ≤ u := ht.1.1.trans hu.1.le
    have huUpper : u ≤ T + H := by
      nlinarith [ht.1.2, hu.2]
    have huZ : (1 / 2 : ℂ) + I * u ∈ Z := by
      simp only [Z, criticalLineOddZerosFinset, Finset.mem_filter]
      refine ⟨?_, hodd⟩
      rw [mem_criticalLineZerosFinset]
      refine ⟨⟨hzeta, ?_, ?_⟩, ?_, ?_, ?_⟩
      · norm_num
      · norm_num
      · norm_num
      · simpa using huNonneg
      · simpa using huUpper
    refine Set.mem_iUnion₂.mpr ⟨(1 / 2 : ℂ) + I * u, huZ, ?_⟩
    constructor <;> norm_num at * <;> linarith
  have hcoverSubset : cover ⊆ Set.Icc (-H) (T + H) := by
    intro x hx
    simp only [cover, Set.mem_iUnion] at hx
    obtain ⟨rho, hrho⟩ := hx
    obtain ⟨hrhoZ, hxInterval⟩ := hrho
    have hrhoZ' : rho ∈ Z := by simpa using hrhoZ
    have hrhoBase : rho ∈ criticalLineZerosFinset (T + H) := by
      have hz := hrhoZ'
      simp only [Z, criticalLineOddZerosFinset, Finset.mem_filter] at hz
      exact hz.1
    have hrange := (mem_criticalLineZerosFinset.mp hrhoBase).2.2
    constructor
    · linarith [hrange.1, hxInterval.1]
    · exact hxInterval.2.le.trans hrange.2
  have hcover_ne_top : volume cover ≠ ⊤ := by
    apply measure_ne_top_of_subset hcoverSubset
    exact (measure_Icc_lt_top : volume (Set.Icc (-H) (T + H)) < ⊤).ne
  calc
    volume.real
        (Set.Icc 0 T ∩ MathlibAux.strictCancellationStarts
          (selbergCompletedMollifiedF delta X) H) = volume.real E := by rfl
    _ ≤ volume.real cover :=
      measureReal_mono hEcover hcover_ne_top
    _ ≤ ∑ rho ∈ Z, volume.real (Set.Ioo (rho.im - H) rho.im) := by
      simpa only [cover] using
        (measureReal_biUnion_finset_le (μ := volume) Z
          (fun rho : ℂ => Set.Ioo (rho.im - H) rho.im))
    _ = (Z.card : ℝ) * H := by
      simp [Measure.real, Real.volume_Ioo, hH]
    _ = (criticalLineOddZeroCount (T + H) : ℝ) * H := by
      rfl

/-- The Selberg mainline now gives the dyadic `T log T` lower bound directly:
the completed-mollifier strict-cancellation set has measure `≥ kappa*T`,
while the backward zero cover has measure at most `H*N_odd(T+H)`. -/
theorem exists_pos_mul_log_le_criticalLineOddZeroCount_two_mul_selberg :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T →
        C * T * Real.log T ≤
          (criticalLineOddZeroCount (2 * T) : ℝ) := by
  obtain ⟨a, kappa, Tmeasure, ha, haOne, hkappa, hTmeasure, hmeasure⟩ :=
    exists_pos_measure_strictCancellationStarts_selberg
  have hparam := eventually_selbergMomentParameter_conditions ha
  obtain ⟨Tparam, hparamAfter⟩ := Filter.eventually_atTop.1 hparam
  let C : ℝ := kappa * a / (128 * Real.pi)
  let T0 : ℝ := max Tmeasure Tparam
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, T0, hC, hTmeasure.trans (le_max_left _ _), ?_⟩
  intro T hT
  have hTmeasure' : Tmeasure ≤ T := (le_max_left _ _).trans hT
  have hTparam' : Tparam ≤ T := (le_max_right _ _).trans hT
  rcases hparamAfter T hTparam' with
    ⟨hdelta, _hdeltaOne, _hdeltaPi, hXtwo, hXexp, _hXpow,
      _hlogXa, _hlogDelta, hlogRatio, hH, hHT⟩
  let X : ℕ := selbergFirstMomentCutoff T
  let H : ℝ := selbergMomentWindow a T
  let F : ℝ → ℝ := selbergCompletedMollifiedF (1 / T) X
  have hTpos : 0 < T := one_div_pos.mp hdelta
  have hXone : 1 ≤ X := by
    dsimp only [X]
    omega
  have hmeasureT :
      kappa * T ≤ volume.real
        (Set.Icc 0 T ∩ MathlibAux.strictCancellationStarts F H) := by
    simpa only [X, H, F] using hmeasure T hTmeasure'
  have hcover :
      volume.real
          (Set.Icc 0 T ∩ MathlibAux.strictCancellationStarts F H) ≤
        (criticalLineOddZeroCount (T + H) : ℝ) * H := by
    simpa only [F] using
      measure_strictCancellationStarts_selbergCompleted_le_oddZeroCount_mul
        (delta := 1 / T) (T := T) (H := H) (X := X) hXone hH.le
  have hcountTH :
      kappa * T / H ≤
        (criticalLineOddZeroCount (T + H) : ℝ) := by
    exact (div_le_iff₀ hH).2 (hmeasureT.trans hcover)
  have hTH : T + H ≤ 2 * T := by
    dsimp only [H] at hHT ⊢
    linarith
  have hcountMono :
      (criticalLineOddZeroCount (T + H) : ℝ) ≤
        (criticalLineOddZeroCount (2 * T) : ℝ) := by
    exact_mod_cast criticalLineOddZeroCount_mono hTH
  have hlogX : 0 < Real.log (X : ℝ) := by
    have hExpOne : (1 : ℝ) < Real.exp 1 := by
      linarith [Real.exp_one_gt_d9]
    exact Real.log_pos (hExpOne.trans_le
      (by simpa only [X] using hXexp))
  have hInvDelta : 1 / (1 / T) = T := by field_simp
  have hratio : Real.log T / Real.log (X : ℝ) ≤ 64 := by
    simpa only [X, hInvDelta] using hlogRatio
  have hlogLower : Real.log T / 64 ≤ Real.log (X : ℝ) := by
    have hscaled := (div_le_iff₀ hlogX).mp hratio
    nlinarith
  have hlogRpow : Real.log ((X : ℝ) ^ a) =
      a * Real.log (X : ℝ) := Real.log_rpow (by positivity) a
  have hHform : H = 2 * Real.pi / (a * Real.log (X : ℝ)) := by
    dsimp [H, selbergMomentWindow]
    rw [hlogRpow]
  let D : ℝ := kappa * a * T / (2 * Real.pi)
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hscale : C * T * Real.log T ≤ kappa * T / H := by
    calc
      C * T * Real.log T = D * (Real.log T / 64) := by
        dsimp [C, D]
        ring
      _ ≤ D * Real.log (X : ℝ) :=
        mul_le_mul_of_nonneg_left hlogLower hD
      _ = kappa * T / H := by
        rw [hHform]
        dsimp [D]
        field_simp [ha.ne', hlogX.ne', Real.pi_ne_zero]
  exact hscale.trans (hcountTH.trans hcountMono)

/-- Unconditional Selberg theorem, through the Fourier--Mellin/square-root
zeta mollifier mainline and not through `Zeta23`: a positive proportion of
the critical-line zeros have odd analytic multiplicity. -/
theorem selberg_odd_zero_proportion_target_proved_mainline :
    selberg_odd_zero_proportion_target := by
  obtain ⟨C, T0, hC, _hT0, hdyadic⟩ :=
    exists_pos_mul_log_le_criticalLineOddZeroCount_two_mul_selberg
  let c : ℝ := C * Real.pi / 2
  let X0 : ℝ := 2 * max T0 (Real.exp 1)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hc, X0, ?_⟩
  intro X hX
  let T : ℝ := X / 2
  have hTlarge : max T0 (Real.exp 1) ≤ T := by
    dsimp only [T, X0] at hX ⊢
    linarith
  have hT0 : T0 ≤ T := (le_max_left _ _).trans hTlarge
  have hTexp : Real.exp 1 ≤ T := (le_max_right _ _).trans hTlarge
  have hTpos : 0 < T := (Real.exp_pos 1).trans_le hTexp
  have hlogone : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTpos]
    exact hTexp
  have hlogtwo : Real.log 2 ≤ Real.log T := by
    calc
      Real.log 2 ≤ 2 - 1 :=
        Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
      _ ≤ Real.log T := hlogone
  have hlogTwoT : Real.log (2 * T) ≤ 2 * Real.log T := by
    calc
      Real.log (2 * T) = Real.log 2 + Real.log T :=
        Real.log_mul (by norm_num) (ne_of_gt hTpos)
      _ ≤ Real.log T + Real.log T := by linarith
      _ = 2 * Real.log T := by ring
  have hXT : X = 2 * T := by
    dsimp only [T]
    ring
  have hdyadicT := hdyadic T hT0
  calc
    c * (X / (2 * Real.pi) * Real.log X) =
        C * T / 2 * Real.log (2 * T) := by
      rw [hXT]
      dsimp only [c]
      field_simp [Real.pi_ne_zero]
    _ ≤ C * T / 2 * (2 * Real.log T) :=
      mul_le_mul_of_nonneg_left hlogTwoT (by positivity)
    _ = C * T * Real.log T := by ring
    _ ≤ (criticalLineOddZeroCount (2 * T) : ℝ) := hdyadicT
    _ = (criticalLineOddZeroCount X : ℝ) := by rw [hXT]

/-- The corresponding distinct-zero positive-proportion statement. -/
theorem selberg_zero_proportion_target_proved_mainline :
    selberg_zero_proportion_target :=
  selberg_zero_proportion_target_of_odd
    selberg_odd_zero_proportion_target_proved_mainline

end HardyTheorem
