import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativePositiveTail

open Filter Real Complex
open scoped Topology BigOperators

namespace PrimeNumberTheorem

noncomputable def classicalRealOrdinateFixedMajorant (m : ℕ) : ℝ :=
  ∑ rho ∈ realOrdinateNontrivialZerosFinset 0,
    ‖pntRelativeZeroContribution (m : ℝ) rho‖

lemma classicalRealOrdinateFixedMajorant_nonneg (m : ℕ) :
    0 ≤ classicalRealOrdinateFixedMajorant m := by
  unfold classicalRealOrdinateFixedMajorant
  positivity

lemma tendsto_classicalRealOrdinateFixedMajorant_zero :
    Tendsto classicalRealOrdinateFixedMajorant atTop (nhds 0) := by
  let realZeros := realOrdinateNontrivialZerosFinset 0
  have hterm : ∀ rho ∈ realZeros,
      Tendsto
        (fun m : ℕ => ‖pntRelativeZeroContribution (m : ℝ) rho‖)
        atTop (nhds 0) := by
    intro rho hrho
    have hzero : RiemannHypothesis.IsNontrivialZero rho :=
      (mem_nontrivialZerosFinset.mp
        (mem_realOrdinateNontrivialZerosFinset.mp hrho).1).1
    have hreal :=
      tendsto_norm_pntRelativeZeroContribution_div_targetZeroPowerAmplitude
        (beta := 1) hzero.2.2
    have hplain : Tendsto
        (fun x : ℝ => ‖pntRelativeZeroContribution x rho‖)
        atTop (nhds 0) := by
      simpa [targetZeroPowerAmplitude] using hreal
    have hnat := hplain.comp tendsto_natCast_atTop_atTop
    change Tendsto
      (fun m : ℕ => ‖pntRelativeZeroContribution (m : ℝ) rho‖)
      atTop (nhds 0) at hnat
    exact hnat
  have hsum : Tendsto
      (fun m : ℕ => ∑ rho ∈ realZeros,
        ‖pntRelativeZeroContribution (m : ℝ) rho‖)
      atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finset_sum realZeros hterm
  simpa [classicalRealOrdinateFixedMajorant, realZeros] using hsum

lemma eventually_dynamicRealOrdinatePNTZeroTailNorm_le_classicalFixedMajorant
    {H : ℝ → ℝ} (hHtop : Tendsto H atTop atTop) :
    ∀ᶠ m : ℕ in atTop,
      dynamicRealOrdinatePNTZeroTailNorm H (m : ℝ) ≤
        classicalRealOrdinateFixedMajorant m := by
  have hheightReal : ∀ᶠ x : ℝ in atTop, 0 ≤ H x :=
    hHtop.eventually (eventually_ge_atTop (0 : ℝ))
  have hheight := tendsto_natCast_atTop_atTop.eventually hheightReal
  filter_upwards [hheight] with m hm
  have hset : realOrdinateNontrivialZerosFinset (H (m : ℝ)) =
      realOrdinateNontrivialZerosFinset 0 :=
    realOrdinateNontrivialZerosFinset_eq_zeroHeight hm
  rw [dynamicRealOrdinatePNTZeroTailNorm, hset]
  exact norm_sum_le _ _

noncomputable def classicalDyadicCarlsonFullZeroTailMajorant
    (E eta C kappa D rate : ℝ) (m : ℕ) : ℝ :=
  classicalDyadicCarlsonPositiveZeroTailMajorant E eta C kappa D rate m +
    classicalDyadicCarlsonPositiveZeroTailMajorant E eta C kappa D rate m +
    classicalRealOrdinateFixedMajorant m

lemma tendsto_classicalDyadicCarlsonFullZeroTailMajorant_zero
    {E eta C kappa D rate : ℝ}
    (hE : 0 ≤ E) (heta : 0 < eta)
    (hC : 0 ≤ C) (hkappa : 0 < kappa) (hrate : 0 < rate) :
    Tendsto
      (classicalDyadicCarlsonFullZeroTailMajorant
        E eta C kappa D rate) atTop (nhds 0) := by
  have hpositive :=
    tendsto_classicalDyadicCarlsonPositiveZeroTailMajorant_zero
      (D := D) hE heta hC hkappa hrate
  simpa [classicalDyadicCarlsonFullZeroTailMajorant] using
    (hpositive.add hpositive).add
      tendsto_classicalRealOrdinateFixedMajorant_zero

lemma exists_selectedClassicalAdmissibleDyadicCarlsonQuantitativeFullZeroTailMajorant :
    ∃ b rate D : ℝ,
      0 < b ∧ 0 < rate ∧ 0 < D ∧
      IsCarlsonMovingDyadicLogPowerGap
        (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
      ∀ selection : UniformNaturalPointGoodHeightSelection,
        IsSelectedHeightDynamicZeroFree
          (selectedClassicalAdmissibleGoodHeight b selection)
          (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
        ∃ E eta C kappa : ℝ,
          0 ≤ E ∧ 0 < eta ∧ 0 ≤ C ∧ 0 < kappa ∧
          Tendsto
            (classicalDyadicCarlsonFullZeroTailMajorant
              E eta C kappa D rate) atTop (nhds 0) ∧
          ∀ᶠ m : ℕ in atTop,
            dynamicFullPNTZeroTailNorm
                (selectedClassicalAdmissibleGoodHeight b selection) (m : ℝ) ≤
              classicalDyadicCarlsonFullZeroTailMajorant
                E eta C kappa D rate m := by
  rcases
      exists_selectedClassicalAdmissibleDyadicCarlsonQuantitativePositiveZeroTailMajorant with
    ⟨b, rate, D, hb, hrate, hD, hgap, hselected⟩
  refine ⟨b, rate, D, hb, hrate, hD, hgap, ?_⟩
  intro selection
  let H := selectedClassicalAdmissibleGoodHeight b selection
  rcases hselected selection with
    ⟨hzeroFree, E, eta, C, kappa, hE, heta, hC, hkappa,
      hpositiveZero, hpositive⟩
  have hreal :=
    eventually_dynamicRealOrdinatePNTZeroTailNorm_le_classicalFixedMajorant
      (tendsto_selectedClassicalAdmissibleGoodHeight_atTop hb selection)
  refine ⟨hzeroFree, E, eta, C, kappa, hE, heta, hC, hkappa,
    tendsto_classicalDyadicCarlsonFullZeroTailMajorant_zero
      hE heta hC hkappa hrate, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hpositive, hreal] with
      m hm hpositivem hrealm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  calc
    dynamicFullPNTZeroTailNorm H (m : ℝ) ≤
        dynamicPositivePNTTailNorm H (m : ℝ) +
          dynamicPositivePNTTailNorm H (m : ℝ) +
            dynamicRealOrdinatePNTZeroTailNorm H (m : ℝ) :=
      dynamicFullPNTZeroTailNorm_le_two_positive_add_real hmR
    _ ≤ classicalDyadicCarlsonPositiveZeroTailMajorant
            E eta C kappa D rate m +
          classicalDyadicCarlsonPositiveZeroTailMajorant
            E eta C kappa D rate m +
          classicalRealOrdinateFixedMajorant m :=
      add_le_add (add_le_add hpositivem hpositivem) hrealm
    _ = classicalDyadicCarlsonFullZeroTailMajorant
        E eta C kappa D rate m := rfl

end PrimeNumberTheorem
