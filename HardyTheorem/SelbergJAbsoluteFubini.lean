import HardyTheorem.SelbergJOffDiagonalPhysical
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Complex MeasureTheory Set

namespace HardyTheorem

/-! # Absolute Gaussian Fubini bound for the pair expansion of Selberg's `J` -/

noncomputable def selbergPhysicalExpandedPairIntegrand
    (delta theta : ℝ) (X kappa lambda mu nu : ℕ)
    (p : ℕ × ℕ) (u : ℝ) : ℂ :=
  selbergPhysicalPairMollifierCoefficient X kappa lambda mu nu *
    selbergPhysicalPairIntegrand delta theta u
      (p.1 + 1) kappa lambda (p.2 + 1) mu nu

theorem selbergPhysicalPairDamping_eq_parameters
    (delta : ℝ) (m kappa lambda n mu nu : ℕ) :
    selbergPhysicalPairDamping delta m kappa lambda n mu nu =
      selbergOffDiagonalGaussianParameter delta kappa lambda * (m : ℝ) ^ 2 +
        selbergOffDiagonalGaussianParameter delta mu nu * (n : ℝ) ^ 2 := by
  unfold selbergPhysicalPairDamping selbergPhysicalSquareRatio
    selbergOffDiagonalGaussianParameter
  push_cast
  ring

theorem selbergPhysicalPairDamping_ge_uniform
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {X kappa lambda mu nu : ℕ} (hX : 1 ≤ X)
    (hkappa : 1 ≤ kappa) (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    (hmu : 1 ≤ mu) (hnu : 1 ≤ nu) (hnuX : nu ≤ X)
    (m n : ℕ) :
    (delta / (X : ℝ) ^ 2) * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ≤
      selbergPhysicalPairDamping delta m kappa lambda n mu nu := by
  have hk := delta_div_sq_le_selbergOffDiagonalGaussianParameter
    hdelta hdelta1 hX hkappa hlambda hlambdaX
  have hm := delta_div_sq_le_selbergOffDiagonalGaussianParameter
    hdelta hdelta1 hX hmu hnu hnuX
  rw [selbergPhysicalPairDamping_eq_parameters]
  calc
    (delta / (X : ℝ) ^ 2) * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) =
        (delta / (X : ℝ) ^ 2) * (m : ℝ) ^ 2 +
          (delta / (X : ℝ) ^ 2) * (n : ℝ) ^ 2 := by ring
    _ ≤ selbergOffDiagonalGaussianParameter delta kappa lambda * (m : ℝ) ^ 2 +
        selbergOffDiagonalGaussianParameter delta mu nu * (n : ℝ) ^ 2 := by
      gcongr

theorem norm_selbergPhysicalPairMollifierCoefficient_le_one
    {X kappa lambda mu nu : ℕ} (hX : 2 ≤ X)
    (hkappa : 1 ≤ kappa) (hkappaX : kappa ≤ X)
    (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    (hmu : 1 ≤ mu) (hmuX : mu ≤ X)
    (hnu : 1 ≤ nu) (hnuX : nu ≤ X) :
    ‖selbergPhysicalPairMollifierCoefficient X kappa lambda mu nu‖ ≤ 1 := by
  have hcoeff := norm_selbergPhysicalPairMollifierCoefficient_le hX
    hkappa hkappaX hlambda hlambdaX hmu hmuX hnu hnuX
  have hden : 1 ≤ lambda * nu := Nat.mul_pos hlambda hnu
  have hinv : ((((lambda * nu : ℕ) : ℝ))⁻¹) ≤ 1 := by
    exact inv_le_one₀ (by positivity) |>.2 (by exact_mod_cast hden)
  exact hcoeff.trans hinv

theorem norm_selbergPhysicalExpandedPairIntegrand_le_linearGaussian
    {delta theta u : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hu : 1 ≤ u)
    {X kappa lambda mu nu : ℕ} (hX : 2 ≤ X)
    (hkappa : 1 ≤ kappa) (hkappaX : kappa ≤ X)
    (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    (hmu : 1 ≤ mu) (hmuX : mu ≤ X)
    (hnu : 1 ≤ nu) (hnuX : nu ≤ X)
    (p : ℕ × ℕ) :
    ‖selbergPhysicalExpandedPairIntegrand
        delta theta X kappa lambda mu nu p u‖ ≤
      Real.exp (-((delta / (X : ℝ) ^ 2) *
        ((((p.1 + 1 : ℕ) : ℝ) ^ 2) +
          (((p.2 + 1 : ℕ) : ℝ) ^ 2))) * u) := by
  let A : ℝ := (delta / (X : ℝ) ^ 2) *
    ((((p.1 + 1 : ℕ) : ℝ) ^ 2) + (((p.2 + 1 : ℕ) : ℝ) ^ 2))
  let P : ℝ := selbergPhysicalPairDamping delta
    (p.1 + 1) kappa lambda (p.2 + 1) mu nu
  have hXone : 1 ≤ X := hX.trans' (by norm_num)
  have hcoeff := norm_selbergPhysicalPairMollifierCoefficient_le_one hX
    hkappa hkappaX hlambda hlambdaX hmu hmuX hnu hnuX
  have hP : A ≤ P := by
    dsimp [A, P]
    exact selbergPhysicalPairDamping_ge_uniform
      hdelta hdelta1 hXone hkappa hlambda hlambdaX hmu hnu hnuX _ _
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hP0 : 0 ≤ P := hA0.trans hP
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have huSq : u ≤ u ^ 2 := by nlinarith
  have hrpow : u ^ (-theta) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith)
  have hexp : Real.exp (-P * u ^ 2) ≤ Real.exp (-A * u) := by
    apply Real.exp_le_exp.mpr
    have hPu : A * u ^ 2 ≤ P * u ^ 2 :=
      mul_le_mul_of_nonneg_right hP (sq_nonneg u)
    have hAu : A * u ≤ A * u ^ 2 :=
      mul_le_mul_of_nonneg_left huSq hA0
    linarith
  unfold selbergPhysicalExpandedPairIntegrand
  rw [norm_mul]
  unfold selbergPhysicalPairIntegrand
  rw [norm_selbergOscillatoryGaussian hu0]
  change ‖selbergPhysicalPairMollifierCoefficient X kappa lambda mu nu‖ *
      (u ^ (-theta) * Real.exp (-P * u ^ 2)) ≤ Real.exp (-A * u)
  calc
    ‖selbergPhysicalPairMollifierCoefficient X kappa lambda mu nu‖ *
        (u ^ (-theta) * Real.exp (-P * u ^ 2)) ≤
      1 * (1 * Real.exp (-A * u)) := by gcongr
    _ = Real.exp (-A * u) := by ring

theorem integrableOn_selbergPhysicalExpandedPairIntegrand
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x)
    {X kappa lambda mu nu : ℕ} (hX : 2 ≤ X)
    (hkappa : 1 ≤ kappa) (hkappaX : kappa ≤ X)
    (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    (hmu : 1 ≤ mu) (hmuX : mu ≤ X)
    (hnu : 1 ≤ nu) (hnuX : nu ≤ X)
    (p : ℕ × ℕ) :
    IntegrableOn (selbergPhysicalExpandedPairIntegrand
      delta theta X kappa lambda mu nu p) (Ioi x) := by
  let A : ℝ := (delta / (X : ℝ) ^ 2) *
    ((((p.1 + 1 : ℕ) : ℝ) ^ 2) + (((p.2 + 1 : ℕ) : ℝ) ^ 2))
  have hA : 0 < A := by dsimp [A]; positivity
  have hmajor := integrableOn_exp_mul_Ioi (a := -A) (by linarith) x
  apply Integrable.mono' hmajor
  · exact ContinuousOn.aestronglyMeasurable
      (continuousOn_of_forall_continuousAt fun u hu => by
        unfold selbergPhysicalExpandedPairIntegrand
        exact ContinuousAt.mul continuousAt_const
          (by
            unfold selbergPhysicalPairIntegrand selbergOscillatoryGaussian
            have hu0 : u ≠ 0 := ne_of_gt (zero_lt_one.trans_le (hx.trans hu.le))
            exact (Real.continuousAt_rpow_const u (-theta) (Or.inl hu0)).smul
              (by fun_prop))) measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (norm_selbergPhysicalExpandedPairIntegrand_le_linearGaussian
      hdelta hdelta1 htheta (hx.trans hu.le) hX
      hkappa hkappaX hlambda hlambdaX hmu hmuX hnu hnuX p).trans_eq
        (by dsimp [A])

theorem integral_norm_selbergPhysicalExpandedPairIntegrand_le_productGaussian
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x)
    {X kappa lambda mu nu : ℕ} (hX : 2 ≤ X)
    (hkappa : 1 ≤ kappa) (hkappaX : kappa ≤ X)
    (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    (hmu : 1 ≤ mu) (hmuX : mu ≤ X)
    (hnu : 1 ≤ nu) (hnuX : nu ≤ X)
    (p : ℕ × ℕ) :
    (∫ u in Ioi x, ‖selbergPhysicalExpandedPairIntegrand
        delta theta X kappa lambda mu nu p u‖) ≤
      (delta / (X : ℝ) ^ 2)⁻¹ *
        selbergGaussianMass (delta / (X : ℝ) ^ 2) p.1 *
        selbergGaussianMass (delta / (X : ℝ) ^ 2) p.2 := by
  let a : ℝ := delta / (X : ℝ) ^ 2
  let M : ℝ := (((p.1 + 1 : ℕ) : ℝ) ^ 2) + (((p.2 + 1 : ℕ) : ℝ) ^ 2)
  let A : ℝ := a * M
  have ha : 0 < a := by dsimp [a]; positivity
  have hM : 1 ≤ M := by
    have hp : (1 : ℝ) ≤ ((p.1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left 1 p.1
    dsimp [M]
    nlinarith [sq_nonneg (((p.2 + 1 : ℕ) : ℝ))]
  have hA : 0 < A := mul_pos ha (zero_lt_one.trans_le hM)
  have hf := integrableOn_selbergPhysicalExpandedPairIntegrand
    hdelta hdelta1 htheta hx hX hkappa hkappaX hlambda hlambdaX
      hmu hmuX hnu hnuX p
  have hmajor := integrableOn_exp_mul_Ioi (a := -A) (by linarith) x
  have hpoint : ∀ᵐ u ∂volume.restrict (Ioi x),
      ‖selbergPhysicalExpandedPairIntegrand
        delta theta X kappa lambda mu nu p u‖ ≤ Real.exp (-A * u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (norm_selbergPhysicalExpandedPairIntegrand_le_linearGaussian
      hdelta hdelta1 htheta (hx.trans hu.le) hX
      hkappa hkappaX hlambda hlambdaX hmu hmuX hnu hnuX p).trans_eq
        (by dsimp [A, a, M])
  have hintegral :
      (∫ u in Ioi x, ‖selbergPhysicalExpandedPairIntegrand
          delta theta X kappa lambda mu nu p u‖) ≤
        ∫ u in Ioi x, Real.exp (-A * u) :=
    integral_mono_ae hf.norm hmajor hpoint
  have hvalue : (∫ u in Ioi x, Real.exp (-A * u)) =
      Real.exp (-A * x) / A := by
    rw [integral_exp_mul_Ioi (a := -A) (by linarith) x]
    ring
  have hxA : Real.exp (-A * x) ≤ Real.exp (-A) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hAinv : A⁻¹ ≤ a⁻¹ := by
    have haA : a ≤ A := by dsimp [A]; nlinarith
    simpa only [one_div] using one_div_le_one_div_of_le ha haA
  have hnonneg : 0 ≤ Real.exp (-A * x) := (Real.exp_pos _).le
  have hprodExp : Real.exp (-A) =
      selbergGaussianMass a p.1 * selbergGaussianMass a p.2 := by
    unfold selbergGaussianMass
    dsimp [A, M]
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (∫ u in Ioi x, ‖selbergPhysicalExpandedPairIntegrand
        delta theta X kappa lambda mu nu p u‖) ≤
      ∫ u in Ioi x, Real.exp (-A * u) := hintegral
    _ = Real.exp (-A * x) * A⁻¹ := by rw [hvalue]; ring
    _ ≤ Real.exp (-A) * a⁻¹ := by gcongr
    _ = a⁻¹ * selbergGaussianMass a p.1 * selbergGaussianMass a p.2 := by
      rw [hprodExp]
      ring
    _ = _ := rfl

theorem summable_integral_norm_selbergPhysicalExpandedPairIntegrand
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x)
    {X kappa lambda mu nu : ℕ} (hX : 2 ≤ X)
    (hkappa : 1 ≤ kappa) (hkappaX : kappa ≤ X)
    (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    (hmu : 1 ≤ mu) (hmuX : mu ≤ X)
    (hnu : 1 ≤ nu) (hnuX : nu ≤ X) :
    Summable (fun p : ℕ × ℕ =>
      ∫ u in Ioi x, ‖selbergPhysicalExpandedPairIntegrand
        delta theta X kappa lambda mu nu p u‖) := by
  let a : ℝ := delta / (X : ℝ) ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hmass := summable_selbergGaussianMass ha
  have hprod := hmass.mul_of_nonneg hmass
    (fun _ => by unfold selbergGaussianMass; positivity)
    (fun _ => by unfold selbergGaussianMass; positivity)
  have hmajor := hprod.mul_left a⁻¹
  apply Summable.of_nonneg_of_le
  · intro p
    exact integral_nonneg fun _ => norm_nonneg _
  · intro p
    exact integral_norm_selbergPhysicalExpandedPairIntegrand_le_productGaussian
      hdelta hdelta1 htheta hx hX hkappa hkappaX hlambda hlambdaX
        hmu hmuX hnu hnuX p
  · simpa only [a, mul_assoc] using hmajor

theorem hasSum_integral_selbergPhysicalExpandedPairIntegrand
    {delta theta x : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x)
    {X kappa lambda mu nu : ℕ} (hX : 2 ≤ X)
    (hkappa : 1 ≤ kappa) (hkappaX : kappa ≤ X)
    (hlambda : 1 ≤ lambda) (hlambdaX : lambda ≤ X)
    (hmu : 1 ≤ mu) (hmuX : mu ≤ X)
    (hnu : 1 ≤ nu) (hnuX : nu ≤ X) :
    HasSum (fun p : ℕ × ℕ =>
      ∫ u in Ioi x, selbergPhysicalExpandedPairIntegrand
        delta theta X kappa lambda mu nu p u)
      (∫ u in Ioi x, ∑' p : ℕ × ℕ,
        selbergPhysicalExpandedPairIntegrand
          delta theta X kappa lambda mu nu p u) := by
  have hint : ∀ p : ℕ × ℕ, IntegrableOn
      (selbergPhysicalExpandedPairIntegrand
        delta theta X kappa lambda mu nu p) (Ioi x) := fun p =>
    integrableOn_selbergPhysicalExpandedPairIntegrand
      hdelta hdelta1 htheta hx hX hkappa hkappaX hlambda hlambdaX
        hmu hmuX hnu hnuX p
  have hsum := summable_integral_norm_selbergPhysicalExpandedPairIntegrand
    hdelta hdelta1 htheta hx hX hkappa hkappaX hlambda hlambdaX
      hmu hmuX hnu hnuX
  exact hasSum_integral_of_summable_integral_norm hint hsum

end HardyTheorem
