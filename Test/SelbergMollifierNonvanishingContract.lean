import HardyTheorem.SelbergMollifierNonvanishing

open Complex Filter Set

namespace HardyTheorem

example (X : ℕ) (coeff : ℕ → ℂ) :
    AnalyticOnNhd ℂ (selbergMollifier X coeff) Set.univ :=
  analyticOnNhd_selbergMollifier X coeff

example (X : ℕ) (coeff : ℕ → ℂ) (hX : 1 ≤ X) (hcoeff : coeff 1 = 1) :
    Tendsto (fun sigma : ℝ => selbergMollifier X coeff (sigma : ℂ))
      atTop (nhds 1) :=
  tendsto_selbergMollifier_real_atTop X coeff hX hcoeff

example (X : ℕ) (coeff : ℕ → ℂ) (hX : 1 ≤ X) (hcoeff : coeff 1 = 1) :
    ∃ s : ℂ, selbergMollifier X coeff s ≠ 0 :=
  exists_selbergMollifier_ne_zero X coeff hX hcoeff

example (X : ℕ) (coeff : ℕ → ℂ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => selbergMollifier X coeff ((1 / 2 : ℂ) + I * z))
      Set.univ :=
  analyticOnNhd_selbergMollifier_vertical X coeff

example (X : ℕ) (coeff : ℕ → ℂ) (hX : 1 ≤ X) (hcoeff : coeff 1 = 1)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Set.Ioo a b,
      selbergMollifier X coeff ((1 / 2 : ℂ) + I * t) ≠ 0 :=
  exists_selbergMollifier_criticalLine_ne_zero_Ioo X coeff hX hcoeff hab

example (X : ℕ) (coeff : ℕ → ℂ) (hX : 1 ≤ X) (hcoeff : coeff 1 = 1)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Set.Ioo a b, selbergMollifiedHardyZ X coeff t ≠ 0 :=
  exists_selbergMollifiedHardyZ_ne_zero_Ioo X coeff hX hcoeff hab

end HardyTheorem
