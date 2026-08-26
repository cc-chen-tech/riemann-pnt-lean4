import PrimeNumberTheorem.SingleLayerForcingBeta14Over17
import PrimeNumberTheorem.ZeroDensityExponentCertificate

/-!
# Single-layer forcing with separate forcing and density exponents

The existing Carlson theorem uses the same exponent in the forcing lower
bound and density upper bound.  This module separates them as `qF` and `qD`.
-/

namespace PrimeNumberTheorem

open Filter

/-- A positive power beats an arbitrary fixed natural power of the logarithm,
even after a real logarithmic deficit. -/
theorem powerGrowth_arbitraryLogGap_contradiction
    {A C k d : ℝ} {B : ℕ}
    (hA : 0 < A) (hC : 0 ≤ C) (hk : 0 ≤ k) (hd : 0 < d)
    (hineq : ∀ᶠ X in atTop,
      A * X ^ d * (Real.log X) ^ (-k) ≤ C * (Real.log X) ^ B) :
    False := by
  have hreduced : ∀ᶠ X in atTop,
      A * X ^ d * (Real.log X) ^ (-(k + (B : ℝ))) ≤
        C * (Real.log X) ^ 4 := by
    filter_upwards [hineq, Filter.eventually_ge_atTop (Real.exp 1)] with X hineqX hXe
    have hlogpos : 0 < Real.log X := by
      have hle : Real.log (Real.exp 1) ≤ Real.log X :=
        Real.log_le_log (Real.exp_pos 1) hXe
      exact lt_of_lt_of_le zero_lt_one (by simpa [Real.log_exp] using hle)
    have hlogone : 1 ≤ Real.log X := by
      have hle : Real.log (Real.exp 1) ≤ Real.log X :=
        Real.log_le_log (Real.exp_pos 1) hXe
      simpa [Real.log_exp] using hle
    have hinvB0 : 0 ≤ (Real.log X) ^ (-(B : ℝ)) :=
      Real.rpow_nonneg hlogpos.le _
    have hmul := mul_le_mul_of_nonneg_right hineqX hinvB0
    have hleft :
        A * X ^ d * (Real.log X) ^ (-k) * (Real.log X) ^ (-(B : ℝ)) =
          A * X ^ d * (Real.log X) ^ (-(k + (B : ℝ))) := by
      calc
        A * X ^ d * (Real.log X) ^ (-k) * (Real.log X) ^ (-(B : ℝ)) =
            A * X ^ d *
              ((Real.log X) ^ (-k) * (Real.log X) ^ (-(B : ℝ))) := by ring
        _ = A * X ^ d * (Real.log X) ^ (-k + -(B : ℝ)) := by
          rw [Real.rpow_add hlogpos]
        _ = A * X ^ d * (Real.log X) ^ (-(k + (B : ℝ))) := by
          congr 2
          ring
    have hright :
        C * (Real.log X) ^ B * (Real.log X) ^ (-(B : ℝ)) = C := by
      have hnat : (Real.log X) ^ B = (Real.log X) ^ (B : ℝ) :=
        (Real.rpow_natCast (Real.log X) B).symm
      calc
        C * (Real.log X) ^ B * (Real.log X) ^ (-(B : ℝ)) =
            C * ((Real.log X) ^ B * (Real.log X) ^ (-(B : ℝ))) := by ring
        _ = C * ((Real.log X) ^ (B : ℝ) *
            (Real.log X) ^ (-(B : ℝ))) := by rw [hnat]
        _ = C * (Real.log X) ^ ((B : ℝ) + -(B : ℝ)) := by
          rw [Real.rpow_add hlogpos]
        _ = C := by simp
    have hAC : A * X ^ d * (Real.log X) ^ (-(k + (B : ℝ))) ≤ C := by
      rwa [hleft, hright] at hmul
    have hlog4 : 1 ≤ (Real.log X) ^ 4 := one_le_pow₀ hlogone
    exact hAC.trans (by
      calc
        C = C * 1 := by ring
        _ ≤ C * (Real.log X) ^ 4 := mul_le_mul_of_nonneg_left hlog4 hC)
  exact powerGrowth_logGap_contradiction
    (A := A) (B := C) (k := k + (B : ℝ)) (d := d)
    hA hC (add_nonneg hk (Nat.cast_nonneg B)) hd hreduced

/-- A single-layer contradiction in which the forcing construction loses
`qF` while the terminal density theorem has exponent `qD`. -/
theorem singleLayerForcing_density_contradiction
    {σ β lam c k qF qD : ℝ} {B : ℕ}
    (hβ1 : β < 1) (hlam : 0 < lam) (hc : 0 < c) (hk : 0 ≤ k)
    (_hqD : 0 ≤ qD) (density : ZeroDensityEventualMajorant σ qD B)
    (hlow : ∀ᶠ X in atTop,
      c * X ^ (2 * lam * (β - σ) - lam * (1 - β) * qF) *
          (Real.log X) ^ (-k) ≤
        (ZeroDensity.zeroDensityCount σ (X ^ (lam * (1 - β))) : ℝ))
    (hgap : lam * (1 - β) * qD <
      2 * lam * (β - σ) - lam * (1 - β) * qF) :
    False := by
  have hγpos : 0 < lam * (1 - β) := mul_pos hlam (sub_pos.mpr hβ1)
  have hγ0 : 0 ≤ lam * (1 - β) := hγpos.le
  have hdensityX : ∀ᶠ X in atTop,
      (ZeroDensity.zeroDensityCount σ (X ^ (lam * (1 - β))) : ℝ) ≤
        density.C * ‖(X ^ (lam * (1 - β))) ^ qD *
          (Real.log (X ^ (lam * (1 - β)))) ^ B‖ := by
    have htend : Tendsto (fun X : ℝ => X ^ (lam * (1 - β))) atTop atTop :=
      tendsto_rpow_atTop hγpos
    exact htend.eventually density.bound
  have hnormalized : ∀ᶠ X in atTop,
      c * X ^ (2 * lam * (β - σ) - lam * (1 - β) * qF) *
          (Real.log X) ^ (-k) ≤
        density.C * (lam * (1 - β)) ^ B *
          X ^ (lam * (1 - β) * qD) * (Real.log X) ^ B := by
    filter_upwards [hlow, hdensityX, Filter.eventually_ge_atTop (1 : ℝ)] with
        X hlowX hupX hX1
    have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
    have hpow : (X ^ (lam * (1 - β))) ^ qD =
        X ^ (lam * (1 - β) * qD) := by
      exact (Real.rpow_mul hXpos.le (lam * (1 - β)) qD).symm
    have hlog : Real.log (X ^ (lam * (1 - β))) =
        (lam * (1 - β)) * Real.log X :=
      Real.log_rpow hXpos (lam * (1 - β))
    have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX1
    have hnorm : ‖(X ^ (lam * (1 - β))) ^ qD *
          (Real.log (X ^ (lam * (1 - β)))) ^ B‖ =
        X ^ (lam * (1 - β) * qD) * (lam * (1 - β)) ^ B *
          (Real.log X) ^ B := by
      rw [hpow, hlog, Real.norm_eq_abs]
      have hnonneg : 0 ≤ X ^ (lam * (1 - β) * qD) *
          ((lam * (1 - β)) * Real.log X) ^ B := by positivity
      rw [abs_of_nonneg hnonneg, mul_pow]
      ring
    exact hlowX.trans (by
      calc
        (ZeroDensity.zeroDensityCount σ (X ^ (lam * (1 - β))) : ℝ) ≤
            density.C *
              (X ^ (lam * (1 - β) * qD) * (lam * (1 - β)) ^ B *
                (Real.log X) ^ B) := by simpa [hnorm] using hupX
        _ = density.C * (lam * (1 - β)) ^ B *
            X ^ (lam * (1 - β) * qD) * (Real.log X) ^ B := by ring)
  let d : ℝ :=
    2 * lam * (β - σ) - lam * (1 - β) * qF - lam * (1 - β) * qD
  have hd : 0 < d := by
    dsimp [d]
    linarith [hgap]
  have hfinal : ∀ᶠ X in atTop,
      c * X ^ d * (Real.log X) ^ (-k) ≤
        (density.C * (lam * (1 - β)) ^ B) * (Real.log X) ^ B := by
    filter_upwards [hnormalized, Filter.eventually_ge_atTop (1 : ℝ)] with
        X hnormX hX1
    have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
    have hden : 0 < X ^ (lam * (1 - β) * qD) :=
      Real.rpow_pos_of_pos hXpos _
    have hdiv := div_le_div_of_nonneg_right hnormX hden.le
    have hleft :
        c * X ^ (2 * lam * (β - σ) - lam * (1 - β) * qF) *
              (Real.log X) ^ (-k) / X ^ (lam * (1 - β) * qD) =
          c * X ^ d * (Real.log X) ^ (-k) := by
      have hpowdiv :
          X ^ (2 * lam * (β - σ) - lam * (1 - β) * qF) /
              X ^ (lam * (1 - β) * qD) = X ^ d := by
        calc
          X ^ (2 * lam * (β - σ) - lam * (1 - β) * qF) /
                X ^ (lam * (1 - β) * qD) =
              X ^ (2 * lam * (β - σ) - lam * (1 - β) * qF) *
                X ^ (-(lam * (1 - β) * qD)) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg hXpos.le]
          _ = X ^ (2 * lam * (β - σ) - lam * (1 - β) * qF +
              -(lam * (1 - β) * qD)) := by rw [Real.rpow_add hXpos]
          _ = X ^ d := by rfl
      calc
        c * X ^ (2 * lam * (β - σ) - lam * (1 - β) * qF) *
              (Real.log X) ^ (-k) / X ^ (lam * (1 - β) * qD) =
            c * (Real.log X) ^ (-k) *
              (X ^ (2 * lam * (β - σ) - lam * (1 - β) * qF) /
                X ^ (lam * (1 - β) * qD)) := by ring
        _ = c * (Real.log X) ^ (-k) * X ^ d := by rw [hpowdiv]
        _ = c * X ^ d * (Real.log X) ^ (-k) := by ring
    have hright :
        density.C * (lam * (1 - β)) ^ B *
              X ^ (lam * (1 - β) * qD) * (Real.log X) ^ B /
                X ^ (lam * (1 - β) * qD) =
          (density.C * (lam * (1 - β)) ^ B) * (Real.log X) ^ B := by
      field_simp [hden.ne']
    rwa [hleft, hright] at hdiv
  have hC : 0 ≤ density.C * (lam * (1 - β)) ^ B :=
    mul_nonneg density.C_nonneg (pow_nonneg hγ0 B)
  exact powerGrowth_arbitraryLogGap_contradiction hc hC hk hd hfinal

/-- The separated-exponent gap at the old endpoint `β=14/17` is the exact
positive margin `15/1088`. -/
theorem separatedDensity_gap_at_fourteen_seventeenths :
    0 < 2 * (14 / 17 - 2 / 3) -
      (1 - 14 / 17) * (8 / 9 + diTargetExponent) := by
  rw [di_direct_gap_at_fourteen_seventeenths]
  norm_num

/-- The DI density certificate contradicts the old forcing lower bound for
every `β > 14/17`. -/
theorem singleLayerForcing_DI_contradiction
    {β lam c k : ℝ}
    (density : CarlsonDIImprovedDensityCertificate)
    (hβ : 14 / 17 < β) (hβ1 : β < 1)
    (hlam : 0 < lam) (hc : 0 < c) (hk : 0 ≤ k)
    (hlow : ∀ᶠ X in atTop,
      c * X ^ (2 * lam * (β - 2 / 3) - lam * (1 - β) * (8 / 9)) *
          (Real.log X) ^ (-k) ≤
        (ZeroDensity.zeroDensityCount (2 / 3)
          (X ^ (lam * (1 - β))) : ℝ)) :
    False := by
  have hqD : 0 ≤ diTargetExponent := by
    norm_num [diTargetExponent]
  have hgap : lam * (1 - β) * diTargetExponent <
      2 * lam * (β - 2 / 3) - lam * (1 - β) * (8 / 9) := by
    have hmargin : 0 < 2 * (β - 2 / 3) -
        (1 - β) * ((8 / 9) + diTargetExponent) := by
      norm_num [diTargetExponent] at hβ ⊢
      linarith
    nlinarith [mul_pos hlam hmargin]
  exact singleLayerForcing_density_contradiction
    hβ1 hlam hc hk hqD density hlow hgap

/-- Supplying both the old forcing family and the improved DI density
certificate plugs the new density exponent into the existing `14/17`
terminal exclusion. -/
theorem no_nontrivial_zero_re_gt_14_over_17_of_forcing_and_DI
    (density : CarlsonDIImprovedDensityCertificate)
    (hforcing : ∀ β lam : ℝ, (14 / 17 : ℝ) < β → β < 1 → 0 < lam →
      ∃ c k : ℝ, 0 < c ∧ 0 < k ∧
        ∀ᶠ X in atTop,
          c * X ^ (2 * lam * (β - 2 / 3) - lam * (1 - β) * (8 / 9)) *
              (Real.log X) ^ (-k) ≤
            (ZeroDensity.zeroDensityCount (2 / 3)
              (X ^ (lam * (1 - β))) : ℝ)) :
    ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → ρ.re ≤ (14 / 17 : ℝ) := by
  intro ρ hρ
  by_contra hnot
  have hβ : (14 / 17 : ℝ) < ρ.re := lt_of_not_ge hnot
  have hβ1 : ρ.re < 1 := hρ.2.2
  rcases hforcing ρ.re 1 hβ hβ1 (by norm_num) with
    ⟨c, k, hc, hk, hlow⟩
  exact singleLayerForcing_DI_contradiction density hβ hβ1
    (by norm_num) hc hk.le hlow

end PrimeNumberTheorem
