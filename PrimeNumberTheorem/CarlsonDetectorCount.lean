import PrimeNumberTheorem.CarlsonZeroDetector
import PrimeNumberTheorem.ZeroDensityCount

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The closed axis-parallel rectangle used to count zeros of Carlson's
detector. -/
def carlsonDetectorRectangle
    (sigma alpha a b : ℝ) : Set ℂ :=
  Set.Icc sigma alpha ×ℂ Set.Icc a b

theorem isCompact_carlsonDetectorRectangle
    (sigma alpha a b : ℝ) :
    IsCompact (carlsonDetectorRectangle sigma alpha a b) := by
  simpa [carlsonDetectorRectangle] using
    (isCompact_Icc.reProdIm isCompact_Icc)

/-- Carlson's detector is meromorphic on the whole complex plane. -/
theorem meromorphic_carlsonZeroDetector (X : ℕ) :
    Meromorphic (carlsonZeroDetector X) := by
  intro s
  have hzeta : MeromorphicAt riemannZeta s :=
    ZeroFreeRegion.meromorphic_riemannZeta s
  have hmollifier : MeromorphicAt (mobiusMollifier X) s :=
    (analyticAt_mobiusMollifier X s).meromorphicAt
  change MeromorphicAt
    (fun z : ℂ =>
      1 - (riemannZeta z * mobiusMollifier X z - 1) ^ 2) s
  exact (MeromorphicAt.const 1 s).sub
    (((hzeta.mul hmollifier).sub (MeromorphicAt.const 1 s)).pow 2)

/-- Finite divisor support of Carlson's detector on a closed rectangle. -/
noncomputable def carlsonDetectorRectangleDivisorSupport
    (X : ℕ) (sigma alpha a b : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor (carlsonZeroDetector X)
      (carlsonDetectorRectangle sigma alpha a b)).finiteSupport
    (isCompact_carlsonDetectorRectangle sigma alpha a b)).toFinset

/-- Total zero multiplicity of Carlson's detector in a closed rectangle.
Poles have negative divisor order and contribute zero through `Int.toNat`. -/
noncomputable def carlsonDetectorRectangleZeroCount
    (X : ℕ) (sigma alpha a b : ℝ) : ℕ :=
  let D := MeromorphicOn.divisor (carlsonZeroDetector X)
    (carlsonDetectorRectangle sigma alpha a b)
  ∑ z ∈ carlsonDetectorRectangleDivisorSupport X sigma alpha a b,
    (D z).toNat

/-- Finite divisor support of the pole-free Carlson detector on a closed
rectangle. -/
noncomputable def regularizedCarlsonDetectorRectangleDivisorSupport
    (X : ℕ) (sigma alpha a b : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
      (carlsonDetectorRectangle sigma alpha a b)).finiteSupport
    (isCompact_carlsonDetectorRectangle sigma alpha a b)).toFinset

/-- Distinct imaginary parts of the regularized detector zeros in the unit
height window used to select a quantitatively separated horizontal edge. -/
noncomputable def regularizedCarlsonDetectorHorizontalZeroHeights
    (X : ℕ) (sigma alpha T : ℝ) : Finset ℝ :=
  (regularizedCarlsonDetectorRectangleDivisorSupport
    X sigma alpha T (T + 1)).image Complex.im

/-- Total zero multiplicity of the pole-free Carlson detector in a closed
rectangle. -/
noncomputable def regularizedCarlsonDetectorRectangleZeroCount
    (X : ℕ) (sigma alpha a b : ℝ) : ℕ :=
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
    (carlsonDetectorRectangle sigma alpha a b)
  ∑ z ∈ regularizedCarlsonDetectorRectangleDivisorSupport
      X sigma alpha a b, (D z).toNat

/-- Multiplicity-weighted sum of the logarithmic principal parts contributed
by all regularized-detector zeros in a closed rectangle. -/
noncomputable def regularizedCarlsonDetectorRectanglePrincipalPart
    (X : ℕ) (sigma alpha a b : ℝ) (z : ℂ) : ℂ :=
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
    (carlsonDetectorRectangle sigma alpha a b)
  ∑ᶠ u, (D u : ℂ) * (z - u)⁻¹

/-- The logarithmic derivative after subtracting every rectangle-zero
principal part and filling the resulting removable singularities. -/
noncomputable def regularizedCarlsonDetectorRectangleRegularPart
    (X : ℕ) (sigma alpha a b : ℝ) : ℂ → ℂ :=
  let K := carlsonDetectorRectangle sigma alpha a b
  let P := regularizedCarlsonDetectorRectangleDivisorSupport
    X sigma alpha a b
  toMeromorphicNFOn
    (fun z : ℂ =>
      logDeriv (regularizedCarlsonZeroDetector X) z -
        ∑ u ∈ P,
          (analyticOrderNatAt (regularizedCarlsonZeroDetector X) u : ℂ) *
            (z - u)⁻¹)
    K

private theorem divisor_regularizedCarlsonZeroDetector_eq_analyticOrderNatAt_of_mem
    {X : ℕ} (hX : 1 ≤ X) {sigma alpha a b : ℝ}
    (hsigma : 0 < sigma) {z : ℂ}
    (hz : z ∈ carlsonDetectorRectangle sigma alpha a b) :
    MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
        (carlsonDetectorRectangle sigma alpha a b) z =
      (analyticOrderNatAt (regularizedCarlsonZeroDetector X) z : ℤ) := by
  have hzre : 0 < z.re := by
    have hzIcc := hz.1
    exact hsigma.trans_le hzIcc.1
  have hanalytic : AnalyticAt ℂ (regularizedCarlsonZeroDetector X) z :=
    analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X z hzre
  have horder :
      analyticOrderAt (regularizedCarlsonZeroDetector X) z ≠ ⊤ :=
    analyticOrderAt_regularizedCarlsonZeroDetector_ne_top X hX hzre
  rw [MeromorphicOn.divisor_apply
      (meromorphic_regularizedCarlsonZeroDetector X).meromorphicOn hz,
    hanalytic.meromorphicOrderAt_eq]
  have hcast := Nat.cast_analyticOrderNatAt horder
  rw [← hcast]
  simp

/-- If a point stays `delta` away from every zero in the rectangle, the norm
of the rectangle's full principal-part sum is at most total zero multiplicity
divided by `delta`. -/
theorem norm_regularizedCarlsonDetectorRectanglePrincipalPart_le_count_div
    {X : ℕ} (hX : 1 ≤ X) {sigma alpha a b delta : ℝ}
    (hsigma : 0 < sigma) (hdelta : 0 < delta) {z : ℂ}
    (hsep : ∀ u ∈ regularizedCarlsonDetectorRectangleDivisorSupport
        X sigma alpha a b, delta ≤ ‖z - u‖) :
    ‖regularizedCarlsonDetectorRectanglePrincipalPart
        X sigma alpha a b z‖ ≤
      (regularizedCarlsonDetectorRectangleZeroCount
        X sigma alpha a b : ℝ) / delta := by
  classical
  let K := carlsonDetectorRectangle sigma alpha a b
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X) K
  have hfinite : D.support.Finite :=
    D.finiteSupport (isCompact_carlsonDetectorRectangle sigma alpha a b)
  have hD : ∀ u, 0 ≤ D u := by
    intro u
    by_cases hu : u ∈ K
    · have hDu : D u =
          (analyticOrderNatAt (regularizedCarlsonZeroDetector X) u : ℤ) := by
        dsimp [D, K]
        exact divisor_regularizedCarlsonZeroDetector_eq_analyticOrderNatAt_of_mem
          hX hsigma hu
      rw [hDu]
      exact Int.natCast_nonneg _
    · dsimp [D]
      simp [MeromorphicOn.divisor, hu]
  have hsepSupport : ∀ u ∈ D.support, delta ≤ ‖z - u‖ := by
    intro u hu
    apply hsep u
    dsimp [regularizedCarlsonDetectorRectangleDivisorSupport, D, K]
    exact hfinite.mem_toFinset.mpr hu
  have hprincipal := ZeroFreeRegion.norm_finsum_divisor_mul_inv_le_mass_div
    hfinite hD hdelta hsepSupport
  have hmass :
      (∑ᶠ u, (D u : ℝ)) =
        (regularizedCarlsonDetectorRectangleZeroCount
          X sigma alpha a b : ℝ) := by
    rw [← ZeroFreeRegion.sum_toNat_eq_finsum_cast_of_nonneg_finiteSupport
      hfinite hD]
    dsimp [regularizedCarlsonDetectorRectangleZeroCount,
      regularizedCarlsonDetectorRectangleDivisorSupport, D, K]
    norm_cast
  simpa [regularizedCarlsonDetectorRectanglePrincipalPart, D, K, hmass]
    using hprincipal

/-- Inside a rectangle contained in the open right half-plane, the finite
divisor support of the regularized detector is exactly its zero set. -/
theorem mem_regularizedCarlsonDetectorRectangleDivisorSupport_iff_zero
    {X : ℕ} (hX : 1 ≤ X) {sigma alpha a b : ℝ}
    (hsigma : 0 < sigma) {z : ℂ}
    (hz : z ∈ carlsonDetectorRectangle sigma alpha a b) :
    z ∈ regularizedCarlsonDetectorRectangleDivisorSupport X sigma alpha a b ↔
      regularizedCarlsonZeroDetector X z = 0 := by
  classical
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
    (carlsonDetectorRectangle sigma alpha a b)
  have hdivisor : D z =
      (analyticOrderNatAt (regularizedCarlsonZeroDetector X) z : ℤ) := by
    dsimp [D]
    exact divisor_regularizedCarlsonZeroDetector_eq_analyticOrderNatAt_of_mem
      hX hsigma hz
  have hzre : 0 < z.re := hsigma.trans_le hz.1.1
  have hanalytic : AnalyticAt ℂ (regularizedCarlsonZeroDetector X) z :=
    analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X z hzre
  have horder :
      analyticOrderAt (regularizedCarlsonZeroDetector X) z ≠ ⊤ :=
    analyticOrderAt_regularizedCarlsonZeroDetector_ne_top X hX hzre
  have hnatCast := Nat.cast_analyticOrderNatAt horder
  rw [regularizedCarlsonDetectorRectangleDivisorSupport]
  rw [(D.finiteSupport
    (isCompact_carlsonDetectorRectangle sigma alpha a b)).mem_toFinset]
  simp only [Function.mem_support]
  rw [hdivisor, Int.ofNat_ne_zero]
  constructor
  · intro hnat
    apply hanalytic.analyticOrderAt_ne_zero.mp
    intro hzero
    have hcastZero :
        (analyticOrderNatAt (regularizedCarlsonZeroDetector X) z : ℕ∞) = 0 :=
      hnatCast.trans hzero
    exact hnat (by simpa using hcastZero)
  · intro hzero hnatZero
    have horderZero :
        analyticOrderAt (regularizedCarlsonZeroDetector X) z = 0 := by
      rw [← hnatCast, hnatZero]
      rfl
    exact (hanalytic.analyticOrderAt_eq_zero.mp horderZero) hzero

/-- The number of distinct zero ordinates in a unit rectangle is at most the
total analytic zero multiplicity in that rectangle. -/
theorem card_regularizedCarlsonDetectorHorizontalZeroHeights_le_zeroCount
    {X : ℕ} (hX : 1 ≤ X) {sigma alpha T : ℝ}
    (hsigma : 0 < sigma) :
    (regularizedCarlsonDetectorHorizontalZeroHeights
      X sigma alpha T).card ≤
      regularizedCarlsonDetectorRectangleZeroCount
        X sigma alpha T (T + 1) := by
  classical
  let K := carlsonDetectorRectangle sigma alpha T (T + 1)
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X) K
  let P := regularizedCarlsonDetectorRectangleDivisorSupport
    X sigma alpha T (T + 1)
  let H := regularizedCarlsonDetectorHorizontalZeroHeights X sigma alpha T
  have hfinite : D.support.Finite :=
    D.finiteSupport (isCompact_carlsonDetectorRectangle sigma alpha T (T + 1))
  have hpoint : ∀ u ∈ P, 1 ≤ (D u).toNat := by
    intro u hu
    have huSupport : u ∈ D.support := by
      change u ∈ hfinite.toFinset at hu
      exact hfinite.mem_toFinset.mp hu
    have huK : u ∈ K := by
      by_contra hnot
      have hDne : D u ≠ 0 := by
        simpa only [Function.mem_support] using huSupport
      apply hDne
      dsimp [D]
      simp [MeromorphicOn.divisor, hnot]
    have hDu : D u =
        (analyticOrderNatAt (regularizedCarlsonZeroDetector X) u : ℤ) := by
      dsimp [D, K]
      exact divisor_regularizedCarlsonZeroDetector_eq_analyticOrderNatAt_of_mem
        hX hsigma huK
    have hDne : D u ≠ 0 := by
      simpa only [Function.mem_support] using huSupport
    have hnatNe :
        analyticOrderNatAt (regularizedCarlsonZeroDetector X) u ≠ 0 := by
      rw [hDu, Int.ofNat_ne_zero] at hDne
      exact hDne
    rw [hDu, Int.toNat_natCast]
    exact Nat.one_le_iff_ne_zero.mpr hnatNe
  calc
    H.card ≤ P.card := by
      dsimp [H, regularizedCarlsonDetectorHorizontalZeroHeights]
      exact Finset.card_image_le
    _ = ∑ u ∈ P, 1 := by simp
    _ ≤ ∑ u ∈ P, (D u).toNat := by
      exact Finset.sum_le_sum fun u hu => hpoint u hu
    _ = regularizedCarlsonDetectorRectangleZeroCount
        X sigma alpha T (T + 1) := by
      rfl

/-- Subtracting all multiplicity-weighted rectangle-zero principal parts
removes every singularity of the detector logarithmic derivative on the
rectangle. -/
theorem analyticOnNhd_regularizedCarlsonDetectorRectangleRegularPart
    {X : ℕ} (hX : 1 ≤ X) {sigma alpha a b : ℝ}
    (hsigma : 0 < sigma) :
    AnalyticOnNhd ℂ
      (regularizedCarlsonDetectorRectangleRegularPart X sigma alpha a b)
      (carlsonDetectorRectangle sigma alpha a b) := by
  classical
  let K := carlsonDetectorRectangle sigma alpha a b
  let P := regularizedCarlsonDetectorRectangleDivisorSupport
    X sigma alpha a b
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X) K
  have hfinite : D.support.Finite :=
    D.finiteSupport (isCompact_carlsonDetectorRectangle sigma alpha a b)
  have hf : AnalyticOnNhd ℂ (regularizedCarlsonZeroDetector X) K := by
    intro z hz
    exact analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X z (hsigma.trans_le hz.1.1)
  have hzero : ∀ z ∈ K,
      regularizedCarlsonZeroDetector X z = 0 ↔ z ∈ P := by
    intro z hz
    simpa [P, K] using
      (mem_regularizedCarlsonDetectorRectangleDivisorSupport_iff_zero
        hX hsigma hz).symm
  have horder : ∀ u ∈ P,
      analyticOrderAt (regularizedCarlsonZeroDetector X) u =
        analyticOrderNatAt (regularizedCarlsonZeroDetector X) u := by
    intro u hu
    have huSupport : u ∈ D.support := by
      change u ∈ hfinite.toFinset at hu
      exact hfinite.mem_toFinset.mp hu
    have huK : u ∈ K := by
      by_contra hnot
      have hDne : D u ≠ 0 := by
        simpa only [Function.mem_support] using huSupport
      apply hDne
      dsimp [D]
      simp [MeromorphicOn.divisor, hnot]
    have huRe : 0 < u.re := hsigma.trans_le huK.1.1
    exact (Nat.cast_analyticOrderNatAt
      (analyticOrderAt_regularizedCarlsonZeroDetector_ne_top
        X hX huRe)).symm
  dsimp [regularizedCarlsonDetectorRectangleRegularPart]
  exact
    ZeroFreeRegion.analyticOnNhd_toMeromorphicNFOn_logDeriv_sub_finset_principalParts
      hf P (analyticOrderNatAt (regularizedCarlsonZeroDetector X)) hzero horder

/-- Away from detector zeros, the normalized regular part is literally the
logarithmic derivative minus the complete multiplicity-weighted rectangle
principal part. -/
theorem regularizedCarlsonDetectorRectangleRegularPart_eq_logDeriv_sub_principalPart
    {X : ℕ} (hX : 1 ≤ X) {sigma alpha a b : ℝ}
    (hsigma : 0 < sigma) {z : ℂ}
    (hz : z ∈ carlsonDetectorRectangle sigma alpha a b)
    (hne : regularizedCarlsonZeroDetector X z ≠ 0) :
    regularizedCarlsonDetectorRectangleRegularPart X sigma alpha a b z =
      logDeriv (regularizedCarlsonZeroDetector X) z -
        regularizedCarlsonDetectorRectanglePrincipalPart
          X sigma alpha a b z := by
  classical
  let K := carlsonDetectorRectangle sigma alpha a b
  let P := regularizedCarlsonDetectorRectangleDivisorSupport
    X sigma alpha a b
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X) K
  let raw : ℂ → ℂ := fun w =>
    logDeriv (regularizedCarlsonZeroDetector X) w -
      ∑ u ∈ P,
        (analyticOrderNatAt (regularizedCarlsonZeroDetector X) u : ℂ) *
          (w - u)⁻¹
  have hf : AnalyticOnNhd ℂ (regularizedCarlsonZeroDetector X) K := by
    intro w hw
    exact analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X w (hsigma.trans_le hw.1.1)
  have hfinite : D.support.Finite :=
    D.finiteSupport (isCompact_carlsonDetectorRectangle sigma alpha a b)
  have hD : ∀ u, 0 ≤ D u := by
    intro u
    by_cases hu : u ∈ K
    · have hDu : D u =
          (analyticOrderNatAt (regularizedCarlsonZeroDetector X) u : ℤ) := by
        dsimp [D, K]
        exact divisor_regularizedCarlsonZeroDetector_eq_analyticOrderNatAt_of_mem
          hX hsigma hu
      rw [hDu]
      exact Int.natCast_nonneg _
    · dsimp [D]
      simp [MeromorphicOn.divisor, hu]
  have hprincipal :
      (∑ u ∈ P,
          (analyticOrderNatAt (regularizedCarlsonZeroDetector X) u : ℂ) *
            (z - u)⁻¹) =
        regularizedCarlsonDetectorRectanglePrincipalPart
          X sigma alpha a b z := by
    rw [regularizedCarlsonDetectorRectanglePrincipalPart]
    rw [← ZeroFreeRegion.sum_toNat_cast_mul_eq_finsum_cast_mul_of_nonneg_finiteSupport
      hfinite hD (fun u => (z - u)⁻¹)]
    apply Finset.sum_congr
    · rfl
    · intro u hu
      have huSupport : u ∈ D.support := hfinite.mem_toFinset.mp hu
      have huK : u ∈ K := by
        by_contra hnot
        have hDne : D u ≠ 0 := by
          simpa only [Function.mem_support] using huSupport
        apply hDne
        dsimp [D]
        simp [MeromorphicOn.divisor, hnot]
      have hDu : D u =
          (analyticOrderNatAt (regularizedCarlsonZeroDetector X) u : ℤ) := by
        dsimp [D, K]
        exact divisor_regularizedCarlsonZeroDetector_eq_analyticOrderNatAt_of_mem
          hX hsigma huK
      rw [hDu, Int.toNat_natCast]
  have hrawMeromorphic : MeromorphicOn raw K := by
    simpa [raw] using
      ZeroFreeRegion.meromorphicOn_logDeriv_sub_finset_principalParts
        hf.meromorphicOn P
          (analyticOrderNatAt (regularizedCarlsonZeroDetector X))
  have hrawAnalytic : AnalyticAt ℂ raw z := by
    have hlog : AnalyticAt ℂ
        (logDeriv (regularizedCarlsonZeroDetector X)) z :=
      (hf z hz).deriv.div (hf z hz) hne
    have hsum : AnalyticAt ℂ
        (fun w : ℂ =>
          ∑ u ∈ P,
            (analyticOrderNatAt (regularizedCarlsonZeroDetector X) u : ℂ) *
              (w - u)⁻¹) z := by
      apply Finset.analyticAt_fun_sum
      intro u hu
      have hzu : z ≠ u := by
        intro heq
        subst u
        exact hne
          ((mem_regularizedCarlsonDetectorRectangleDivisorSupport_iff_zero
            hX hsigma hz).mp (by simpa [P] using hu))
      exact analyticAt_const.mul
        ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hzu))
    simpa [raw] using hlog.sub hsum
  have hregular :
      regularizedCarlsonDetectorRectangleRegularPart
          X sigma alpha a b z = raw z := by
    dsimp [regularizedCarlsonDetectorRectangleRegularPart]
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hrawMeromorphic hz]
    rw [toMeromorphicNFAt_eq_self.2 hrawAnalytic.meromorphicNFAt]
  rw [hregular]
  dsimp [raw]
  rw [hprincipal]

/-- Every unit height interval contains a horizontal segment on which the
regularized detector is nonvanishing throughout a prescribed compact real
interval in the open right half-plane. -/
theorem exists_regularizedCarlsonZeroDetector_horizontal_ne_zero
    {X : ℕ} (hX : 1 ≤ X) {sigma alpha T : ℝ}
    (hsigma : 0 < sigma) :
    ∃ t : ℝ, T < t ∧ t < T + 1 ∧
      ∀ x ∈ Set.Icc sigma alpha,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (t : ℂ) * I) ≠ 0 := by
  classical
  let P := regularizedCarlsonDetectorRectangleDivisorSupport
    X sigma alpha T (T + 1)
  let bad : Finset ℝ := P.image Complex.im
  obtain ⟨t, htIoo, htbad⟩ :=
    (Set.Ioo_infinite (show T < T + 1 by linarith)).exists_notMem_finset bad
  refine ⟨t, htIoo.1, htIoo.2, ?_⟩
  intro x hx hzero
  let z : ℂ := (x : ℂ) + (t : ℂ) * I
  have hz : z ∈ carlsonDetectorRectangle sigma alpha T (T + 1) := by
    change z.re ∈ Set.Icc sigma alpha ∧ z.im ∈ Set.Icc T (T + 1)
    constructor
    · simpa [z] using hx
    · simpa [z] using And.intro htIoo.1.le htIoo.2.le
  have hzP : z ∈ P := by
    dsimp [P]
    exact
      (mem_regularizedCarlsonDetectorRectangleDivisorSupport_iff_zero
        hX hsigma hz).mpr hzero
  apply htbad
  dsimp [bad]
  apply Finset.mem_image.mpr
  refine ⟨z, hzP, ?_⟩
  dsimp [z]
  simp

/-- Every unit height interval contains a horizontal segment separated by an
explicit pigeonhole distance from every regularized-detector zero in the
corresponding rectangle.  In particular, the detector is nonzero on the whole
segment. -/
theorem exists_regularizedCarlsonZeroDetector_horizontal_quantitativelySeparated
    {X : ℕ} (hX : 1 ≤ X) {sigma alpha T : ℝ}
    (hsigma : 0 < sigma) :
    ∃ t ∈ Set.Icc T (T + 1),
      (∀ z ∈ regularizedCarlsonDetectorRectangleDivisorSupport
          X sigma alpha T (T + 1),
        1 / ((4 : ℝ) *
            ((regularizedCarlsonDetectorHorizontalZeroHeights
              X sigma alpha T).card + 1)) ≤ |t - z.im|) ∧
      ∀ x ∈ Set.Icc sigma alpha,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (t : ℂ) * I) ≠ 0 := by
  classical
  let P := regularizedCarlsonDetectorRectangleDivisorSupport
    X sigma alpha T (T + 1)
  let H := regularizedCarlsonDetectorHorizontalZeroHeights X sigma alpha T
  rcases ZeroFreeRegion.exists_radius_separated_from_finset H
      (show T < T + 1 by linarith) with ⟨t, ht, hsep⟩
  have hdelta :
      0 < 1 / ((4 : ℝ) * ((H.card : ℝ) + 1)) := by
    positivity
  refine ⟨t, ht, ?_, ?_⟩
  · intro z hz
    have hzim : z.im ∈ H := by
      dsimp [H, regularizedCarlsonDetectorHorizontalZeroHeights]
      exact Finset.mem_image.mpr ⟨z, by simpa [P] using hz, rfl⟩
    simpa [H] using hsep z.im hzim
  · intro x hx hzero
    let z : ℂ := (x : ℂ) + (t : ℂ) * I
    have hz : z ∈ carlsonDetectorRectangle sigma alpha T (T + 1) := by
      change z.re ∈ Set.Icc sigma alpha ∧ z.im ∈ Set.Icc T (T + 1)
      constructor
      · simpa [z] using hx
      · simpa [z] using ht
    have hzP : z ∈ P := by
      dsimp [P]
      exact
        (mem_regularizedCarlsonDetectorRectangleDivisorSupport_iff_zero
          hX hsigma hz).mpr hzero
    have hzim : z.im ∈ H := by
      dsimp [H, regularizedCarlsonDetectorHorizontalZeroHeights]
      exact Finset.mem_image.mpr ⟨z, by simpa [P] using hzP, rfl⟩
    have hzeroDistance :
        1 / ((4 : ℝ) * ((H.card : ℝ) + 1)) ≤ 0 := by
      simpa [z] using hsep z.im hzim
    exact (not_lt_of_ge hzeroDistance) hdelta

/-- On a quantitatively selected horizontal segment, the complete principal
part contributed by rectangle zeros is uniformly bounded by the rectangle's
total zero multiplicity divided by the pigeonhole separation. -/
theorem exists_regularizedCarlsonZeroDetector_horizontal_principalPart_le_count
    {X : ℕ} (hX : 1 ≤ X) {sigma alpha T : ℝ}
    (hsigma : 0 < sigma) :
    ∃ t ∈ Set.Icc T (T + 1),
      (∀ x ∈ Set.Icc sigma alpha,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
      ∀ x ∈ Set.Icc sigma alpha,
        ‖regularizedCarlsonDetectorRectanglePrincipalPart
          X sigma alpha T (T + 1)
            ((x : ℂ) + (t : ℂ) * I)‖ ≤
          (regularizedCarlsonDetectorRectangleZeroCount
            X sigma alpha T (T + 1) : ℝ) /
            (1 / ((4 : ℝ) *
              ((regularizedCarlsonDetectorHorizontalZeroHeights
                X sigma alpha T).card + 1))) := by
  classical
  let H := regularizedCarlsonDetectorHorizontalZeroHeights X sigma alpha T
  let delta : ℝ := 1 / ((4 : ℝ) * ((H.card : ℝ) + 1))
  rcases
      exists_regularizedCarlsonZeroDetector_horizontal_quantitativelySeparated
        hX hsigma (alpha := alpha) (T := T) with
    ⟨t, ht, hsep, hne⟩
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  refine ⟨t, ht, hne, ?_⟩
  intro x _hx
  apply norm_regularizedCarlsonDetectorRectanglePrincipalPart_le_count_div
    hX hsigma hdelta
  intro u hu
  have hheight : delta ≤ |t - u.im| := by
    simpa [delta, H] using hsep u hu
  let z : ℂ := (x : ℂ) + (t : ℂ) * I
  have him : |(z - u).im| ≤ ‖z - u‖ := Complex.abs_im_le_norm (z - u)
  have hrewrite : |(z - u).im| = |t - u.im| := by
    simp [z]
  rw [hrewrite] at him
  simpa [z] using hheight.trans him

/-- A uniform bound for the analytic regular part on a unit rectangle,
together with quantitative zero avoidance, yields a usable logarithmic-
derivative bound on one horizontal segment in that window. -/
theorem exists_regularizedCarlsonZeroDetector_horizontal_logDeriv_le_regular_add_count
    {X : ℕ} (hX : 1 ≤ X) {sigma alpha T M : ℝ}
    (hsigma : 0 < sigma)
    (hregular : ∀ t ∈ Set.Icc T (T + 1), ∀ x ∈ Set.Icc sigma alpha,
      ‖regularizedCarlsonDetectorRectangleRegularPart
        X sigma alpha T (T + 1) ((x : ℂ) + (t : ℂ) * I)‖ ≤ M) :
    ∃ t ∈ Set.Icc T (T + 1),
      (∀ x ∈ Set.Icc sigma alpha,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
      ∀ x ∈ Set.Icc sigma alpha,
        ‖logDeriv (regularizedCarlsonZeroDetector X)
          ((x : ℂ) + (t : ℂ) * I)‖ ≤
          M + (regularizedCarlsonDetectorRectangleZeroCount
            X sigma alpha T (T + 1) : ℝ) /
            (1 / ((4 : ℝ) *
              ((regularizedCarlsonDetectorHorizontalZeroHeights
                X sigma alpha T).card + 1))) := by
  rcases
      exists_regularizedCarlsonZeroDetector_horizontal_principalPart_le_count
        hX hsigma (alpha := alpha) (T := T) with
    ⟨t, ht, hne, hprincipal⟩
  refine ⟨t, ht, hne, ?_⟩
  intro x hx
  let z : ℂ := (x : ℂ) + (t : ℂ) * I
  have hz : z ∈ carlsonDetectorRectangle sigma alpha T (T + 1) := by
    change z.re ∈ Set.Icc sigma alpha ∧ z.im ∈ Set.Icc T (T + 1)
    constructor
    · simpa [z] using hx
    · simpa [z] using ht
  have hsplit :
      logDeriv (regularizedCarlsonZeroDetector X) z =
        regularizedCarlsonDetectorRectangleRegularPart
            X sigma alpha T (T + 1) z +
          regularizedCarlsonDetectorRectanglePrincipalPart
            X sigma alpha T (T + 1) z := by
    have hdecomposition :=
      regularizedCarlsonDetectorRectangleRegularPart_eq_logDeriv_sub_principalPart
        hX hsigma hz (hne x hx)
    linear_combination -hdecomposition
  rw [hsplit]
  exact (norm_add_le _ _).trans
    (add_le_add (by simpa [z] using hregular t ht x hx)
      (by simpa [z] using hprincipal x hx))

/-- Every nonempty real interval in the open right half-plane contains a
vertical segment on which the regularized detector is nonvanishing over a
prescribed compact height interval. -/
theorem exists_regularizedCarlsonZeroDetector_vertical_ne_zero
    {X : ℕ} (hX : 1 ≤ X) {sigma0 sigma1 a b : ℝ}
    (hsigma0 : 0 < sigma0) (hsigma : sigma0 < sigma1) :
    ∃ sigma : ℝ, sigma0 < sigma ∧ sigma < sigma1 ∧
      ∀ t ∈ Set.Icc a b,
        regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + (t : ℂ) * I) ≠ 0 := by
  classical
  let P := regularizedCarlsonDetectorRectangleDivisorSupport
    X sigma0 sigma1 a b
  let bad : Finset ℝ := P.image Complex.re
  obtain ⟨sigma, hsigmaIoo, hsigmabad⟩ :=
    (Set.Ioo_infinite hsigma).exists_notMem_finset bad
  refine ⟨sigma, hsigmaIoo.1, hsigmaIoo.2, ?_⟩
  intro t ht hzero
  let z : ℂ := (sigma : ℂ) + (t : ℂ) * I
  have hz : z ∈ carlsonDetectorRectangle sigma0 sigma1 a b := by
    change z.re ∈ Set.Icc sigma0 sigma1 ∧ z.im ∈ Set.Icc a b
    constructor
    · simpa [z] using And.intro hsigmaIoo.1.le hsigmaIoo.2.le
    · simpa [z] using ht
  have hzP : z ∈ P := by
    dsimp [P]
    exact
      (mem_regularizedCarlsonDetectorRectangleDivisorSupport_iff_zero
        hX hsigma0 hz).mpr hzero
  apply hsigmabad
  dsimp [bad]
  apply Finset.mem_image.mpr
  refine ⟨z, hzP, ?_⟩
  dsimp [z]
  simp

/-- A detector rectangle whose left side can be selected in any prescribed
nonempty interval `(theta, sigma)` in the open right half-plane. -/
theorem exists_regularizedCarlsonZeroDetector_goodRectangle_of_leftWindow
    {X : ℕ} (hX : 1 ≤ X) {theta sigma T : ℝ}
    (htheta : 0 < theta) (hthetaSigma : theta < sigma)
    (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      theta < x0 ∧ x0 < sigma ∧
      1 < x1 ∧ x1 < 2 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y0 : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) := by
  obtain ⟨x0, hx0Lower, hx0Upper, hx0ne⟩ :=
    exists_regularizedCarlsonZeroDetector_vertical_ne_zero
      hX htheta hthetaSigma
      (a := (-1 : ℝ)) (b := T + 1)
  obtain ⟨x1, hx1Lower, hx1Upper, hx1ne⟩ :=
    exists_regularizedCarlsonZeroDetector_vertical_ne_zero
      hX (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
      (a := (-1 : ℝ)) (b := T + 1)
  have hx0Pos : 0 < x0 := htheta.trans hx0Lower
  obtain ⟨y0, hy0Lower, hy0Upper, hy0ne⟩ :=
    exists_regularizedCarlsonZeroDetector_horizontal_ne_zero
      hX hx0Pos (alpha := x1) (T := (-1 : ℝ))
  obtain ⟨y1, hy1Lower, hy1Upper, hy1ne⟩ :=
    exists_regularizedCarlsonZeroDetector_horizontal_ne_zero
      hX hx0Pos (alpha := x1) (T := T)
  refine ⟨x0, x1, y0, y1,
    hx0Lower, hx0Upper, hx1Lower, hx1Upper,
    hx0Upper.trans (hsigmaOne.trans hx1Lower),
    hy0Lower, ?_, hy1Lower, hy1Upper,
    (by linarith [hy0Upper, hT, hy1Lower]), ?_, ?_, hy0ne, hy1ne⟩
  · linarith
  · intro y hy
    apply hx0ne y
    constructor
    · exact hy0Lower.le.trans hy.1
    · exact hy.2.trans hy1Upper.le
  · intro y hy
    apply hx1ne y
    constructor
    · exact hy0Lower.le.trans hy.1
    · exact hy.2.trans hy1Upper.le

/-- A good detector rectangle with the quantitative fixed right edge
`Re(s) = 4`.  Only the left and horizontal sides need finite-zero avoidance;
the right side is uniformly zero-free by the Mobius-tail estimate. -/
theorem exists_regularizedCarlsonZeroDetector_goodRectangle_fixedRight_of_leftWindow
    {X : ℕ} (hX : 1 ≤ X) {theta sigma T : ℝ}
    (htheta : 0 < theta) (hthetaSigma : theta < sigma)
    (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      theta < x0 ∧ x0 < sigma ∧ x1 = 4 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y0 : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) := by
  obtain ⟨x0, hx0Lower, hx0Upper, hx0ne⟩ :=
    exists_regularizedCarlsonZeroDetector_vertical_ne_zero
      hX htheta hthetaSigma
      (a := (-1 : ℝ)) (b := T + 1)
  have hx0Pos : 0 < x0 := htheta.trans hx0Lower
  obtain ⟨y0, hy0Lower, hy0Upper, hy0ne⟩ :=
    exists_regularizedCarlsonZeroDetector_horizontal_ne_zero
      hX hx0Pos (alpha := 4) (T := (-1 : ℝ))
  obtain ⟨y1, hy1Lower, hy1Upper, hy1ne⟩ :=
    exists_regularizedCarlsonZeroDetector_horizontal_ne_zero
      hX hx0Pos (alpha := 4) (T := T)
  refine ⟨x0, 4, y0, y1,
    hx0Lower, hx0Upper, rfl, ?_, hy0Lower, ?_, hy1Lower, hy1Upper,
    (by linarith [hy0Upper, hT, hy1Lower]), ?_, ?_, hy0ne, hy1ne⟩
  · linarith
  · linarith
  · intro y hy
    apply hx0ne y
    constructor
    · exact hy0Lower.le.trans hy.1
    · exact hy.2.trans hy1Upper.le
  · intro y _hy
    apply regularizedCarlsonZeroDetector_ne_zero_of_four_le_re hX
    simp

/-- Backwards-compatible good rectangle with left window
`(sigma / 2, sigma)`. -/
theorem exists_regularizedCarlsonZeroDetector_goodRectangle
    {X : ℕ} (hX : 1 ≤ X) {sigma T : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      sigma / 2 < x0 ∧ x0 < sigma ∧
      1 < x1 ∧ x1 < 2 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y0 : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) := by
  exact exists_regularizedCarlsonZeroDetector_goodRectangle_of_leftWindow
    hX (by linarith) (by linarith) hsigmaOne hT

/-- Carlson-ready good rectangle: when `sigma > 1/2`, its left edge can also
be chosen strictly to the right of `1/2`, as required by the mean-square
estimate. -/
theorem exists_regularizedCarlsonZeroDetector_goodRectangle_half
    {X : ℕ} (hX : 1 ≤ X) {sigma T : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) (hT : 0 ≤ T) :
    ∃ x0 x1 y0 y1 : ℝ,
      1 / 2 < x0 ∧ x0 < sigma ∧
      1 < x1 ∧ x1 < 2 ∧ x0 < x1 ∧
      -1 < y0 ∧ y0 < 0 ∧
      T < y1 ∧ y1 < T + 1 ∧ y0 < y1 ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x0 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ Set.Icc y0 y1,
        regularizedCarlsonZeroDetector X
          ((x1 : ℂ) + (y : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y0 : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc x0 x1,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (y1 : ℂ) * I) ≠ 0) := by
  exact exists_regularizedCarlsonZeroDetector_goodRectangle_of_leftWindow
    hX (by norm_num) hsigma hsigmaOne hT

private theorem divisor_carlsonZeroDetector_eq_analyticOrderNatAt
    {X : ℕ} {sigma alpha a b : ℝ} {rho : ℂ}
    (hX : 1 ≤ X) (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (hmem : rho ∈ carlsonDetectorRectangle sigma alpha a b) :
    MeromorphicOn.divisor (carlsonZeroDetector X)
        (carlsonDetectorRectangle sigma alpha a b) rho =
      (analyticOrderNatAt (carlsonZeroDetector X) rho : ℤ) := by
  have hrho1 : rho ≠ 1 := by
    intro hone
    have hre := congrArg Complex.re hone
    simp at hre
    linarith [hrho.2.2]
  have hzeta : AnalyticAt ℂ riemannZeta rho :=
    ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one rho hrho1
  have hmollifier : AnalyticAt ℂ (mobiusMollifier X) rho :=
    analyticAt_mobiusMollifier X rho
  have hdetector : AnalyticAt ℂ (carlsonZeroDetector X) rho := by
    unfold carlsonZeroDetector mollifiedZetaError
    exact analyticAt_const.sub
      (((hzeta.mul hmollifier).sub analyticAt_const).pow 2)
  have hzeta_pos : 0 < analyticOrderNatAt riemannZeta rho :=
    ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero hrho1 hrho.1
  have hdetector_pos :
      0 < analyticOrderNatAt (carlsonZeroDetector X) rho :=
    hzeta_pos.trans_le
      (analyticOrderNatAt_riemannZeta_le_carlsonZeroDetector hX hrho)
  have hdetector_order_ne_top :
      analyticOrderAt (carlsonZeroDetector X) rho ≠ ⊤ := by
    intro htop
    have hzero : analyticOrderNatAt (carlsonZeroDetector X) rho = 0 := by
      simp [analyticOrderNatAt, htop]
    omega
  rw [MeromorphicOn.divisor_apply
      (meromorphic_carlsonZeroDetector X).meromorphicOn hmem,
    hdetector.meromorphicOrderAt_eq]
  have horder := Nat.cast_analyticOrderNatAt hdetector_order_ne_top
  rw [← horder]
  simp

/-- Every zeta zero counted by `zeroDensityCount sigma T` is a detector zero
inside the closed rectangle `[sigma, 1] × [0, T]`, with at least the same
multiplicity. -/
theorem zeroDensityCount_le_carlsonDetectorRectangleZeroCount
    {X : ℕ} (hX : 1 ≤ X) (sigma T : ℝ) :
    ZeroDensity.zeroDensityCount sigma T ≤
      carlsonDetectorRectangleZeroCount X sigma 1 0 T := by
  classical
  let K : Set ℂ := carlsonDetectorRectangle sigma 1 0 T
  let D := MeromorphicOn.divisor (carlsonZeroDetector X) K
  let S := ZeroDensity.zeroDensityZerosFinset sigma T
  let P := carlsonDetectorRectangleDivisorSupport X sigma 1 0 T
  have hS_subset : S ⊆ P := by
    intro rho hrhoS
    have hrho := ZeroDensity.mem_zeroDensityZerosFinset.mp hrhoS
    have hmem : rho ∈ K := by
      dsimp [K, carlsonDetectorRectangle]
      simp only [Complex.mem_reProdIm, Set.mem_Icc]
      exact ⟨⟨hrho.2.2.2.le, hrho.1.2.2.le⟩,
        ⟨hrho.2.1.le, hrho.2.2.1⟩⟩
    have hdivisor : D rho =
        (analyticOrderNatAt (carlsonZeroDetector X) rho : ℤ) := by
      dsimp [D, K]
      exact divisor_carlsonZeroDetector_eq_analyticOrderNatAt
        hX hrho.1 hmem
    have hpositive : 0 < analyticOrderNatAt (carlsonZeroDetector X) rho :=
      (ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        (by
          intro hone
          have hre := congrArg Complex.re hone
          simp at hre
          linarith [hrho.1.2.2]) hrho.1.1).trans_le
        (analyticOrderNatAt_riemannZeta_le_carlsonZeroDetector hX hrho.1)
    dsimp [P, carlsonDetectorRectangleDivisorSupport]
    apply (D.finiteSupport
      (isCompact_carlsonDetectorRectangle sigma 1 0 T)).mem_toFinset.mpr
    simp only [Function.mem_support]
    rw [hdivisor]
    exact_mod_cast hpositive.ne'
  calc
    ZeroDensity.zeroDensityCount sigma T =
        ∑ rho ∈ S, analyticOrderNatAt riemannZeta rho := rfl
    _ ≤ ∑ rho ∈ S, (D rho).toNat := by
      apply Finset.sum_le_sum
      intro rho hrhoS
      have hrho := ZeroDensity.mem_zeroDensityZerosFinset.mp hrhoS
      have hmem : rho ∈ K := by
        dsimp [K, carlsonDetectorRectangle]
        simp only [Complex.mem_reProdIm, Set.mem_Icc]
        exact ⟨⟨hrho.2.2.2.le, hrho.1.2.2.le⟩,
          ⟨hrho.2.1.le, hrho.2.2.1⟩⟩
      have hdivisor : D rho =
          (analyticOrderNatAt (carlsonZeroDetector X) rho : ℤ) := by
        dsimp [D, K]
        exact divisor_carlsonZeroDetector_eq_analyticOrderNatAt
          hX hrho.1 hmem
      rw [hdivisor, Int.toNat_natCast]
      exact analyticOrderNatAt_riemannZeta_le_carlsonZeroDetector hX hrho.1
    _ ≤ ∑ z ∈ P, (D z).toNat :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_subset
        (fun _ _ _ => Nat.zero_le _)
    _ = carlsonDetectorRectangleZeroCount X sigma 1 0 T := rfl

private theorem divisor_regularizedCarlsonZeroDetector_eq_analyticOrderNatAt
    {X : ℕ} {sigma alpha a b : ℝ} {rho : ℂ}
    (hX : 1 ≤ X) (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (hmem : rho ∈ carlsonDetectorRectangle sigma alpha a b) :
    MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
        (carlsonDetectorRectangle sigma alpha a b) rho =
      (analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho : ℤ) := by
  have hdetector : AnalyticAt ℂ (regularizedCarlsonZeroDetector X) rho :=
    analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X rho hrho.2.1
  have hzeta_pos : 0 < analyticOrderNatAt riemannZeta rho :=
    ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
      (by
        intro hone
        have hre := congrArg Complex.re hone
        simp at hre
        linarith [hrho.2.2]) hrho.1
  have hdetector_pos :
      0 < analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho :=
    hzeta_pos.trans_le
      (analyticOrderNatAt_riemannZeta_le_regularizedCarlsonZeroDetector
        hX hrho)
  have hdetector_order_ne_top :
      analyticOrderAt (regularizedCarlsonZeroDetector X) rho ≠ ⊤ := by
    intro htop
    have hzero :
        analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho = 0 := by
      simp [analyticOrderNatAt, htop]
    omega
  rw [MeromorphicOn.divisor_apply
      (meromorphic_regularizedCarlsonZeroDetector X).meromorphicOn hmem,
    hdetector.meromorphicOrderAt_eq]
  have horder := Nat.cast_analyticOrderNatAt hdetector_order_ne_top
  rw [← horder]
  simp

/-- Every zeta zero counted by `zeroDensityCount sigma T` is a zero of the
pole-free Carlson detector inside `[sigma, 1] × [0, T]`, with at least the
same multiplicity. -/
theorem zeroDensityCount_le_regularizedCarlsonDetectorRectangleZeroCount
    {X : ℕ} (hX : 1 ≤ X) (sigma T : ℝ) :
    ZeroDensity.zeroDensityCount sigma T ≤
      regularizedCarlsonDetectorRectangleZeroCount X sigma 1 0 T := by
  classical
  let K : Set ℂ := carlsonDetectorRectangle sigma 1 0 T
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X) K
  let S := ZeroDensity.zeroDensityZerosFinset sigma T
  let P := regularizedCarlsonDetectorRectangleDivisorSupport X sigma 1 0 T
  have hS_subset : S ⊆ P := by
    intro rho hrhoS
    have hrho := ZeroDensity.mem_zeroDensityZerosFinset.mp hrhoS
    have hmem : rho ∈ K := by
      dsimp [K, carlsonDetectorRectangle]
      simp only [Complex.mem_reProdIm, Set.mem_Icc]
      exact ⟨⟨hrho.2.2.2.le, hrho.1.2.2.le⟩,
        ⟨hrho.2.1.le, hrho.2.2.1⟩⟩
    have hdivisor : D rho =
        (analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho : ℤ) := by
      dsimp [D, K]
      exact divisor_regularizedCarlsonZeroDetector_eq_analyticOrderNatAt
        hX hrho.1 hmem
    have hpositive :
        0 < analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho :=
      (ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        (by
          intro hone
          have hre := congrArg Complex.re hone
          simp at hre
          linarith [hrho.1.2.2]) hrho.1.1).trans_le
        (analyticOrderNatAt_riemannZeta_le_regularizedCarlsonZeroDetector
          hX hrho.1)
    dsimp [P, regularizedCarlsonDetectorRectangleDivisorSupport]
    apply (D.finiteSupport
      (isCompact_carlsonDetectorRectangle sigma 1 0 T)).mem_toFinset.mpr
    simp only [Function.mem_support]
    rw [hdivisor]
    exact_mod_cast hpositive.ne'
  calc
    ZeroDensity.zeroDensityCount sigma T =
        ∑ rho ∈ S, analyticOrderNatAt riemannZeta rho := rfl
    _ ≤ ∑ rho ∈ S, (D rho).toNat := by
      apply Finset.sum_le_sum
      intro rho hrhoS
      have hrho := ZeroDensity.mem_zeroDensityZerosFinset.mp hrhoS
      have hmem : rho ∈ K := by
        dsimp [K, carlsonDetectorRectangle]
        simp only [Complex.mem_reProdIm, Set.mem_Icc]
        exact ⟨⟨hrho.2.2.2.le, hrho.1.2.2.le⟩,
          ⟨hrho.2.1.le, hrho.2.2.1⟩⟩
      have hdivisor : D rho =
          (analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho : ℤ) := by
        dsimp [D, K]
        exact divisor_regularizedCarlsonZeroDetector_eq_analyticOrderNatAt
          hX hrho.1 hmem
      rw [hdivisor, Int.toNat_natCast]
      exact
        analyticOrderNatAt_riemannZeta_le_regularizedCarlsonZeroDetector
          hX hrho.1
    _ ≤ ∑ z ∈ P, (D z).toNat :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_subset
        (fun _ _ _ => Nat.zero_le _)
    _ = regularizedCarlsonDetectorRectangleZeroCount X sigma 1 0 T := rfl

end CarlsonZeroDensity
end PrimeNumberTheorem
