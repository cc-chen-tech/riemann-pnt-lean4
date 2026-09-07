import HardyTheorem.SelbergMollifiedDualRational
import HardyTheorem.SelbergMollifiedGaussianPolynomial

/-!
# Polylogarithmic coprime-ray energy of the mollified dual AFE sum

If two raw pairs `(n,d)` and `(m,e)` have the same rational frequency, then
`n*e=m*d=:k`.  Their square-root majorant product is exactly `1/k`.
For fixed `k` there are at most `tau(k)^2` such ordered pairs, which is at
most the fourfold divisor function.  Discrete Abel summation therefore gives
an explicit `O(log^4(NX))` bound without any spectral input.
-/

open Complex MeasureTheory
open scoped BigOperators ArithmeticFunction
open PrimeNumberTheorem.CarlsonZeroDensity

namespace HardyTheorem

private noncomputable def selbergMollifiedDualCrossSupport
    (N X : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((selbergMollifiedDualSupport N X).product
    (selbergMollifiedDualSupport N X)).filter
      (fun pr => pr.1.1 * pr.2.2 = pr.2.1 * pr.1.2)

private theorem dualRationalKey_eq_iff_cross
    {N X : ℕ} {p r : ℕ × ℕ}
    (hp : p ∈ selbergMollifiedDualSupport N X)
    (hr : r ∈ selbergMollifiedDualSupport N X) :
    selbergMollifiedDualRationalKey p =
        selbergMollifiedDualRationalKey r ↔
      p.1 * r.2 = r.1 * p.2 := by
  rcases Finset.mem_product.mp hp with ⟨hpn, hpd⟩
  rcases Finset.mem_product.mp hr with ⟨hrn, hrd⟩
  have hpd0 : p.2 ≠ 0 := Nat.ne_of_gt
    (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hpd).1)
  have hrd0 : r.2 ≠ 0 := Nat.ne_of_gt
    (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hrd).1)
  unfold selbergMollifiedDualRationalKey
  rw [div_eq_div_iff]
  · norm_cast
  · exact_mod_cast hpd0
  · exact_mod_cast hrd0

private theorem sum_sq_dualRationalMass_eq_crossSupport
    (N X : ℕ) :
    (∑ q ∈ selbergMollifiedDualRationalSupport N X,
        (selbergMollifiedDualRationalMass N X q) ^ 2) =
      ∑ pr ∈ selbergMollifiedDualCrossSupport N X,
        selbergMollifiedDualMass X pr.1 *
          selbergMollifiedDualMass X pr.2 := by
  classical
  let P := selbergMollifiedDualSupport N X
  let Q := selbergMollifiedDualRationalSupport N X
  let key := selbergMollifiedDualRationalKey
  let mass := selbergMollifiedDualMass X
  have hmaps : ∀ p ∈ P, key p ∈ Q := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  calc
    (∑ q ∈ selbergMollifiedDualRationalSupport N X,
        (selbergMollifiedDualRationalMass N X q) ^ 2) =
      ∑ q ∈ Q,
        (∑ p ∈ P.filter (fun p => key p = q), mass p) ^ 2 := by rfl
    _ = ∑ q ∈ Q,
        ∑ p ∈ P.filter (fun p => key p = q),
          ∑ r ∈ P.filter (fun r => key r = q), mass p * mass r := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
    _ = ∑ q ∈ Q,
        ∑ p ∈ P.filter (fun p => key p = q),
          ∑ r ∈ P.filter (fun r => key r = key p), mass p * mass r := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = ∑ p ∈ P,
        ∑ r ∈ P.filter (fun r => key r = key p), mass p * mass r := by
      exact Finset.sum_fiberwise_of_maps_to hmaps
        (fun p => ∑ r ∈ P.filter (fun r => key r = key p), mass p * mass r)
    _ = ∑ p ∈ P, ∑ r ∈ P,
        if key r = key p then mass p * mass r else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_filter]
    _ = ∑ p ∈ P, ∑ r ∈ P,
        if p.1 * r.2 = r.1 * p.2 then mass p * mass r else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro r hr
      have hiff := dualRationalKey_eq_iff_cross hp hr
      by_cases hcross : p.1 * r.2 = r.1 * p.2
      · have hkey : key r = key p := (hiff.mpr hcross).symm
        simp [hcross, hkey]
      · have hkey : key r ≠ key p := by
          intro h
          exact hcross (hiff.mp h.symm)
        simp [hcross, hkey]
    _ = ∑ pr ∈ P.product P,
        if pr.1.1 * pr.2.2 = pr.2.1 * pr.1.2
        then mass pr.1 * mass pr.2 else 0 :=
      (Finset.sum_product P P (fun pr =>
        if pr.1.1 * pr.2.2 = pr.2.1 * pr.1.2
        then mass pr.1 * mass pr.2 else 0)).symm
    _ = ∑ pr ∈ (P.product P).filter
          (fun pr => pr.1.1 * pr.2.2 = pr.2.1 * pr.1.2),
        mass pr.1 * mass pr.2 := by
      rw [Finset.sum_filter]
    _ = _ := by rfl

private noncomputable def selbergMollifiedDualUnitMass
    (p : ℕ × ℕ) : ℝ :=
  (Real.sqrt p.1)⁻¹ * (Real.sqrt p.2)⁻¹

private theorem dualMass_le_unitMass
    {N X : ℕ} (hX : 2 ≤ X) {p : ℕ × ℕ}
    (hp : p ∈ selbergMollifiedDualSupport N X) :
    selbergMollifiedDualMass X p ≤ selbergMollifiedDualUnitMass p := by
  rcases Finset.mem_product.mp hp with ⟨hn, hd⟩
  have hcoeff := abs_selbergMoebiusCoeff_le_one hX
    (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2
  unfold selbergMollifiedDualMass selbergMollifiedDualUnitMass
  have hfactor : 0 ≤ (Real.sqrt p.1)⁻¹ * (Real.sqrt p.2)⁻¹ := by
    positivity
  calc
    |selbergMoebiusCoeff X p.2| * (Real.sqrt p.1)⁻¹ *
        (Real.sqrt p.2)⁻¹ =
      |selbergMoebiusCoeff X p.2| *
        ((Real.sqrt p.1)⁻¹ * (Real.sqrt p.2)⁻¹) := by ring
    _ ≤ 1 * ((Real.sqrt p.1)⁻¹ * (Real.sqrt p.2)⁻¹) :=
      mul_le_mul_of_nonneg_right hcoeff hfactor
    _ = _ := one_mul _

private theorem crossTerm_le_inv_key
    {N X k : ℕ} (hX : 2 ≤ X)
    {pr : (ℕ × ℕ) × (ℕ × ℕ)}
    (hpr : pr ∈ selbergMollifiedDualCrossSupport N X)
    (hkey : pr.1.1 * pr.2.2 = k) :
    selbergMollifiedDualMass X pr.1 *
        selbergMollifiedDualMass X pr.2 ≤ (k : ℝ)⁻¹ := by
  rcases Finset.mem_filter.mp hpr with ⟨hprod, hcross⟩
  rcases Finset.mem_product.mp hprod with ⟨hp, hr⟩
  have hpBound := dualMass_le_unitMass hX hp
  have hrBound := dualMass_le_unitMass hX hr
  have hp0 : 0 ≤ selbergMollifiedDualMass X pr.1 := by
    unfold selbergMollifiedDualMass
    positivity
  have hr0 : 0 ≤ selbergMollifiedDualMass X pr.2 := by
    unfold selbergMollifiedDualMass
    positivity
  have hunit0 : 0 ≤ selbergMollifiedDualUnitMass pr.1 := by
    unfold selbergMollifiedDualUnitMass
    positivity
  have hprodBound :
      selbergMollifiedDualMass X pr.1 *
          selbergMollifiedDualMass X pr.2 ≤
        selbergMollifiedDualUnitMass pr.1 *
          selbergMollifiedDualUnitMass pr.2 :=
    mul_le_mul hpBound hrBound hr0 hunit0
  have hkey' : pr.2.1 * pr.1.2 = k := hcross.symm.trans hkey
  have hsqrtLeft :
      Real.sqrt pr.1.1 * Real.sqrt pr.2.2 = Real.sqrt k := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ pr.1.1)]
    exact congrArg Real.sqrt (by exact_mod_cast hkey)
  have hsqrtRight :
      Real.sqrt pr.2.1 * Real.sqrt pr.1.2 = Real.sqrt k := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ pr.2.1)]
    exact congrArg Real.sqrt (by exact_mod_cast hkey')
  calc
    selbergMollifiedDualMass X pr.1 *
        selbergMollifiedDualMass X pr.2 ≤
      selbergMollifiedDualUnitMass pr.1 *
        selbergMollifiedDualUnitMass pr.2 := hprodBound
    _ = (Real.sqrt pr.1.1 * Real.sqrt pr.2.2)⁻¹ *
          (Real.sqrt pr.2.1 * Real.sqrt pr.1.2)⁻¹ := by
      unfold selbergMollifiedDualUnitMass
      rw [mul_inv, mul_inv]
      ring
    _ = (Real.sqrt k)⁻¹ * (Real.sqrt k)⁻¹ := by
      rw [hsqrtLeft, hsqrtRight]
    _ = (k : ℝ)⁻¹ := by
      rw [← pow_two, inv_pow, Real.sq_sqrt (by positivity)]

private theorem crossFiber_card_le_divisors_sq
    {N X k : ℕ} (hk : 0 < k) :
    ((selbergMollifiedDualCrossSupport N X).filter
        (fun pr => pr.1.1 * pr.2.2 = k)).card ≤
      k.divisorsAntidiagonal.card ^ 2 := by
  classical
  let F := (selbergMollifiedDualCrossSupport N X).filter
    (fun pr => pr.1.1 * pr.2.2 = k)
  let D := k.divisorsAntidiagonal.product k.divisorsAntidiagonal
  let g : ((ℕ × ℕ) × (ℕ × ℕ)) →
      ((ℕ × ℕ) × (ℕ × ℕ)) := fun pr =>
    ((pr.1.1, pr.2.2), (pr.2.1, pr.1.2))
  have hmaps : Set.MapsTo g (F : Set _) (D : Set _) := by
    intro pr hpr
    have hprF := Finset.mem_filter.mp hpr
    have hcross := (Finset.mem_filter.mp hprF.1).2
    apply Finset.mem_product.mpr
    constructor
    · rw [Nat.mem_divisorsAntidiagonal]
      exact ⟨hprF.2, hk.ne'⟩
    · rw [Nat.mem_divisorsAntidiagonal]
      exact ⟨hcross.symm.trans hprF.2, hk.ne'⟩
  have hinj : Set.InjOn g (F : Set _) := by
    intro p hp r hr heq
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun z => z.1.1) heq
      · exact congrArg (fun z => z.2.2) heq
    · apply Prod.ext
      · exact congrArg (fun z => z.2.1) heq
      · exact congrArg (fun z => z.1.2) heq
  calc
    F.card ≤ D.card := Finset.card_le_card_of_injOn g hmaps hinj
    _ = k.divisorsAntidiagonal.card ^ 2 := by
      simp [D, pow_two]

private theorem sum_crossFiber_le_fourfold_inv
    {N X k : ℕ} (hX : 2 ≤ X) (hk : 0 < k) :
    (∑ pr ∈ (selbergMollifiedDualCrossSupport N X).filter
        (fun pr => pr.1.1 * pr.2.2 = k),
      selbergMollifiedDualMass X pr.1 *
        selbergMollifiedDualMass X pr.2) ≤
      (fourfoldDivisorCount k : ℝ) * (k : ℝ)⁻¹ := by
  let F := (selbergMollifiedDualCrossSupport N X).filter
    (fun pr => pr.1.1 * pr.2.2 = k)
  have hterm :
      (∑ pr ∈ F, selbergMollifiedDualMass X pr.1 *
          selbergMollifiedDualMass X pr.2) ≤
        ∑ _pr ∈ F, (k : ℝ)⁻¹ := by
    apply Finset.sum_le_sum
    intro pr hpr
    have hpr' : pr ∈ (selbergMollifiedDualCrossSupport N X).filter
        (fun pr => pr.1.1 * pr.2.2 = k) := by
      simpa only [F] using hpr
    exact crossTerm_le_inv_key hX (Finset.mem_filter.mp hpr').1
      (Finset.mem_filter.mp hpr').2
  have hcard := crossFiber_card_le_divisors_sq (N := N) (X := X) hk
  have hfour := card_divisorsAntidiagonal_sq_le_fourfoldDivisorCount hk.ne'
  calc
    (∑ pr ∈ F, selbergMollifiedDualMass X pr.1 *
        selbergMollifiedDualMass X pr.2) ≤
      ∑ _pr ∈ F, (k : ℝ)⁻¹ := hterm
    _ = (F.card : ℝ) * (k : ℝ)⁻¹ := by simp
    _ ≤ (k.divisorsAntidiagonal.card ^ 2 : ℕ) * (k : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ ≤ (fourfoldDivisorCount k : ℝ) * (k : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfour) (by positivity)

/-- The complete absolute coprime-ray energy is polylogarithmic. -/
theorem sum_sq_selbergMollifiedDualRationalMass_le
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) :
    (∑ q ∈ selbergMollifiedDualRationalSupport N X,
        (selbergMollifiedDualRationalMass N X q) ^ 2) ≤
      2 * (1 + Real.log (N * X)) ^ 4 := by
  classical
  let C := selbergMollifiedDualCrossSupport N X
  let K := Finset.Icc 1 (N * X)
  let key : ((ℕ × ℕ) × (ℕ × ℕ)) → ℕ :=
    fun pr => pr.1.1 * pr.2.2
  let term : ((ℕ × ℕ) × (ℕ × ℕ)) → ℝ :=
    fun pr => selbergMollifiedDualMass X pr.1 *
      selbergMollifiedDualMass X pr.2
  have hmaps : ∀ pr ∈ C, key pr ∈ K := by
    intro pr hpr
    have hprod := (Finset.mem_filter.mp hpr).1
    rcases Finset.mem_product.mp hprod with ⟨hp, hr⟩
    rcases Finset.mem_product.mp hp with ⟨hpn, hpd⟩
    rcases Finset.mem_product.mp hr with ⟨hrn, hrd⟩
    exact Finset.mem_Icc.mpr ⟨
      Nat.mul_pos (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hpn).1)
        (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hrd).1),
      Nat.mul_le_mul (Finset.mem_Icc.mp hpn).2 (Finset.mem_Icc.mp hrd).2⟩
  rw [sum_sq_dualRationalMass_eq_crossSupport]
  change (∑ pr ∈ C, term pr) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps term]
  calc
    (∑ k ∈ K, ∑ pr ∈ C.filter (fun pr => key pr = k), term pr) ≤
      ∑ k ∈ K, (fourfoldDivisorCount k : ℝ) * (k : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro k hk
        exact sum_crossFiber_le_fourfold_inv hX
          (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hk).1)
    _ ≤ 2 * (1 + Real.log (N * X)) ^ 4 := by
      simpa only [K, Nat.cast_mul] using
        (fourfoldDivisor_inv_sum_le_two_mul_log_pow_four
          (Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hN))
              (Nat.ne_of_gt (Nat.zero_lt_of_lt hX)))))

/-- Fully closed Gaussian mean square for the finite dual AFE sum times the
linear Selberg mollifier. -/
theorem integral_gaussian_normSq_selbergMollifiedDualPolynomial_le
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X)
    {Delta : ℝ} (hDelta : 2 * ((N * X : ℕ) : ℝ) ≤ Delta)
    (w : ℝ) :
    (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq (selbergMollifiedDualPolynomial N X t)) ≤
      Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
        MathlibAux.gaussianBucketSchurConstant *
          (2 * (1 + Real.log (N * X)) ^ 4) := by
  have hbase :=
    integral_gaussian_normSq_selbergMollifiedDualPolynomial_le_rationalMassEnergy
      hN (by omega) hDelta w
  refine hbase.trans ?_
  have henergy := sum_sq_selbergMollifiedDualRationalMass_le hN hX
  have hfactor :
      0 ≤ Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
        MathlibAux.gaussianBucketSchurConstant :=
    mul_nonneg (Real.sqrt_nonneg _)
      MathlibAux.gaussianBucketSchurConstant_pos.le
  exact mul_le_mul_of_nonneg_left henergy hfactor

end HardyTheorem
