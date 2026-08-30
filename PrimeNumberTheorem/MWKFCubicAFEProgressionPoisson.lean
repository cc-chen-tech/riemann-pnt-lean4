import PrimeNumberTheorem.MWKFCubicAFEPhysicalPoisson

open Complex Set
open scoped FourierTransform

namespace PrimeNumberTheorem.MWKFCubic

/-!
# From the actual positive progression to the bilateral Poisson lattice

Every nonzero term on the bilateral lattice lies in the positive-index
domain, by the cutoff's support condition. Exact integer inverses then
identify it with an original positive progression term. No rounding or
coprimality restriction on the shift is introduced.
-/

def cubicAFEProgressionLattice (d e : ℕ) (δ j : ℤ) : ℤ :=
  -δ * Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e) +
    ((e / Nat.gcd d e : ℕ) : ℤ) * j

def cubicAFEProgressionLatticeIndex (d e : ℕ) (δ : ℤ) (m : ℕ) : ℤ :=
  ((m : ℤ) - (-δ * Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e))) /
    ((e / Nat.gcd d e : ℕ) : ℤ)

private theorem reduced_modulus_pos {d e : ℕ} (he : 0 < e) : 0 < e / Nat.gcd d e := by
  have hq : 0 < Nat.gcd d e := by
    simpa only [Nat.gcd_comm] using Nat.gcd_pos_of_pos_left d he
  have heq := (gcd_extraction hq.ne').2.1
  apply Nat.pos_of_ne_zero
  intro hz
  rw [hz, mul_zero] at heq
  exact he.ne' heq

theorem cubicAFEProgressionLattice_injective {d e : ℕ} (he : 0 < e) (δ : ℤ) :
    Function.Injective (cubicAFEProgressionLattice d e δ) := by
  have hs0 : ((e / Nat.gcd d e : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (reduced_modulus_pos (d := d) he).ne'
  intro i j h
  apply mul_left_cancel₀ hs0
  exact add_left_cancel h

theorem cubicAFEProgressionLattice_index {d e : ℕ} (he : 0 < e) {δ : ℤ} {m : ℕ}
    (hm : m ∈ cubicAFEProgression d e δ) :
    cubicAFEProgressionLattice d e δ (cubicAFEProgressionLatticeIndex d e δ m) = (m : ℤ) := by
  have hc := ((cubicAFEProgression_mem_iff_residue he δ m).mp hm).2.2
  have hdiv := hc.symm.dvd
  unfold cubicAFEProgressionLattice cubicAFEProgressionLatticeIndex
  rw [mul_comm (((e / Nat.gcd d e : ℕ) : ℤ)), Int.ediv_mul_cancel hdiv]
  ring

theorem cubicAFEProgressionLattice_toNat_mem {d e : ℕ} (he : 0 < e) {δ j : ℤ}
    (hj : (cubicAFEProgressionLattice d e δ j : ℝ) ∈ cubicAFEProgressionDomain d e δ) :
    (cubicAFEProgressionLattice d e δ j).toNat ∈ cubicAFEProgression d e δ := by
  have hjZ : 0 < cubicAFEProgressionLattice d e δ j := by exact_mod_cast hj.1
  have hn := Int.toNat_of_nonneg hjZ.le
  apply (cubicAFEProgression_mem_iff_residue he δ _).mpr
  refine ⟨Int.pos_iff_toNat_pos.mp hjZ, ?_, ?_⟩
  · unfold cubicAFEProgressionNumerator
    rw [hn]
    have hnumR : (0 : ℝ) < ((δ + cubicAFEProgressionLattice d e δ j *
        ((d / Nat.gcd d e : ℕ) : ℤ) : ℤ) : ℝ) := by
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hj.2
    exact_mod_cast hnumR
  · rw [hn]
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-j, by unfold cubicAFEProgressionLattice; ring⟩

/-- The cutoff vanishes at every forbidden real-domain point. In
particular, adding nonpositive lattice indices never inserts a spurious
`toNat = 0` contribution. -/
theorem cubicAFEProgressionCutoffSummand_eq_zero_of_not_domain
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} {δ : ℤ}
    (χ : CubicProgressionCutoff d e δ) (t : ℝ) {x : ℝ}
    (hx : x ∉ cubicAFEProgressionDomain d e δ) :
    cubicAFEProgressionCutoffSummand W T X V χ t x = 0 := by
  have hχ : χ x = 0 := image_eq_zero_of_notMem_tsupport
    (fun h ↦ hx (χ.support_subset h))
  simp only [cubicAFEProgressionCutoffSummand, hχ, Complex.ofReal_zero, zero_mul]

/-- Actual positive progression series equals the bilateral lattice series.
The index map is injective and contains every nonzero lattice term; this is
an exact reindexing, not an estimate or a truncation. -/
theorem tsum_cubicAFEProgressionCutoff_eq_lattice
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e) {δ : ℤ}
    (χ : CubicProgressionCutoff d e δ) (t : ℝ) :
    (∑' m : cubicAFEProgression d e δ, cubicAFEProgressionCutoffSummand W T X V χ t m.val) =
      ∑' j : ℤ, cubicAFEProgressionCutoffSummand W T X V χ t
        (cubicAFEProgressionLattice d e δ j : ℝ) := by
  let K := cubicAFEProgressionCutoffSummand W T X V χ t
  let f : ℤ → ℂ := fun j ↦ K (cubicAFEProgressionLattice d e δ j : ℝ)
  let g : cubicAFEProgression d e δ → ℤ := fun m ↦ cubicAFEProgressionLatticeIndex d e δ m.val
  have hindex : ∀ m : cubicAFEProgression d e δ,
      cubicAFEProgressionLattice d e δ (g m) = (m.val : ℤ) :=
    fun m ↦ cubicAFEProgressionLattice_index he m.property
  have hginj : Function.Injective g := by
    intro m n h
    apply Subtype.ext
    have hZ : (m.val : ℤ) = (n.val : ℤ) := by rw [← hindex m, ← hindex n, h]
    exact_mod_cast hZ
  have hsupport : Function.support f ⊆ range g := by
    intro j hj
    have hdom : (cubicAFEProgressionLattice d e δ j : ℝ) ∈
        cubicAFEProgressionDomain d e δ := by
      by_contra hn
      exact hj (cubicAFEProgressionCutoffSummand_eq_zero_of_not_domain W T X V χ t hn)
    have hpos : 0 < cubicAFEProgressionLattice d e δ j := by exact_mod_cast hdom.1
    let m : cubicAFEProgression d e δ :=
      ⟨(cubicAFEProgressionLattice d e δ j).toNat, cubicAFEProgressionLattice_toNat_mem he hdom⟩
    refine ⟨m, ?_⟩
    apply cubicAFEProgressionLattice_injective he δ
    rw [hindex m]
    exact Int.toNat_of_nonneg hpos.le
  calc
    (∑' m : cubicAFEProgression d e δ, K m.val) = ∑' m : cubicAFEProgression d e δ, f (g m) := by
      apply tsum_congr
      intro m
      dsimp only [f]
      rw [hindex m]
      simp only [Int.cast_natCast]
    _ = ∑' j : ℤ, f j := hginj.tsum_eq hsupport

/-- Poisson for the original complete shifted-fiber summand, with the
physical cutoff retained and both sides now connected by exact reindexing. -/
theorem cubicAFEShiftFiberCutoff_poisson
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    {δ : ℤ} (χ : CubicProgressionCutoff d e δ) (t : ℝ) (hX : 1 / 2 < X) :
    (∑' p : cubicAFEShiftFiber d e δ,
      (χ (p.val.1 + 1 : ℕ) : ℂ) * cubicAFECombinedSummandFinite W T X V d e t p.val) =
      (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∑' h : ℤ,
        𝓕 (cubicAFEProgressionCutoffSummand W T X V χ t)
          ((h : ℝ) / ((e / Nat.gcd d e : ℕ) : ℝ)) *
          Complex.exp (-2 * (Real.pi : ℂ) * I * (h : ℂ) * (δ : ℂ) *
            (Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e) : ℂ) /
              ((e / Nat.gcd d e : ℕ) : ℂ)) := by
  rw [tsum_cubicAFEShiftFiber_eq_progression (d := d) he δ
    (fun p : ℕ × ℕ ↦ (χ (p.1 + 1 : ℕ) : ℂ) *
      cubicAFECombinedSummandFinite W T X V d e t p)]
  have hterms :
      (fun m : cubicAFEProgression d e δ ↦
        (χ ((cubicAFEProgressionPair d e δ m.val).1 + 1 : ℕ) : ℂ) *
          cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val)) =
      fun m : cubicAFEProgression d e δ ↦ cubicAFEProgressionCutoffSummand W T X V χ t m.val := by
    funext m
    rw [(cubicAFEProgressionPair_succ he m.property).1,
      cubicAFEProgressionCutoffSummand_eq_discrete W T X V hd he χ t m.property]
  rw [hterms, tsum_cubicAFEProgressionCutoff_eq_lattice W T X V he χ t]
  simpa only [cubicAFEProgressionLattice, Int.cast_add, Int.cast_mul, Int.cast_neg,
    Int.cast_natCast] using cubicAFEProgressionCutoff_poisson_inverseResidue W T X V hd he χ t hX

end PrimeNumberTheorem.MWKFCubic
