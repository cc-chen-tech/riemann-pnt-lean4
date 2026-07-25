import ZeroFreeRegion.VinogradovKorobov.VinogradovTailRefinement

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The representative of a residue class in `{1, ..., p}`.  The zero class
is represented by `p`, which makes every residue fiber a one-based affine
progression without a separate missing first term. -/
def vinogradovPositiveResidueRepresentative
    (p : ℕ) (rho : ZMod p) : ℕ :=
  if rho.val = 0 then p else rho.val

/-- The exact number of integers in `{1, ..., Y}` with residue `rho` modulo
`p`, written using the positive representative in `{1, ..., p}`. -/
def vinogradovTailResidueLength
    (p Y : ℕ) (rho : ZMod p) : ℕ :=
  (Y + p - vinogradovPositiveResidueRepresentative p rho) / p

theorem vinogradovPositiveResidueRepresentative_pos
    (p : ℕ) [Fact p.Prime] (rho : ZMod p) :
    0 < vinogradovPositiveResidueRepresentative p rho := by
  by_cases hzero : rho.val = 0
  · simpa [vinogradovPositiveResidueRepresentative, hzero] using
      (Fact.out : p.Prime).pos
  · simpa [vinogradovPositiveResidueRepresentative, hzero] using
      Nat.pos_of_ne_zero hzero

theorem vinogradovPositiveResidueRepresentative_le
    (p : ℕ) [Fact p.Prime] (rho : ZMod p) :
    vinogradovPositiveResidueRepresentative p rho ≤ p := by
  by_cases hzero : rho.val = 0
  · simp [vinogradovPositiveResidueRepresentative, hzero]
  · simpa [vinogradovPositiveResidueRepresentative, hzero] using
      Nat.le_of_lt rho.val_lt

@[simp] theorem vinogradovPositiveResidueRepresentative_cast
    (p : ℕ) [Fact p.Prime] (rho : ZMod p) :
    ((vinogradovPositiveResidueRepresentative p rho : ℕ) : ZMod p) = rho := by
  by_cases hzero : rho.val = 0
  · apply ZMod.val_injective
    simp [vinogradovPositiveResidueRepresentative, hzero]
  · apply ZMod.val_injective
    simp [vinogradovPositiveResidueRepresentative, hzero]

/-- The `q`-th member of a residue fiber, as a zero-based index in `Fin Y`.
Its represented one-based integer is `r + p*q`, where `r` is the positive
residue representative. -/
def vinogradovTailResidueIndex
    (p Y : ℕ) [Fact p.Prime] (rho : ZMod p)
    (q : Fin (vinogradovTailResidueLength p Y rho)) : Fin Y := by
  let r := vinogradovPositiveResidueRepresentative p rho
  have hrpos : 0 < r :=
    vinogradovPositiveResidueRepresentative_pos p rho
  have hrle : r ≤ p :=
    vinogradovPositiveResidueRepresentative_le p rho
  have hqle :
      q.val + 1 ≤ vinogradovTailResidueLength p Y rho :=
    Nat.succ_le_iff.mpr q.isLt
  have hdiv :
      vinogradovTailResidueLength p Y rho * p ≤ Y + p - r := by
    exact Nat.div_mul_le_self (Y + p - r) p
  have hmul :
      (q.val + 1) * p ≤
        vinogradovTailResidueLength p Y rho * p :=
    Nat.mul_le_mul_right p hqle
  refine ⟨r + p * q.val - 1, ?_⟩
  have hbound : r + p * q.val ≤ Y := by
    have hrle' : r ≤ Y + p := hrle.trans (Nat.le_add_left p Y)
    have hsub : Y + p - r + r = Y + p :=
      Nat.sub_add_cancel hrle'
    have hproduct : (q.val + 1) * p = p * q.val + p := by ring
    dsimp [vinogradovTailResidueLength, r] at hdiv
    have hN : (q.val + 1) * p ≤ Y + p - r :=
      hmul.trans hdiv
    have hNadd := Nat.add_le_add_right hN r
    rw [hproduct, hsub] at hNadd
    have hreorder :
        p * q.val + p + r = (r + p * q.val) + p := by ring
    rw [hreorder] at hNadd
    exact Nat.le_of_add_le_add_right hNadd
  omega

@[simp] theorem vinogradovTailResidueIndex_val_add_one
    (p Y : ℕ) [Fact p.Prime] (rho : ZMod p)
    (q : Fin (vinogradovTailResidueLength p Y rho)) :
    (vinogradovTailResidueIndex p Y rho q).val + 1 =
      vinogradovPositiveResidueRepresentative p rho + p * q.val := by
  unfold vinogradovTailResidueIndex
  change
    (vinogradovPositiveResidueRepresentative p rho + p * q.val - 1) + 1 =
      vinogradovPositiveResidueRepresentative p rho + p * q.val
  have hrpos :=
    vinogradovPositiveResidueRepresentative_pos p rho
  omega

theorem vinogradovTailResidueIndex_mem
    (p Y : ℕ) [Fact p.Prime] (rho : ZMod p)
    (q : Fin (vinogradovTailResidueLength p Y rho)) :
    vinogradovTailResidueIndex p Y rho q ∈
      vinogradovResidueClassFinset p Y rho := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [mem_vinogradovResidueClassFinset,
    vinogradovTailResidueIndex_val_add_one]
  simp [Nat.cast_add, Nat.cast_mul]

theorem exists_vinogradovTailResidueIndex_eq_of_mem
    (p Y : ℕ) [Fact p.Prime] (rho : ZMod p) (n : Fin Y)
    (hn : n ∈ vinogradovResidueClassFinset p Y rho) :
    ∃ q : Fin (vinogradovTailResidueLength p Y rho),
      vinogradovTailResidueIndex p Y rho q = n := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let r := vinogradovPositiveResidueRepresentative p rho
  let m := n.val + 1
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hrpos : 0 < r :=
    vinogradovPositiveResidueRepresentative_pos p rho
  have hrle : r ≤ p :=
    vinogradovPositiveResidueRepresentative_le p rho
  have hmpos : 0 < m := by simp [m]
  have hmle : m ≤ Y := by
    dsimp [m]
    exact Nat.succ_le_iff.mpr n.isLt
  have hcast : (m : ZMod p) = rho := by
    simpa [m] using
      (mem_vinogradovResidueClassFinset p Y rho n).mp hn
  have hrem : m % p = rho.val := by
    have hval := congrArg ZMod.val hcast
    simpa [ZMod.val_natCast] using hval
  obtain ⟨q, hmq⟩ : ∃ q : ℕ, m = r + p * q := by
    by_cases hzero : rho.val = 0
    · have hr : r = p := by
        simp [r, vinogradovPositiveResidueRepresentative, hzero]
      have hmrem : m % p = 0 := hrem.trans hzero
      have hpdvd : p ∣ m := Nat.dvd_of_mod_eq_zero hmrem
      have hplem : p ≤ m := Nat.le_of_dvd hmpos hpdvd
      have hdivpos : 0 < m / p := Nat.div_pos hplem hp
      refine ⟨m / p - 1, ?_⟩
      have hdecomp : p * (m / p) = m := by
        simpa [hmrem] using Nat.div_add_mod m p
      have hpred : m / p - 1 + 1 = m / p :=
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hdivpos.ne')
      rw [hr]
      calc
        m = p * (m / p) := hdecomp.symm
        _ = p * ((m / p - 1) + 1) := by rw [hpred]
        _ = p + p * (m / p - 1) := by ring
    · have hr : r = rho.val := by
        simp [r, vinogradovPositiveResidueRepresentative, hzero]
      refine ⟨m / p, ?_⟩
      have hdecomp : p * (m / p) + m % p = m :=
        Nat.div_add_mod m p
      rw [hrem, ← hr] at hdecomp
      simpa [Nat.add_comm] using hdecomp.symm
  have hrle' : r ≤ Y + p := hrle.trans (Nat.le_add_left p Y)
  have hright : Y + p - r + r = Y + p :=
    Nat.sub_add_cancel hrle'
  have hleft : (q + 1) * p + r = m + p := by
    rw [hmq]
    ring
  have hmul : (q + 1) * p ≤ Y + p - r := by
    apply Nat.le_of_add_le_add_right (b := r)
    rw [hleft, hright]
    exact Nat.add_le_add_right hmle p
  have hqle :
      q + 1 ≤ vinogradovTailResidueLength p Y rho := by
    rw [vinogradovTailResidueLength]
    exact (Nat.le_div_iff_mul_le hp).mpr hmul
  let qfin : Fin (vinogradovTailResidueLength p Y rho) :=
    ⟨q, Nat.lt_iff_add_one_le.mpr hqle⟩
  refine ⟨qfin, ?_⟩
  apply Fin.ext
  dsimp [r, m] at hmq
  have hadd :
      (vinogradovTailResidueIndex p Y rho qfin).val + 1 =
        n.val + 1 := by
    rw [vinogradovTailResidueIndex_val_add_one]
    dsimp [qfin]
    exact hmq.symm
  omega

/-- The one-based progression enumerator is a bijection onto the chosen
residue fiber, including the shorter endpoint fibers when `p ∤ Y`. -/
theorem card_vinogradovResidueClassFinset_eq_tailResidueLength
    (p Y : ℕ) [Fact p.Prime] (rho : ZMod p) :
    (vinogradovResidueClassFinset p Y rho).card =
      vinogradovTailResidueLength p Y rho := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hcard :
      (Finset.univ :
          Finset (Fin (vinogradovTailResidueLength p Y rho))).card =
        (vinogradovResidueClassFinset p Y rho).card := by
    apply Finset.card_bij
      (fun q _ ↦ vinogradovTailResidueIndex p Y rho q)
    · intro q hq
      exact vinogradovTailResidueIndex_mem p Y rho q
    · intro q₁ hq₁ q₂ hq₂ heq
      apply Fin.ext
      have hval := congrArg (fun z : Fin Y ↦ z.val + 1) heq
      simp only [vinogradovTailResidueIndex_val_add_one] at hval
      have hmul :
          p * q₁.val = p * q₂.val :=
        Nat.add_left_cancel hval
      exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos hmul
    · intro n hn
      obtain ⟨q, hq⟩ :=
        exists_vinogradovTailResidueIndex_eq_of_mem p Y rho n hn
      exact ⟨q, Finset.mem_univ _, hq⟩
  simpa using hcard.symm

/-- The center shift that converts the `rho` fiber at scale `b` into a
one-based affine tail at scale `b + 1`. -/
def vinogradovTailResidueRefinedCenter
    (p b : ℕ) (eta : ℤ) (rho : ZMod p) : ℤ :=
  eta + (p : ℤ) ^ b *
    ((vinogradovPositiveResidueRepresentative p rho : ℕ) : ℤ) -
      (p : ℤ) ^ b * (p : ℤ)

theorem vinogradovMixedTailValue_tailResidueIndex
    (p b Y : ℕ) [Fact p.Prime] (eta : ℤ) (rho : ZMod p)
    (q : Fin (vinogradovTailResidueLength p Y rho)) :
    vinogradovMixedTailValue p b Y eta
        (vinogradovTailResidueIndex p Y rho q) =
      vinogradovMixedTailValue p (b + 1)
        (vinogradovTailResidueLength p Y rho)
        (vinogradovTailResidueRefinedCenter p b eta rho) q := by
  unfold vinogradovMixedTailValue vinogradovTailResidueRefinedCenter
  rw [vinogradovTailResidueIndex_val_add_one, pow_succ]
  push_cast
  ring

/-- Each endpoint-sensitive residue fiber is exactly a standard affine tail
Weyl sum at the next `p`-adic scale.  No divisibility hypothesis on `Y` and no
padding error are needed. -/
theorem vinogradovMixedTailResidueWeylSum_eq_refinedTailWeylSum
    (p B b k Y : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (eta : ℤ) (rho : ZMod p) (c : Fin k → ZMod (p ^ B)) :
    vinogradovMixedTailResidueWeylSum p B b k Y eta rho c =
      vinogradovIntWeylSum (p ^ B) k
        (vinogradovTailResidueLength p Y rho)
        (vinogradovMixedTailValue p (b + 1)
          (vinogradovTailResidueLength p Y rho)
          (vinogradovTailResidueRefinedCenter p b eta rho)) c := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  unfold vinogradovMixedTailResidueWeylSum
    vinogradovResidueClassSum vinogradovIntWeylSum
  symm
  apply Finset.sum_bij
      (fun q _ ↦ vinogradovTailResidueIndex p Y rho q)
  · intro q hq
    exact vinogradovTailResidueIndex_mem p Y rho q
  · intro q₁ hq₁ q₂ hq₂ heq
    apply Fin.ext
    have hval := congrArg (fun z : Fin Y ↦ z.val + 1) heq
    simp only [vinogradovTailResidueIndex_val_add_one] at hval
    have hmul :
        p * q₁.val = p * q₂.val :=
      Nat.add_left_cancel hval
    exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos hmul
  · intro n hn
    obtain ⟨q, hq⟩ :=
      exists_vinogradovTailResidueIndex_eq_of_mem p Y rho n hn
    exact ⟨q, Finset.mem_univ _, hq⟩
  · intro q hq
    rw [vinogradovMixedTailValue_tailResidueIndex]

/-- After exact residue reparameterization, the one-step conditioned moment is
the sum of ordinary affine tail moments at scale `b + 1`; the fiber lengths
record the endpoint imbalance exactly. -/
theorem normalizedVinogradovMixedTailOneStepRefinedNormMoment_eq_nextScale
    (p B b k s Y : ℕ) [Fact p.Prime] [NeZero (p ^ B)] (eta : ℤ) :
    normalizedVinogradovMixedTailOneStepRefinedNormMoment
        p B b k s Y eta =
      ∑ rho : ZMod p,
        normalizedVinogradovMixedTailNormMoment p B (b + 1) k s
          (vinogradovTailResidueLength p Y rho)
          (vinogradovTailResidueRefinedCenter p b eta rho) := by
  unfold normalizedVinogradovMixedTailOneStepRefinedNormMoment
    normalizedVinogradovMixedTailNormMoment
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro rho
  congr 1
  apply Fintype.sum_congr
  intro c
  rw [vinogradovMixedTailResidueWeylSum_eq_refinedTailWeylSum]

/-- A genuine one-digit tail recurrence: the scale-`b` normalized moment is
bounded by the sum of endpoint-sensitive scale-`b+1` moments, with only the
finite Holder factor from splitting into the `p` residue classes. -/
theorem normalizedVinogradovMixedTailNormMoment_le_nextScaleResidueSum
    (p B b k s Y : ℕ) [Fact p.Prime] [NeZero (p ^ B)]
    (hs : 0 < s) (eta : ℤ) :
    normalizedVinogradovMixedTailNormMoment p B b k s Y eta ≤
      (p : ℝ) ^ (2 * s - 1) *
        ∑ rho : ZMod p,
          normalizedVinogradovMixedTailNormMoment p B (b + 1) k s
            (vinogradovTailResidueLength p Y rho)
            (vinogradovTailResidueRefinedCenter p b eta rho) := by
  rw [← normalizedVinogradovMixedTailOneStepRefinedNormMoment_eq_nextScale]
  exact normalizedVinogradovMixedTailNormMoment_le_oneStepRefinement
    p B b k s Y hs eta

end

end ZeroFreeRegion.VinogradovKorobov
