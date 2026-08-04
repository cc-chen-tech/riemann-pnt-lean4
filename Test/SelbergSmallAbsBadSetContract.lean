import HardyTheorem.SelbergSmallAbsBadSet

open MeasureTheory Set

namespace Test.SelbergSmallAbsBadSetContract

example {Q : ℝ → ℂ} {absMass : ℝ → ℝ} {A B H eta R M : ℝ}
    (hthreshold : 0 < H - eta - R)
    (hlower : ∀ t ∈ Icc A B, H - ‖Q t‖ - R ≤ absMass t)
    (hQint : Integrable (fun t => Complex.normSq (Q t))
      (volume.restrict (Icc A B)))
    (hQbound :
      (∫ t, Complex.normSq (Q t) ∂volume.restrict (Icc A B)) ≤ M) :
    volume.real ({t | absMass t ≤ eta} ∩ Icc A B) ≤
      M / (H - eta - R) ^ 2 :=
  HardyTheorem.volume_smallMassStarts_inter_Icc_le_of_L2
    hthreshold hlower hQint hQbound

example {X N : ℕ} {A B H eta R M : ℝ}
    (hthreshold : 0 < H - eta - R)
    (hlower : ∀ t ∈ Icc A B,
      H - ‖HardyTheorem.selbergMollifiedShortDirichletPolynomial H N X t‖ - R ≤
        HardyTheorem.selbergMoebiusAbsShortIntegral X H t)
    (hQint : Integrable
      (fun t => Complex.normSq
        (HardyTheorem.selbergMollifiedShortDirichletPolynomial H N X t))
      (volume.restrict (Icc A B)))
    (hQbound :
      (∫ t, Complex.normSq
          (HardyTheorem.selbergMollifiedShortDirichletPolynomial H N X t)
        ∂volume.restrict (Icc A B)) ≤ M) :
    volume.real
        (HardyTheorem.selbergSmallAbsoluteMassStarts X H eta ∩ Icc A B) ≤
      M / (H - eta - R) ^ 2 :=
  HardyTheorem.volume_selbergSmallAbsoluteMassStarts_inter_Icc_le_of_shortDirichletL2
    hthreshold hlower hQint hQbound

end Test.SelbergSmallAbsBadSetContract
