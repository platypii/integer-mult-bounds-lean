module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedReplicaBoundaryFactory

/-! The physical factory adds only polynomial header and geometry work to the
existing numerical factor-construction bill. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {s : ℕ} [NeZero s]

theorem generatedReplicaBoundaryFactoryCost_controls_le (H : ReplicaHaloProblem s) (target : ℕ) {Z : ℕ}
    (hZ : 1 ≤ Z) (ht : H.t ≤ Z) (hP : 2^15*H.p ≤ Z) (hstage : H.stage+1 ≤ Z)
    (hq : H.precision ≤ Z) (hl : H.l ≤ Z) (hu : H.u ≤ Z)
    (hV : publicationGeometryWidth H.t H.band ≤ Z) :
    generatedReplicaBoundaryFactoryCost H target ≤
      constructedBoundaryFactorCost H.p H.u H.l s H.t H.origin (H.origin+H.span)
        (boundaryRecoveryTarget H.p target) H.rhsExp+10000*Z^2 := by
  have hs : s ≤ Z := H.s_lt_t.le.trans ht
  have hb : H.band ≤ Z := H.band_fit.trans hs
  have hab : H.origin+H.span ≤ Z := H.span_fit.trans hs
  have ha : H.origin ≤ Z := by omega
  have hspan : H.span ≤ Z := by omega
  have hN : (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card ≤ Z :=
    (show (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card ≤ s by
      simpa only [ZMod.card] using (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card_le_univ).trans hs
  have hmaster : replicaBoundaryFactoryMasterCost H ≤ 40*Z+41 := by
    unfold replicaBoundaryFactoryMasterCost
    simp only [List.ofFn_succ,List.ofFn_zero,List.sum_cons,List.sum_nil,masterHeaderValues]
    norm_num only [Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons]
    omega
  have hgeom : factoryGeometryCost H.origin (H.origin+H.span) (publicationGeometryWidth H.t H.band) ≤
      8*Z^2+42*Z+30 := by
    have hp := Nat.mul_le_mul ha (show 4*publicationGeometryWidth H.t H.band+10 ≤ 4*Z+10 by omega)
    have hp' := Nat.mul_le_mul hspan (show 4*publicationGeometryWidth H.t H.band+10 ≤ 4*Z+10 by omega)
    unfold factoryGeometryCost
    rw [Nat.add_sub_cancel_left]
    nlinarith only [hp,hp',ha,hab,hspan,hV]
  have hcontrols :
      (2*((haloBoundary s H.t H.band H.origin (H.origin+H.span)).card*
        publicationGeometryWidth H.t H.band+publicationGeometryWidth H.t H.band+
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)+7)+
      ((s+H.t+H.band+H.origin+(H.origin+H.span))*(4*publicationGeometryWidth H.t H.band+10)+
        56*publicationGeometryWidth H.t H.band+77) ≤ 22*Z^2+110*Z+84 := by
    have hprod := Nat.mul_le_mul hN hV
    have hprod' := Nat.mul_le_mul (show s+H.t+H.band+H.origin+(H.origin+H.span) ≤ 5*Z by omega)
      (show 4*publicationGeometryWidth H.t H.band+10 ≤ 4*Z+10 by omega)
    nlinarith only [hprod,hprod',hV,hN]
  have hsq : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  have hone : 1 ≤ Z^2 := Nat.one_le_pow _ _ hZ
  unfold generatedReplicaBoundaryFactoryCost prepareReplicaBoundaryFactoryCost installReplicaBoundaryFactoryCost
    replicaBoundaryFactoryCost generatePublicationWidthCost
  nlinarith only [hmaster,hgeom,hcontrols,ht,hb,hq,hV,hsq,hone]

end IntegerMultBounds.MathlibTM2.Cost
