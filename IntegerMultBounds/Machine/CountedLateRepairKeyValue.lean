import IntegerMultBounds.Machine.CountedLateRepairKeyRun
import IntegerMultBounds.Compact.LatePowerTwoBridges

/-! Semantic rank membership for the physically generated later key. -/
namespace IntegerMultBounds.Machine.CountedLateRepairKeyValue
noncomputable section
open CountedLateRepairKeyRun (V W U)
open IntegerMultBounds.Compact
open IntegerMultBounds.Compact.PowerTwo

theorem flag_rank (q b : ℕ) (hb : 1≤b) (hbq : b+3≤q) (X cs : List Bool)
    (j : ℕ) (hj : j<lateMi q b X) (hc : Counter.value cs=j) :
    CountedLateRepairKeyBank.fl q b (V q X cs) (W q b X cs) (U q b X cs) X =
      rankFlag (lateRankEquiv q b X) (lateBadSet q b X) j := by
  rw [rankFlag,dite_eq_left hj,late_rank_split q b X cs (by omega) j hj hc]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  have h := CountedLateRepairGuard.combined_iff_bad q b hb hbq
    (V q X cs) (W q b X cs) (U q b X cs) X
    (Gather.field_length _ _ _) (Gather.field_length _ _ _) (Gather.field_length _ _ _)
  simpa only [CountedLateRepairKeyBank.fl,lateBadSet,lateGood,earlyGood,controls,Bi,Li,List.length_map,lateAddr,addr,
    CountedLateRepairGuard.address,CountedGuardGadgetValue.address,V,W,U,Vw,Ww,Uw] using h

theorem bits_rank (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (X cs : List Bool)
    (j : ℕ) (hj : j<lateMi q b X) (hc : Counter.value cs=j) :
    CountedLateRepairKeyBank.bits q b hb hbq (V q X cs) (W q b X cs) (U q b X cs) X =
      rankKey (lateRankEquiv q b X) (lateSperm q b X) (lateTperm q b X)
        (X.length*q+X.length*b+X.length*b) j := by
  rw [rankKey,dite_eq_left hj,destRank,late_rank_split q b X cs (by omega) j hj hc,lateAddr_words]
  exact (late_destination_words q b hb hbq X (V q X cs) (W q b X cs) (U q b X cs)
    (by omega) (Gather.field_length _ _ _) (Gather.field_length _ _ _) (Gather.field_length _ _ _)).symm


end
end IntegerMultBounds.Machine.CountedLateRepairKeyValue
