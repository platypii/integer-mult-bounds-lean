module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunSpatialCouplingRows
public import IntegerMultBounds.NLogN.PhaseCellHaloCouplingBudget

/-! Exact branch counts in the executed ambient recovery loop. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Generated mask bits count ambient coordinates, with no signed-offset deduplication. -/
theorem couplingGuard_true_count {s t : ℕ} [NeZero s] (hst : s < t)
    (boundary : Bool) (band a b : ℕ) (hb : b ≤ s) :
    ((Finset.range s).filter (fun i => couplingSkipAt boundary s t band a b i = true)).card =
      (couplingZeroRows boundary s t band a b).card := by
  refine Finset.card_bij (fun i _ => (i : ZMod s)) ?_ ?_ ?_
  · intro i hi
    obtain ⟨hir,hflag⟩ := Finset.mem_filter.mp hi
    exact couplingSkipAt_sound hst boundary band a b i hb (Finset.mem_range.mp hir) hflag
  · intro i hi j hj he
    have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hv := congrArg (fun x : ZMod s => x.val) he
    simpa [ZMod.val_cast_of_lt hi',ZMod.val_cast_of_lt hj'] using hv
  · intro j hj
    refine ⟨j.val,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt j),?_⟩,by simp⟩
    have hmask := (recoveryGuardMaskAt_spec hst boundary band a b j.val hb (ZMod.val_lt j)).mpr (by simpa [couplingZeroRows] using hj)
    simpa [couplingSkipAt] using hmask

theorem packetSpatialGuardedLoopCost_counts {s t : ℕ} [NeZero s] (hst : s < t)
    (boundary : Bool) (P q w u band a b : ℕ) (hb : b ≤ s) :
    packetSpatialGuardedLoopCost boundary P q w s t u band a b s =
      (couplingZeroRows boundary s t band a b).card*zeroPacketSpatialCouplingRowCost P q w s t u band+
      (s-(couplingZeroRows boundary s t band a b).card)*packetSpatialCouplingRowCost P q w s t u band+
      s*(10*w+16)+2 := by
  let pred := fun i => couplingSkipAt boundary s t band a b i = true
  have hcount := Finset.card_filter_add_card_filter_not (s := Finset.range s) pred
  have htrue : ((Finset.range s).filter pred).card = (couplingZeroRows boundary s t band a b).card :=
    couplingGuard_true_count hst boundary band a b hb
  have hfalse : ((Finset.range s).filter (fun i => ¬pred i)).card =
      s-(couplingZeroRows boundary s t band a b).card := by
    rw [Finset.card_range,htrue] at hcount
    omega
  have heach (i : ℕ) : packetSpatialGuardedStepCost (couplingSkipAt boundary s t band a b i) P q w s t u band+3 =
      (if pred i then zeroPacketSpatialCouplingRowCost P q w s t u band else packetSpatialCouplingRowCost P q w s t u band)+(10*w+16) := by
    unfold packetSpatialGuardedStepCost pred
    omega
  unfold packetSpatialGuardedLoopCost
  simp_rw [heach]
  rw [Finset.sum_add_distrib,Finset.sum_ite]
  simp [htrue,hfalse,smul_eq_mul,Nat.add_assoc]

theorem couplingGuard_full_count_le {s t : ℕ} [NeZero s] (hst : s < t) (boundary : Bool) (band a b : ℕ) :
    s-(couplingZeroRows boundary s t band a b).card ≤ (if boundary then haloBoundaryCountBound s t (2*band) a b else b-a)+4*band := by
  have hcomp : (Finset.univ \ couplingZeroRows boundary s t band a b).card = s-(couplingZeroRows boundary s t band a b).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  rw [← hcomp]
  cases boundary with
  | true => exact recovery_active_card_le hst band a b
  | false => exact haloExterior_active_card_le band a b

theorem packetSpatialGuardedLoopCost_le {s t : ℕ} [NeZero s] (hst : s < t)
    (boundary : Bool) (P q w u band a b : ℕ) (hb : b ≤ s) :
    packetSpatialGuardedLoopCost boundary P q w s t u band a b s ≤
      s*zeroPacketSpatialCouplingRowCost P q w s t u band+
      ((if boundary then haloBoundaryCountBound s t (2*band) a b else b-a)+4*band)*
        packetSpatialCouplingRowCost P q w s t u band+s*(10*w+16)+2 := by
  rw [packetSpatialGuardedLoopCost_counts hst boundary P q w u band a b hb]
  have hI : (couplingZeroRows boundary s t band a b).card ≤ s := by
    rw [← couplingGuard_true_count hst boundary band a b hb]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hz := Nat.mul_le_mul_right (zeroPacketSpatialCouplingRowCost P q w s t u band) hI
  have hf := Nat.mul_le_mul_right (packetSpatialCouplingRowCost P q w s t u band)
    (couplingGuard_full_count_le hst boundary band a b)
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
