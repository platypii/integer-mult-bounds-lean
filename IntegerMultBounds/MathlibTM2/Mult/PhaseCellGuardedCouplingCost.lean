module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunSpatialCouplingRows
public import IntegerMultBounds.NLogN.PhaseCellHaloCouplingBudget

/-! Exact branch counts in the executed ambient recovery loop. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Generated mask bits count ambient coordinates, with no signed-offset deduplication. -/
theorem couplingGuard_true_count {s t : ℕ} [NeZero s] (hst : s < t)
    (band a b : ℕ) (hb : b ≤ s) :
    ((Finset.range s).filter (fun i => couplingSkipAt true s t band a b i = true)).card =
      (haloInterior s t (2*band) a b).card := by
  refine Finset.card_bij (fun i _ => (i : ZMod s)) ?_ ?_ ?_
  · intro i hi
    obtain ⟨hir,hflag⟩ := Finset.mem_filter.mp hi
    exact (couplingSkipAt_sound hst true band a b i hb (Finset.mem_range.mp hir) hflag).2
  · intro i hi j hj he
    have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hv := congrArg (fun x : ZMod s => x.val) he
    simpa [ZMod.val_cast_of_lt hi',ZMod.val_cast_of_lt hj'] using hv
  · intro j hj
    refine ⟨j.val,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt j),?_⟩,by simp⟩
    have hmask := (haloMaskAt_spec false hst (2*band) a b j.val hb (ZMod.val_lt j)).mpr (by simpa using hj)
    simpa [couplingSkipAt] using hmask

theorem packetSpatialGuardedLoopCost_recovery {s t : ℕ} [NeZero s] (hst : s < t)
    (P q w u band a b : ℕ) (hb : b ≤ s) :
    packetSpatialGuardedLoopCost true P q w s t u band a b s =
      (haloInterior s t (2*band) a b).card*zeroPacketSpatialCouplingRowCost P q w s t u band+
      (s-(haloInterior s t (2*band) a b).card)*packetSpatialCouplingRowCost P q w s t u band+
      s*(10*w+16)+2 := by
  let pred := fun i => couplingSkipAt true s t band a b i = true
  have hcount := Finset.card_filter_add_card_filter_not (s := Finset.range s) pred
  have htrue : ((Finset.range s).filter pred).card = (haloInterior s t (2*band) a b).card :=
    couplingGuard_true_count hst band a b hb
  have hfalse : ((Finset.range s).filter (fun i => ¬pred i)).card =
      s-(haloInterior s t (2*band) a b).card := by
    rw [Finset.card_range,htrue] at hcount
    omega
  have heach (i : ℕ) : packetSpatialGuardedStepCost (couplingSkipAt true s t band a b i) P q w s t u band+3 =
      (if pred i then zeroPacketSpatialCouplingRowCost P q w s t u band else packetSpatialCouplingRowCost P q w s t u band)+(10*w+16) := by
    unfold packetSpatialGuardedStepCost pred
    omega
  unfold packetSpatialGuardedLoopCost
  simp_rw [heach]
  rw [Finset.sum_add_distrib,Finset.sum_ite]
  simp [htrue,hfalse,smul_eq_mul,Nat.add_assoc]

theorem couplingGuard_full_count_le {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ) :
    s-(haloInterior s t (2*band) a b).card ≤
      s-(haloVertices s a b).card+haloBoundaryCountBound s t (2*band) a b := by
  have hI := Finset.card_le_card (haloInterior_subset s t (2*band) a b)
  have hV : (haloVertices s a b).card ≤ s := by
    have h := Finset.card_le_card (Finset.subset_univ (haloVertices s a b))
    simpa using h
  have hB : (haloBoundary s t (2*band) a b).card =
      (haloVertices s a b).card-(haloInterior s t (2*band) a b).card :=
    Finset.card_sdiff_of_subset (haloInterior_subset s t (2*band) a b)
  have hbound := haloBoundary_card_bound hst (2*band) a b
  omega

theorem packetSpatialGuardedLoopCost_recovery_le {s t : ℕ} [NeZero s] (hst : s < t)
    (P q w u band a b : ℕ) (hb : b ≤ s) :
    packetSpatialGuardedLoopCost true P q w s t u band a b s ≤
      s*zeroPacketSpatialCouplingRowCost P q w s t u band+
      (s-(haloVertices s a b).card+haloBoundaryCountBound s t (2*band) a b)*
        packetSpatialCouplingRowCost P q w s t u band+s*(10*w+16)+2 := by
  rw [packetSpatialGuardedLoopCost_recovery hst P q w u band a b hb]
  have hI : (haloInterior s t (2*band) a b).card ≤ s := by
    rw [← couplingGuard_true_count hst band a b hb]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hz := Nat.mul_le_mul_right (zeroPacketSpatialCouplingRowCost P q w s t u band) hI
  have hf := Nat.mul_le_mul_right (packetSpatialCouplingRowCost P q w s t u band)
    (couplingGuard_full_count_le hst band a b)
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
