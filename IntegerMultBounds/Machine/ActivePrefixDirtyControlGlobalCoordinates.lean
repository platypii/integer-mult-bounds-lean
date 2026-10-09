import IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalSequence

/-! The two conjugations shift exactly T or U at their original coordinates;
the dirty back word and all spectators return to their original values. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalCoordinates
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes
open ActivePrefixDirtyControlGlobalConjugation (tDestination uDestination)
open ActivePrefixLayoutSwap (swapT)
open ActivePrefixDirtyControlUSwapGeometry (swapU)
open ActivePrefixDirtyControlGlobalSequence

variable (s : Shape) (p : Parameters s) {rows : ℕ}

theorem t_destination (V : List Bool) (x : Address s p rows) :
    tDestination s p V x={ x with
    t := BinaryPackedEarlyData.add x.t
      (PackedOffsetPayloadValue.offset V (p.n*p.b) (backRank s p (swapT s p x))) } := by
  have hr {a b : ℕ} (v : Fin (a*b)) : finProdFinEquiv (v.divNat,v.modNat)=v :=
    finProdFinEquiv.apply_symm_apply v
  simp [tDestination,swapT,ActivePrefixDirtyControlGlobalBack.destination,
    CompactActiveTargetGeometry.splitBack,RecursiveInterchangeRows.pack,hr]

theorem u_destination (V : List Bool) (x : Address s p rows) :
    uDestination s p V x={ x with
    u := BinaryPackedEarlyData.add x.u
      (PackedOffsetPayloadValue.offset V (p.n*p.b) (backRank s p (swapU s p x))) } := by
  have hr {a b : ℕ} (v : Fin (a*b)) : finProdFinEquiv (v.divNat,v.modNat)=v :=
    finProdFinEquiv.apply_symm_apply v
  simp [uDestination,swapU,ActivePrefixDirtyControlGlobalBack.destination,
    CompactActiveTargetGeometry.splitBack,RecursiveInterchangeRows.pack,hr]

theorem pure_gather_independent (X Z Z' : List Bool) :
    Gather.gather (fun x _ => x) (PackedArith.parity p.q p.b p.hb p.hbq) X Z p.n=
      Gather.gather (fun x _ => x) (PackedArith.parity p.q p.b p.hb p.hbq) X Z' p.n := by
  simp only [Compact.PowerTwo.gather_flatten]
  congr 2

 theorem pure_offset (x : Address s p rows) :
    PackedOffsetPayloadValue.offset (pureOffsets s p rows) (p.n*p.b) (backRank s p (swapT s p x))=
      BinaryPackedEarlyData.parity p.q p.b p.n p.hb p.hbq x.target := by
  unfold PackedOffsetPayloadValue.offset pureOffsets
  change Counter.value (Gather.field (BinaryAddressOffsetRepeatData.copies
    (ActivePrefixDirtyControlPureBank.offsetWord (ActivePrefixDirtyControlLayoutFields.compactShape s p)) rows)
      (backRank s p (swapT s p x)*(p.n*p.b)) (p.n*p.b))=_
  rw [ActivePrefixDirtyControlLayoutRows.pure_row s p (swapT s p x)]
  unfold BinaryPackedEarlyData.parity BinaryAddressOffsetValue.rowWord
  exact congrArg Counter.value (pure_gather_independent s p _ _ _)

 theorem negative_offset (x : Address s p rows) :
    PackedOffsetPayloadValue.offset (negativeOffsets s p rows) (p.n*p.b) (backRank s p (swapT s p x))=
      BinaryPackedEarlyData.negative p.q p.b p.n (ActivePrefixDirtyControlLayoutRows.controls s p x)
        p.hb p.hbq x.target := by
  unfold PackedOffsetPayloadValue.offset negativeOffsets
  change Counter.value (Gather.field (BinaryAddressOffsetRepeatData.copies
    (ActivePrefixDirtyControlNegativeData.negative (ActivePrefixDirtyControlLayoutFields.compactShape s p)) rows)
      (backRank s p (swapT s p x)*(p.n*p.b)) (p.n*p.b))=_
  rw [ActivePrefixDirtyControlLayoutRows.negative_row s p (swapT s p x)]
  rfl

theorem source_offset (offset : ℕ) (hfit : offset+p.f*p.q≤p.after) (x : Address s p rows) :
    PackedOffsetPayloadValue.offset (sourceOffsets s p rows offset hfit) (p.n*p.b) (backRank s p (swapU s p x))=
      Counter.value (ActivePrefixDirtyControlSourceSemantics.selectedCompact s p offset x) := by
  unfold PackedOffsetPayloadValue.offset sourceOffsets
  change Counter.value (Gather.field (BinaryAddressOffsetRepeatData.copies
    (ActivePrefixDirtyControlPureBank.offsetWord (ActivePrefixDirtyControlSourceGeometry.sourceShape s p offset hfit)) rows)
      (backRank s p (swapU s p x)*(p.n*p.b)) (p.n*p.b))=_
  rw [ActivePrefixDirtyControlSourceSemantics.positive_row s p offset hfit (swapU s p x)]
  rfl

theorem unload_offset (offset : ℕ) (hfit : offset+p.f*p.q≤p.after) (x : Address s p rows) :
    PackedOffsetPayloadValue.offset (unloadOffsets s p rows offset hfit) (p.n*p.b) (backRank s p (swapU s p x))=
      Counter.value (TwosComplement.negWord (ActivePrefixDirtyControlSourceSemantics.selectedCompact s p offset x)) := by
  unfold PackedOffsetPayloadValue.offset unloadOffsets ActivePrefixDirtyControlNegativePureLoadData.offsets
  rw [ActivePrefixDirtyControlSourceSemantics.negative_row s p offset hfit (swapU s p x)]
  rfl

theorem pure_destination (x : Address s p rows) :
    tDestination s p (pureOffsets s p rows) x={ x with
      t := BinaryPackedEarlyData.add x.t (BinaryPackedEarlyData.parity p.q p.b p.n p.hb p.hbq x.target) } := by
  rw [t_destination,pure_offset]

theorem negative_destination (x : Address s p rows) :
    tDestination s p (negativeOffsets s p rows) x={ x with
      t := BinaryPackedEarlyData.add x.t (BinaryPackedEarlyData.negative p.q p.b p.n
        (ActivePrefixDirtyControlLayoutRows.controls s p x) p.hb p.hbq x.target) } := by
  rw [t_destination,negative_offset]

theorem source_destination (offset : ℕ) (hfit : offset+p.f*p.q≤p.after) (x : Address s p rows) :
    uDestination s p (sourceOffsets s p rows offset hfit) x={ x with
      u := BinaryPackedEarlyData.add x.u
        (Counter.value (ActivePrefixDirtyControlSourceSemantics.selectedCompact s p offset x)) } := by
  rw [u_destination,source_offset]

theorem unload_destination (offset : ℕ) (hfit : offset+p.f*p.q≤p.after) (x : Address s p rows) :
    uDestination s p (unloadOffsets s p rows offset hfit) x={ x with
      u := BinaryPackedEarlyData.add x.u
        (Counter.value (TwosComplement.negWord (ActivePrefixDirtyControlSourceSemantics.selectedCompact s p offset x))) } := by
  rw [u_destination,unload_offset]

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalCoordinates
