import IntegerMultBounds.Machine.ActivePrefixLayoutBack

/-! The real compact-T/back exchange on unchanged array coordinates. The
active target and both active source regions remain literal coordinates; the
back rotation now acts on T, while its prefix contains the current target. -/
namespace IntegerMultBounds.Machine.ActivePrefixLayoutSwap
open CompactGadgetReservationShape (Shape)
open CompactActiveTargetGeometry
open ActivePrefixLayoutShapes
open RecursiveInterchangeRows (pack)
open BinaryAddressOffsetRepeatData (copies)
open BinaryAddressTableData (row)

variable (s : Shape) (p : Parameters s) {rows : ℕ}

def swapT (x : Address s p rows) : Address s p rows :=
  { x with
    t := (splitBack s (p.n*p.b) p.compactFits x.back).1
    back := Fin.cast (back_size s (p.n*p.b) p.compactFits).symm
      (pack x.t (splitBack s (p.n*p.b) p.compactFits x.back).2) }

theorem split_swap (x : Address s p rows) :
    splitBack s (p.n*p.b) p.compactFits (swapT s p x).back=
      (x.t,(splitBack s (p.n*p.b) p.compactFits x.back).2) := by
  simp [swapT,splitBack,pack]

theorem target_and_sources (x : Address s p rows) :
    (swapT s p x).target=x.target ∧ (swapT s p x).activeBefore=x.activeBefore ∧
      (swapT s p x).activeAfter=x.activeAfter ∧
      (splitBack s (p.n*p.b) p.compactFits (swapT s p x).back).1=x.t := by
  exact ⟨rfl,rfl,rfl,congrArg Prod.fst (split_swap s p x)⟩

theorem swapped_index (x : Address s p rows) :
    tIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits (swapT s p x)=
      RadixRangePadding.index (pack (pack x.row x.u) x.uTail)
        (splitBack s (p.n*p.b) p.compactFits x.back).1
        (pack (pack (pack (pack x.tTail x.frontSlack) x.activeBefore) x.target) x.activeAfter)
        x.t (pack (splitBack s (p.n*p.b) p.compactFits x.back).2 x.payload) := by
  unfold tIndex
  rw [split_swap]
  rfl

/-- Exactly the existing flat-array transpose swaps compact T with the high
back coordinate. This is a coordinate identity, not a new array layout. -/
theorem transpose_entry {α : Type*}
    (array : Fin (RadixRangePadding.volume (tPrefix s (p.n*p.b) rows) (2^(p.n*p.b))
      (tGap s (p.n*p.b) (p.n*p.q) p.before p.after) (compactSuffix s (p.n*p.b))) → α)
    (x : Address s p rows) :
    RadixRangePadding.transpose array (tIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits x)=
      array (tIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits (swapT s p x)) := by
  rw [swapped_index]
  exact RadixRangePadding.transpose_entry array _ _ _ _ _

theorem unchanged_array_index (x : Address s p rows) :
    Fin.cast (t_volume s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize)
      (tIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits (swapT s p x))=
      CompactActiveTargetLayout.index s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize (swapT s p x) :=
  t_index _ _ _ _ _ _ _ _ _

/-- The post-exchange back-fiber target is literally the original compact T;
its prefix is the exact rank used by the repeated parity offset table. -/
theorem back_fiber_after_swap (x : Address s p rows) :
    Fin.cast (back_volume s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize)
      (FiberLayoutData.index
        (backPrefixIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows (swapT s p x))
        x.t (pack (splitBack s (p.n*p.b) p.compactFits x.back).2 x.payload))=
      CompactActiveTargetLayout.index s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize (swapT s p x) := by
  have h := back_index s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize (swapT s p x)
  unfold backIndex at h
  rw [split_swap] at h
  exact h

theorem pure_before (offset : ℕ) (hfit : offset+p.f*p.q≤p.before) (x : Address s p rows) :
    Gather.field (copies (ActivePrefixParityOnlyBank.offsetWord (backBeforeShape s p offset hfit)) rows)
      (backRank s p (swapT s p x)*(p.n*p.b)) (p.n*p.b)=
      Gather.gather (fun z _ => z) (PackedArith.parity p.q p.b p.hb p.hbq)
        (row (p.n*p.q) x.target.val) (ActivePrefixLayoutBack.beforeControls s p x offset) p.n :=
  ActivePrefixLayoutBack.pure_before s p offset hfit (swapT s p x)

theorem pure_after (offset : ℕ) (hfit : offset+p.f*p.q≤p.after) (x : Address s p rows) :
    Gather.field (copies (ActivePrefixParityOnlyBank.offsetWord (backAfterShape s p offset hfit)) rows)
      (backRank s p (swapT s p x)*(p.n*p.b)) (p.n*p.b)=
      Gather.gather (fun z _ => z) (PackedArith.parity p.q p.b p.hb p.hbq)
        (row (p.n*p.q) x.target.val) (ActivePrefixLayoutBack.afterControls s p x offset) p.n :=
  ActivePrefixLayoutBack.pure_after s p offset hfit (swapT s p x)

theorem negative_before (offset : ℕ) (hfit : offset+p.f*p.q≤p.before) (x : Address s p rows) :
    Gather.field (copies (ActivePrefixParityNegativeData.negative (backBeforeShape s p offset hfit)) rows)
      (backRank s p (swapT s p x)*(p.n*p.b)) (p.n*p.b)=
      TwosComplement.negWord (Gather.gather xor (PackedArith.parity p.q p.b p.hb p.hbq)
        (row (p.n*p.q) x.target.val) (ActivePrefixLayoutBack.beforeControls s p x offset) p.n) :=
  ActivePrefixLayoutBack.negative_before s p offset hfit (swapT s p x)

theorem negative_after (offset : ℕ) (hfit : offset+p.f*p.q≤p.after) (x : Address s p rows) :
    Gather.field (copies (ActivePrefixParityNegativeData.negative (backAfterShape s p offset hfit)) rows)
      (backRank s p (swapT s p x)*(p.n*p.b)) (p.n*p.b)=
      TwosComplement.negWord (Gather.gather xor (PackedArith.parity p.q p.b p.hb p.hbq)
        (row (p.n*p.q) x.target.val) (ActivePrefixLayoutBack.afterControls s p x offset) p.n) :=
  ActivePrefixLayoutBack.negative_after s p offset hfit (swapT s p x)

end IntegerMultBounds.Machine.ActivePrefixLayoutSwap
