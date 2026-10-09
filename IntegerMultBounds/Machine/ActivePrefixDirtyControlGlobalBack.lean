import IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalTarget

/-! Generic full-array back rotation at the unchanged layout coordinates.
Its explicit stream is later instantiated by the proved physical producers. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalBack
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes
open ActivePrefixLayoutGeometry (backWidth)
open CompactActiveTargetGeometry
open ActivePrefixDirtyControlConjugationData (FullArray view)
open ActivePrefixDirtyControlGlobalSwap (index)
open RecursiveInterchangeRows (pack)

variable (s : Shape) (p : Parameters s) {rows : ℕ}
def prefixIndex (x : Address s p rows) : Fin (rows*2^(backWidth s (p.n*p.q) p.before p.after)) :=
  ⟨backRank s p x,back_rank_lt s p x⟩
def suffixIndex (x : Address s p rows) : Fin (compactSuffix s (p.n*p.b)) :=
  pack (splitBack s (p.n*p.b) p.compactFits x.back).2 x.payload

def result (V : List Bool) (array : FullArray s rows) :=
  view (ActivePrefixDirtyControlSequenceGeometry.compact_volume s p rows).symm
    (PackedOffsetPayloadArray.array V (p.n*p.b)
      (rows*2^(backWidth s (p.n*p.q) p.before p.after)) (compactSuffix s (p.n*p.b))
      (view (ActivePrefixDirtyControlSequenceGeometry.compact_volume s p rows) array))

def destination (V : List Bool) (x : Address s p rows) : Address s p rows :=
  { x with
    back := Fin.cast (back_size s (p.n*p.b) p.compactFits).symm
      (pack (BinaryPackedEarlyData.add (splitBack s (p.n*p.b) p.compactFits x.back).1
        (PackedOffsetPayloadValue.offset V (p.n*p.b) (backRank s p x)))
          (splitBack s (p.n*p.b) p.compactFits x.back).2) }

theorem split_destination (V : List Bool) (x : Address s p rows) :
    splitBack s (p.n*p.b) p.compactFits (destination s p V x).back=
      (BinaryPackedEarlyData.add (splitBack s (p.n*p.b) p.compactFits x.back).1
        (PackedOffsetPayloadValue.offset V (p.n*p.b) (backRank s p x)),
      (splitBack s (p.n*p.b) p.compactFits x.back).2) := by
  simp [destination,splitBack,pack]

theorem fiber_index (x : Address s p rows) :
    Fin.cast (ActivePrefixDirtyControlSequenceGeometry.compact_volume s p rows).symm
      (FiberLayoutData.index (prefixIndex s p x) (splitBack s (p.n*p.b) p.compactFits x.back).1
        (suffixIndex s p x))=index s p x := by
  apply Fin.ext
  exact congrArg Fin.val (back_index s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize x)

theorem entry (V : List Bool) (hV : V.length=(rows*2^(backWidth s (p.n*p.q) p.before p.after))*(p.n*p.b))
    (array : FullArray s rows) (x : Address s p rows) :
    result s p V array (index s p (destination s p V x))=array (index s p x) := by
  have h := ActiveTargetRotation.entry V (p.n*p.b)
    (rows*2^(backWidth s (p.n*p.q) p.before p.after)) (compactSuffix s (p.n*p.b)) hV
    (view (ActivePrefixDirtyControlSequenceGeometry.compact_volume s p rows) array)
    (prefixIndex s p x) (splitBack s (p.n*p.b) p.compactFits x.back).1 (suffixIndex s p x)
  have hd := fiber_index s p (destination s p V x)
  have hi := fiber_index s p x
  unfold suffixIndex at hd
  rw [split_destination] at hd
  rw [←hd,←hi]
  unfold result view
  exact h

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalBack
