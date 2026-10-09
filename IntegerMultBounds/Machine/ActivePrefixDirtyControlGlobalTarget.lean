import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceGeometry
import IntegerMultBounds.Machine.ActivePrefixDirtyControlLayoutRows
import IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalSwap
import IntegerMultBounds.Machine.ActivePrefixLayoutTarget
import IntegerMultBounds.Machine.BinaryPackedEarlyData

/-! Physical target selected/correction loads at every original address,
using the current compact U parity controls. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalTarget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes hiding targetShape
open ActivePrefixDirtyControlLayoutFields (targetShape)
open CompactActiveTargetGeometry
open ActivePrefixDirtyControlConjugationData (FullArray view)
variable (s : Shape) (p : Parameters s) {rows : ℕ}
abbrev Array := FullArray

def selected (rows : ℕ) (array : FullArray s rows) :=
  view (ActivePrefixDirtyControlSequenceGeometry.target_volume s p rows).symm
    (ActivePrefixDirtyControlLoad.result (m := .selected) (targetShape s p) rows (targetSuffix s p.after)
      (view (ActivePrefixDirtyControlSequenceGeometry.target_volume s p rows) array))
def correction (rows : ℕ) (array : FullArray s rows) :=
  view (ActivePrefixDirtyControlSequenceGeometry.target_volume s p rows).symm
    (ActivePrefixDirtyControlLoad.result (m := .correction) (targetShape s p) rows (targetSuffix s p.after)
      (view (ActivePrefixDirtyControlSequenceGeometry.target_volume s p rows) array))
def index (x : Address s p rows) :=
  CompactActiveTargetLayout.index s (p.n*p.b) (p.n*p.q) p.before p.after rows
    p.compactFits p.activeSize x

def prefixIndex (x : Address s p rows) :
    Fin (ActivePrefixDirtyControlLoadData.prefixCount (m := .selected) (targetShape s p) rows) :=
  ⟨targetRank s p x,target_rank_lt s p x⟩

theorem target_index (x : Address s p rows) :
    Fin.cast ((ActivePrefixDirtyControlSequenceGeometry.target_volume s p rows).symm)
      (FiberLayoutData.index (prefixIndex s p x) x.target
        (targetSuffixIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows x))=index s p x := by
  apply Fin.ext
  exact congrArg Fin.val (ActivePrefixLayoutTarget.target_fiber_index s p x)

def selectedOffset (x : Address s p rows) :=
  BinaryPackedEarlyData.selected p.q p.b p.n (ActivePrefixDirtyControlLayoutRows.controls s p x)
    p.hb p.hbq x.t
def correctionOffset (x : Address s p rows) :=
  BinaryPackedEarlyData.correction p.q p.b p.n (ActivePrefixDirtyControlLayoutRows.controls s p x)
    p.hb p.hbq x.t
def selectedDestination (x : Address s p rows) : Address s p rows :=
  {x with target := BinaryPackedEarlyData.add x.target (selectedOffset s p x)}
def correctionDestination (x : Address s p rows) : Address s p rows :=
  {x with target := BinaryPackedEarlyData.add x.target (correctionOffset s p x)}

theorem selected_offset (x : Address s p rows) :
    PackedOffsetPayloadValue.offset
      (ActivePrefixDirtyControlLoadData.offsets (m := .selected) (targetShape s p) rows) (p.n*p.q)
      (prefixIndex s p x).val=selectedOffset s p x := by
  unfold PackedOffsetPayloadValue.offset
  rw [show (prefixIndex s p x).val=targetRank s p x from rfl]
  change Counter.value (Gather.field (BinaryAddressOffsetRepeatData.copies
    (ActivePrefixDirtyControlData.offsetWord (targetShape s p)) rows)
    (targetRank s p x*(p.n*p.q)) (p.n*p.q))=_
  rw [ActivePrefixDirtyControlLayoutRows.selected_row s p x]
  rfl

theorem correction_offset (x : Address s p rows) :
    PackedOffsetPayloadValue.offset
      (ActivePrefixDirtyControlLoadData.offsets (m := .correction) ((targetShape s p)) rows) (p.n*p.q)
      (prefixIndex s p x).val=correctionOffset s p x := by
  unfold PackedOffsetPayloadValue.offset
  rw [show (prefixIndex s p x).val=targetRank s p x from rfl]
  change Counter.value (Gather.field (BinaryAddressOffsetRepeatData.copies
    (ActivePrefixDirtyControlCorrectionData.word (targetShape s p)) rows)
    (targetRank s p x*(p.n*p.q)) (p.n*p.q))=_
  rw [ActivePrefixDirtyControlLayoutRows.correction_row s p x]
  rfl

theorem selected_entry (array : Array s rows) (x : Address s p rows) :
    selected s p rows array (index s p (selectedDestination s p x))=
      array (index s p x) := by
  have h := ActivePrefixDirtyControlLoad.entry (m := .selected) ((targetShape s p)) rows (targetSuffix s p.after)
    (view ((ActivePrefixDirtyControlSequenceGeometry.target_volume s p rows).symm).symm array)
    (prefixIndex s p x) x.target
    (targetSuffixIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows x)
  have ho : PackedOffsetPayloadValue.offset
      (ActivePrefixDirtyControlLoadData.offsets (m := .selected) (targetShape s p) rows)
      (ActivePrefixDirtyControlLoadProducer.width (m := .selected) (targetShape s p))
      (prefixIndex s p x).val=selectedOffset s p x :=
    selected_offset s p x
  rw [ho] at h
  have hd := target_index s p (selectedDestination s p x)
  have hi := target_index s p x
  unfold selected view
  convert h using 1
  · congr 1
    apply Fin.ext
    have hv := congrArg Fin.val hd
    dsimp only [Fin.cast,selectedDestination,correctionDestination,prefixIndex,targetRank,
      targetPrefixIndex,targetSuffixIndex,BinaryPackedEarlyData.add,FiberLayoutData.index,
      finProdFinEquiv,ActivePrefixDirtyControlLoadProducer.width,targetShape] at hv ⊢
    exact hv.symm
  · exact congrArg array hi.symm

theorem correction_entry (array : Array s rows) (x : Address s p rows) :
    correction s p rows array (index s p (correctionDestination s p x))=
      array (index s p x) := by
  have h := ActivePrefixDirtyControlLoad.entry (m := .correction) ((targetShape s p)) rows (targetSuffix s p.after)
    (view ((ActivePrefixDirtyControlSequenceGeometry.target_volume s p rows).symm).symm array)
    (prefixIndex s p x) x.target
    (targetSuffixIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows x)
  have ho : PackedOffsetPayloadValue.offset
      (ActivePrefixDirtyControlLoadData.offsets (m := .correction) ((targetShape s p)) rows)
      (ActivePrefixDirtyControlLoadProducer.width (m := .correction) ((targetShape s p)))
      (prefixIndex s p x).val=correctionOffset s p x :=
    correction_offset s p x
  rw [ho] at h
  have hd := target_index s p (correctionDestination s p x)
  have hi := target_index s p x
  unfold correction view
  convert h using 1
  · congr 1
    apply Fin.ext
    have hv := congrArg Fin.val hd
    dsimp only [Fin.cast,selectedDestination,correctionDestination,prefixIndex,targetRank,
      targetPrefixIndex,targetSuffixIndex,BinaryPackedEarlyData.add,FiberLayoutData.index,
      finProdFinEquiv,ActivePrefixDirtyControlLoadProducer.width,targetShape] at hv ⊢
    exact hv.symm
  · exact congrArg array hi.symm

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalTarget
