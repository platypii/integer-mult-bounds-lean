import IntegerMultBounds.Machine.ActivePrefixEarlySequenceData
import IntegerMultBounds.Machine.ActivePrefixLayoutTarget
import IntegerMultBounds.Machine.ActivePrefixCompactConjugationSemantics
import IntegerMultBounds.Machine.BinaryPackedEarlyData

/-! Forward coordinate semantics of the four physical early loads on the
original array. Every spectator remains in its original serialized position. -/
namespace IntegerMultBounds.Machine.ActivePrefixEarlySequenceSemantics
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes CompactActiveTargetGeometry
open ActivePrefixEarlySequenceData
open ActivePrefixCompactConjugationData (Kind view)

variable (s : Shape) (p : Parameters s) (offset : ℕ)
variable (hfit : offset+p.f*p.q≤p.before) {rows : ℕ}

def index (x : Address s p rows) :=
  CompactActiveTargetLayout.index s (p.n*p.b) (p.n*p.q) p.before p.after rows
    p.compactFits p.activeSize x

def prefixIndex (x : Address s p rows) :
    Fin (ActivePrefixSelectedLoadData.prefixCount (targetShape s p offset hfit) rows) :=
  ⟨targetRank s p x,target_rank_lt s p x⟩

theorem target_index (x : Address s p rows) :
    Fin.cast (target_volume s p offset hfit rows)
      (FiberLayoutData.index (prefixIndex s p offset hfit x) x.target
        (targetSuffixIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows x))=index s p x := by
  apply Fin.ext
  exact congrArg Fin.val (ActivePrefixLayoutTarget.target_fiber_index s p x)

def selectedOffset (x : Address s p rows) :=
  BinaryPackedEarlyData.selected p.q p.b p.n (ActivePrefixLayoutTarget.controls s p x offset)
    p.hb p.hbq x.t
def correctionOffset (x : Address s p rows) :=
  BinaryPackedEarlyData.correction p.q p.b p.n (ActivePrefixLayoutTarget.controls s p x offset)
    p.hb p.hbq x.t
def selectedDestination (x : Address s p rows) : Address s p rows :=
  {x with target := BinaryPackedEarlyData.add x.target (selectedOffset s p offset x)}
def correctionDestination (x : Address s p rows) : Address s p rows :=
  {x with target := BinaryPackedEarlyData.add x.target (correctionOffset s p offset x)}

theorem selected_offset (x : Address s p rows) :
    PackedOffsetPayloadValue.offset
      (ActivePrefixSelectedLoadData.offsets (targetShape s p offset hfit) rows) (p.n*p.q)
      (prefixIndex s p offset hfit x).val=selectedOffset s p offset x := by
  unfold PackedOffsetPayloadValue.offset
  rw [show (prefixIndex s p offset hfit x).val=targetRank s p x from rfl]
  unfold ActivePrefixSelectedLoadData.offsets
  rw [ActivePrefixLayoutTarget.selected_row s p offset hfit x]
  rfl

theorem correction_offset (x : Address s p rows) :
    PackedOffsetPayloadValue.offset
      (ActivePrefixCorrectionLoadData.offsets (targetShape s p offset hfit) rows) (p.n*p.q)
      (prefixIndex s p offset hfit x).val=correctionOffset s p offset x := by
  unfold PackedOffsetPayloadValue.offset
  rw [show (prefixIndex s p offset hfit x).val=targetRank s p x from rfl]
  unfold ActivePrefixCorrectionLoadData.offsets ActivePrefixCorrectionLoadData.offsetWord
  rw [ActivePrefixLayoutTarget.correction_row s p offset hfit x]
  rfl

theorem selected_entry (array : Array s rows) (x : Address s p rows) :
    selected s p offset hfit rows array (index s p (selectedDestination s p offset x))=
      array (index s p x) := by
  have h := ActivePrefixSelectedLoad.entry (targetShape s p offset hfit) rows (targetSuffix s p.after)
    (view (target_volume s p offset hfit rows).symm array)
    (prefixIndex s p offset hfit x) x.target
    (targetSuffixIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows x)
  have ho : PackedOffsetPayloadValue.offset
      (ActivePrefixSelectedLoadData.offsets (targetShape s p offset hfit) rows)
      (ActivePrefixSelectedLoadData.width (targetShape s p offset hfit))
      (prefixIndex s p offset hfit x).val=selectedOffset s p offset x :=
    selected_offset s p offset hfit x
  rw [ho] at h
  have hd := target_index s p offset hfit (selectedDestination s p offset x)
  have hi := target_index s p offset hfit x
  unfold selected view
  convert h using 1
  · congr 1
    apply Fin.ext
    have hv := congrArg Fin.val hd
    dsimp only [Fin.cast,selectedDestination,correctionDestination,prefixIndex,targetRank,
      targetPrefixIndex,targetSuffixIndex,BinaryPackedEarlyData.add,FiberLayoutData.index,
      finProdFinEquiv,ActivePrefixSelectedLoadData.width,
      ActivePrefixCorrectionLoadData.width,targetShape] at hv ⊢
    exact hv.symm
  · exact congrArg array hi.symm

theorem correction_entry (array : Array s rows) (x : Address s p rows) :
    correction s p offset hfit rows array (index s p (correctionDestination s p offset x))=
      array (index s p x) := by
  have h := ActivePrefixCorrectionLoad.entry (targetShape s p offset hfit) rows (targetSuffix s p.after)
    (view (target_volume s p offset hfit rows).symm array)
    (prefixIndex s p offset hfit x) x.target
    (targetSuffixIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows x)
  have ho : PackedOffsetPayloadValue.offset
      (ActivePrefixCorrectionLoadData.offsets (targetShape s p offset hfit) rows)
      (ActivePrefixCorrectionLoadData.width (targetShape s p offset hfit))
      (prefixIndex s p offset hfit x).val=correctionOffset s p offset x :=
    correction_offset s p offset hfit x
  rw [ho] at h
  have hd := target_index s p offset hfit (correctionDestination s p offset x)
  have hi := target_index s p offset hfit x
  unfold correction view
  convert h using 1
  · congr 1
    apply Fin.ext
    have hv := congrArg Fin.val hd
    dsimp only [Fin.cast,selectedDestination,correctionDestination,prefixIndex,targetRank,
      targetPrefixIndex,targetSuffixIndex,BinaryPackedEarlyData.add,FiberLayoutData.index,
      finProdFinEquiv,ActivePrefixSelectedLoadData.width,
      ActivePrefixCorrectionLoadData.width,targetShape] at hv ⊢
    exact hv.symm
  · exact congrArg array hi.symm

theorem compact_entry (kind : Kind) (array : Array s rows) (x : Address s p rows) :
    compact kind s p offset hfit rows array
      (index s p (ActivePrefixCompactConjugationLayout.destination kind .before s p offset x))=
        array (index s p x) := by
  have h := ActivePrefixCompactConjugationSemantics.entry .before s p offset hfit kind
    (view (ActivePrefixCompactSwapData.volume_eq s rows (p.n*p.b) p.compactFits).symm array) x
  have hd := ActivePrefixCompactSwapGeometry.original_index s p
    (ActivePrefixCompactConjugationLayout.destination kind .before s p offset x)
  have hi := ActivePrefixCompactSwapGeometry.original_index s p x
  unfold compact view
  dsimp only [index]
  rw [←hd]
  unfold view at h
  rw [hi] at h
  simpa only [Fin.cast_cast,Fin.cast_eq_self,ActivePrefixCompactConjugationLayout.suffix]
    using h

def destination (x : Address s p rows) : Address s p rows :=
  ActivePrefixCompactConjugationLayout.destination .negative .before s p offset
    (correctionDestination s p offset
      (ActivePrefixCompactConjugationLayout.destination .parity .before s p offset
        (selectedDestination s p offset x)))

/-- Every bit follows the composed current-address transformations of the
actual shared-array schedule, including addresses outside the guarded set. -/
theorem entry (array : Array s rows) (x : Address s p rows) :
    result s p offset hfit rows array (index s p (destination s p offset x))=
      array (index s p x) := by
  unfold result destination
  rw [compact_entry,correction_entry,compact_entry,selected_entry]

end
end IntegerMultBounds.Machine.ActivePrefixEarlySequenceSemantics
