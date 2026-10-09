import IntegerMultBounds.Machine.ActivePrefixDirtyControlPackedLate
import IntegerMultBounds.Machine.BinaryPackedLatePermutation
import IntegerMultBounds.Machine.ActiveRepairLayoutPermutation

/-! The actual twelve-swap, ten-rotation later schedule realizes the exact
global permutation consumed by repair, on every original array address. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlLateGlobal
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixLayoutBack
open ActivePrefixDirtyControlGlobalSequence
open ActivePrefixDirtyControlPackedEarly (state)
open ActiveRepairLayoutPermutation ActiveRepairLayoutPermutationFiber
open Compact Compact.PowerTwo
variable (s : Shape) (p : Parameters s) (offset : ℕ) (hfit : offset+p.f*p.q≤p.after) {rows : ℕ}

theorem positive : 1≤p.q := by have := p.hbq; omega
local notation "LA" => lateActual s p.q p.b p.n p.before p.after rows p.rho offset (p.f*p.q)
  ActiveRepairRankHeadersData.SourceSide.after (positive s p)

theorem controls (x : Address s p rows) :
    controlWord p.before p.after p.q p.rho p.n offset (p.f*p.q) .after
      (x.activeBefore,x.activeAfter)=afterControls s p x offset := rfl

theorem local_value (x : Address s p rows) :
    let Z := afterControls s p x offset
    let e := ActiveRepairLayoutPermutationFields.lateEquiv p.q p.b p.n Z (positive s p)
      (SelectedSourceBitsData.selected_length _ _ _ _)
    e ((destination s p rows offset hfit x).u,
      ((destination s p rows offset hfit x).target,(destination s p rows offset hfit x).t))=
      lateSperm p.q p.b Z (e (x.u,(x.target,x.t))) := by
  rw [ActivePrefixDirtyControlPackedLate.destination_as_run]
  exact BinaryPackedLatePermutation.run_fields p.q p.b p.n p.hb p.hbq
    (afterControls s p x offset) (SelectedSourceBitsData.selected_length _ _ _ _) (state s p x)

theorem destination_actual (x : Address s p rows) : destination s p rows offset hfit x=LA x := by
  apply (lateFiber s p.q p.b p.n p.before p.after rows p.rho offset (p.f*p.q)
    ActiveRepairRankHeadersData.SourceSide.after (positive s p)).injective
  rw [late_actual_fiber]
  have hl := local_value s p offset hfit x
  rw [ActivePrefixDirtyControlPackedLate.destination_as_run]
  simp only [lateFiber,ActiveRepairLayoutPermutationFiber.lateEquiv,
    VaryingControlRepairPacked.lateActual,Equiv.coe_fn_mk,controls]
  congr 2
  simp only [ActivePrefixDirtyControlPackedLate.destination_as_run,
    afterControls,afterSource,ActiveRepairLayoutPermutation.Z,
    ActiveRepairLayoutPermutationFiber.controlWord,ActiveRepairLayoutPermutationFiber.sourceWord] at hl ⊢
  convert hl using 1

variable (hn : 0<p.n) (hb : 2≤p.b) (hrecord : s.bits+1≤s.payload)
variable (hrows : 0<rows) (hK : 0<s.chunk) (hd : 0<s.axes) (hg : 0<s.guard)
local notation "g" => ActivePrefixDirtyControlSequenceGeometry.geometry s p rows offset hfit hn hb hrecord hrows hK hd hg

theorem entry (array : ActivePrefixDirtyControlConjugationData.FullArray s rows) (x : Address s p rows) :
    ActivePrefixDirtyControlSequenceData.later g array (ActivePrefixDirtyControlGlobalSwap.index s p (LA x))=
      array (ActivePrefixDirtyControlGlobalSwap.index s p x) := by
  rw [←destination_actual s p offset hfit x]
  exact ActivePrefixDirtyControlGlobalSequence.entry s p rows offset hfit hn hb hrecord hrows hK hd hg array x

theorem entry_inverse (array : ActivePrefixDirtyControlConjugationData.FullArray s rows) (x : Address s p rows) :
    ActivePrefixDirtyControlSequenceData.later g array (ActivePrefixDirtyControlGlobalSwap.index s p x)=
      array (ActivePrefixDirtyControlGlobalSwap.index s p ((LA).symm x)) := by
  simpa only [Equiv.apply_symm_apply] using entry s p offset hfit hn hb hrecord hrows hK hd hg array ((LA).symm x)

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlLateGlobal
