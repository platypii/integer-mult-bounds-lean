import IntegerMultBounds.Machine.ActivePrefixEarlySequencePacked
import IntegerMultBounds.Machine.ActiveRepairLayoutPermutation

/-! The physically implemented early four-load schedule is the complete
varying-source permutation of the unchanged full array. -/
namespace IntegerMultBounds.Machine.ActivePrefixEarlySequenceGlobal
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceSemantics
open ActiveRepairLayoutPermutation ActiveRepairLayoutPermutationFiber
open Compact Compact.PowerTwo

variable (s : Shape) (p : Parameters s) (offset : ℕ) {rows : ℕ}
theorem positive : 1≤p.q := by have := p.hbq; omega
local notation "EA" => earlyActual s p.q p.b p.n p.before p.after rows p.rho offset (p.f*p.q) ActiveRepairRankHeadersData.SourceSide.before (positive s p)

 theorem controls (x : Address s p rows) :
    controlWord p.before p.after p.q p.rho p.n offset (p.f*p.q) .before
      (x.activeBefore,x.activeAfter)=ActivePrefixLayoutTarget.controls s p x offset := rfl

 theorem local_value (x : Address s p rows) :
    let Z := ActivePrefixLayoutTarget.controls s p x offset
    let e := ActiveRepairLayoutPermutationFields.earlyEquiv p.q p.b p.n Z (positive s p)
      (SelectedSourceBitsData.selected_length _ _ _ _)
    e ((destination s p offset x).target,(destination s p offset x).t)=
      Sperm p.q p.b Z (e (x.target,x.t)) := by
  dsimp only
  let Z := ActivePrefixLayoutTarget.controls s p x offset
  let e := ActiveRepairLayoutPermutationFields.earlyEquiv p.q p.b p.n Z (positive s p)
    (SelectedSourceBitsData.selected_length _ _ _ _)
  have h := packedEarlyPerm_agrees (2*Li p.q) (Bi p.b) (by have := Li_pos p.q; omega)
    (by have := Bi_one p.b; omega) (Compact.PowerTwo.controls Z) (e (x.target,x.t))
  have hv := ActivePrefixEarlySequencePacked.packed_value s p offset x
  change ((Sperm p.q p.b Z (e (x.target,x.t))).1.val,
      (Sperm p.q p.b Z (e (x.target,x.t))).2.val)=
    packedEarly (2*Li p.q) (Bi p.b) (Compact.PowerTwo.controls Z) x.target.val x.t.val at h
  have hr : packedEarly (2*Li p.q) (Bi p.b) (Compact.PowerTwo.controls Z) x.target.val x.t.val=
      packedEarly ((2:ℤ)^p.q) ((2:ℤ)^p.b) (Compact.PowerTwo.controls Z) x.target.val x.t.val := by
    rw [two_Li p.q (positive s p)]
  have hh := h.trans hr
  have he : (((destination s p offset x).target.val : ℤ),((destination s p offset x).t.val : ℤ))=
      ((Sperm p.q p.b Z (e (x.target,x.t))).1.val,(Sperm p.q p.b Z (e (x.target,x.t))).2.val) := hv.trans hh.symm
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst he
  · apply Subtype.ext
    exact congrArg Prod.snd he

 theorem destination_actual (x : Address s p rows) : destination s p offset x=EA x := by
  apply (earlyFiber s p.q p.b p.n p.before p.after rows p.rho offset (p.f*p.q) ActiveRepairRankHeadersData.SourceSide.before (positive s p)).injective
  rw [early_actual_fiber]
  have hl := local_value s p offset x
  rw [ActivePrefixEarlySequencePacked.destination_as_run]
  simp only [earlyFiber,ActiveRepairLayoutPermutationFiber.earlyEquiv,
    VaryingControlRepairPacked.earlyActual,
    Equiv.coe_fn_mk,controls]
  congr 2
  simp only [ActivePrefixEarlySequencePacked.destination_as_run,
    ActivePrefixLayoutTarget.controls,ActivePrefixLayoutTarget.source,
    ActiveRepairLayoutPermutation.Z,ActiveRepairLayoutPermutationFiber.controlWord,
    ActiveRepairLayoutPermutationFiber.sourceWord] at hl ⊢
  convert hl using 1

 theorem entry (hfit : offset+p.f*p.q≤p.before)
    (array : ActivePrefixEarlySequenceData.Array s rows) (x : Address s p rows) :
    ActivePrefixEarlySequenceData.result s p offset hfit rows array (index s p (EA x))=
      array (index s p x) := by
  rw [←destination_actual s p offset x]
  exact ActivePrefixEarlySequenceSemantics.entry s p offset hfit array x

 theorem entry_inverse (hfit : offset+p.f*p.q≤p.before)
    (array : ActivePrefixEarlySequenceData.Array s rows) (x : Address s p rows) :
    ActivePrefixEarlySequenceData.result s p offset hfit rows array (index s p x)=
      array (index s p ((EA).symm x)) := by
  simpa only [Equiv.apply_symm_apply] using entry s p offset hfit array ((EA).symm x)

end
end IntegerMultBounds.Machine.ActivePrefixEarlySequenceGlobal
