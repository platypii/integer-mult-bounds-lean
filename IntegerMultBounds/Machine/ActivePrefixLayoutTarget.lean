import IntegerMultBounds.Machine.ActivePrefixLayoutShapes
import IntegerMultBounds.Machine.ActivePrefixCorrectionOffsetData

/-! First and third offset rows at the literal active-target fiber prefix.
The current compact T and the complete earlier source slot come directly from
that address; the generated inner table is repeated for arbitrary outer rows. -/
namespace IntegerMultBounds.Machine.ActivePrefixLayoutTarget
open ActivePrefixLayoutShapes ActivePrefixLayoutFields
open BinaryAddressTableData (row)
open BinaryAddressOffsetRepeatData (copies)
open CompactGadgetReservationShape (Shape)

def source (s : Shape) (p : Parameters s) {rows : ℕ} (x : Address s p rows) (offset : ℕ) :=
  Gather.field (row p.before x.activeBefore.val) offset (p.f*p.q)
def controls (s : Shape) (p : Parameters s) {rows : ℕ} (x : Address s p rows) (offset : ℕ) :=
  SelectedSourceBitsData.selected (source s p x offset) p.q p.rho p.n

variable (s : Shape) (p : Parameters s) (offset : ℕ) (hfit : offset+p.f*p.q≤p.before)
variable {rows : ℕ} (x : Address s p rows)

theorem temp_field :
    ActivePrefixSelectedOffsetData.temp (targetShape s p offset hfit).W
      (targetShape s p offset hfit).startT p.b p.n
      (targetRank s p x%2^(targetShape s p offset hfit).W)=row (p.n*p.b) x.t.val :=
  ActivePrefixLayoutGeometry.target_t s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits x

theorem source_field :
    ActivePrefixSelectedOffsetData.source (targetShape s p offset hfit).W offset p.q p.f
      (targetRank s p x%2^(targetShape s p offset hfit).W)=source s p x offset :=
  ActivePrefixLayoutGeometry.target_source s (p.n*p.b) (p.n*p.q) p.before p.after rows x offset (p.f*p.q) hfit

theorem control_field :
    ActivePrefixSelectedOffsetData.controls (targetShape s p offset hfit).W offset p.q p.rho p.n p.f
      (targetRank s p x%2^(targetShape s p offset hfit).W)=controls s p x offset := by
  unfold ActivePrefixSelectedOffsetData.controls controls
  rw [source_field s p offset hfit x]

theorem selected_row :
    Gather.field (copies (ActivePrefixSelectedOffsetBank.offsetWord (targetShape s p offset hfit)) rows)
      (targetRank s p x*(p.n*p.q)) (p.n*p.q)=
      Gather.gather (fun z c => z && c) (PackedArith.maskShift p.q p.b p.hb p.hbq)
        (row (p.n*p.b) x.t.val) (controls s p x offset) p.n := by
  let sh := targetShape s p offset hfit
  have hr := repeated_field (ActivePrefixSelectedOffsetBank.offsetWord sh) (2^sh.W) (p.n*p.q)
    rows (targetRank s p x) (by positivity)
    (ActivePrefixSelectedOffsetData.offsets_length _ _ _ _ _ _ _ _ _ _ _ _) (target_rank_lt s p x)
  rw [hr]
  have h := ActivePrefixSelectedOffsetData.offset_row sh.W sh.startT sh.startX sh.q sh.b sh.rho sh.n sh.f
    (targetRank s p x%2^sh.W) sh.tempFits sh.sourceFits sh.hb sh.hbq sh.hnf sh.hr (Nat.mod_lt _ (by positivity))
  change Gather.field (ActivePrefixSelectedOffsetBank.offsetWord sh) _ _=_ at h
  have ht := temp_field s p offset hfit x
  have hc := control_field s p offset hfit x
  dsimp only [sh,targetShape] at h ht hc
  rw [ht,hc] at h
  exact h

theorem correction_row :
    Gather.field (copies (ActivePrefixCorrectionOffsetData.word (targetShape s p offset hfit)) rows)
      (targetRank s p x*(p.n*p.q)) (p.n*p.q)=
      BinaryCorrectionOffsetRow.diff (Compact.PowerTwo.toggleMask p.q (controls s p x offset))
        (Gather.gather (fun z c => z && c) (PackedArith.maskShift p.q p.b p.hb p.hbq)
          (row (p.n*p.b) x.t.val) (controls s p x offset) p.n) := by
  let sh := targetShape s p offset hfit
  have hr := repeated_field (ActivePrefixCorrectionOffsetData.word sh) (2^sh.W) (p.n*p.q)
    rows (targetRank s p x) (by positivity) (ActivePrefixCorrectionOffsetData.word_length sh) (target_rank_lt s p x)
  rw [hr]
  have h := ActivePrefixCorrectionOffsetData.current_prefix_row sh (targetRank s p x%2^sh.W)
    (Nat.mod_lt _ (by positivity))
  have ht := temp_field s p offset hfit x
  have hc := control_field s p offset hfit x
  dsimp only [sh,targetShape] at h ht hc
  rw [ht,hc] at h
  exact h

/-- The prefix used above is the existing contiguous active-target fiber in
the original serialized array, including every spectator and payload value. -/
theorem target_fiber_index (s : Shape) (p : Parameters s) {rows : ℕ} (x : Address s p rows) :
    Fin.cast (CompactActiveTargetGeometry.target_volume s (p.n*p.b) (p.n*p.q) p.before p.after rows
      p.compactFits p.activeSize)
      (CompactActiveTargetGeometry.targetIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows x)=
      CompactActiveTargetLayout.index s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize x :=
  CompactActiveTargetGeometry.target_index _ _ _ _ _ _ _ _ _

end IntegerMultBounds.Machine.ActivePrefixLayoutTarget
