import IntegerMultBounds.Machine.ActivePrefixLayoutShapes
import IntegerMultBounds.Machine.ActivePrefixParityOnlyBank
import IntegerMultBounds.Machine.ActivePrefixParityNegativeData

/-! Compact back-fiber offsets read the current active target and the complete
source slot on either side of it. Outer repetition is arbitrary and every
lookup uses the actual serialized back-prefix rank modulo its inner range. -/
namespace IntegerMultBounds.Machine.ActivePrefixLayoutBack
open ActivePrefixLayoutShapes ActivePrefixLayoutFields
open BinaryAddressTableData (row)
open BinaryAddressOffsetRepeatData (copies)
open CompactGadgetReservationShape (Shape)

def beforeSource (s : Shape) (p : Parameters s) {rows : ℕ} (x : Address s p rows) (offset : ℕ) :=
  Gather.field (row p.before x.activeBefore.val) offset (p.f*p.q)
def afterSource (s : Shape) (p : Parameters s) {rows : ℕ} (x : Address s p rows) (offset : ℕ) :=
  Gather.field (row p.after x.activeAfter.val) offset (p.f*p.q)
def beforeControls (s : Shape) (p : Parameters s) {rows : ℕ} (x : Address s p rows) (offset : ℕ) :=
  SelectedSourceBitsData.selected (beforeSource s p x offset) p.q p.rho p.n
def afterControls (s : Shape) (p : Parameters s) {rows : ℕ} (x : Address s p rows) (offset : ℕ) :=
  SelectedSourceBitsData.selected (afterSource s p x offset) p.q p.rho p.n

theorem pure_row (sh : ActivePrefixParityOffsetBank.Shape) (rows rank : ℕ) (X Z : List Bool)
    (hrank : rank<rows*2^sh.W)
    (hx : Gather.field (prefixWord sh.W rank) sh.startT (sh.n*sh.q)=X)
    (hz : ActivePrefixSelectedOffsetData.controls sh.W sh.startX sh.q sh.rho sh.n sh.f (rank%2^sh.W)=Z) :
    Gather.field (copies (ActivePrefixParityOnlyBank.offsetWord sh) rows) (rank*(sh.n*sh.b)) (sh.n*sh.b)=
      Gather.gather (fun x _ => x) (PackedArith.parity sh.q sh.b sh.hb sh.hbq) X Z sh.n := by
  rw [repeated_field (ActivePrefixParityOnlyBank.offsetWord sh) (2^sh.W) (sh.n*sh.b) rows rank (by positivity)
    (ActivePrefixParityOnlyData.offsets_length _ _ _ _ _ _ _ _ _ _ _ _) hrank]
  have h := ActivePrefixParityOnlyData.offset_row sh.W sh.startT sh.startX sh.q sh.b sh.rho sh.n sh.f
    (rank%2^sh.W) sh.tempFits sh.sourceFits sh.hb sh.hbq sh.hnf sh.hr (Nat.mod_lt _ (by positivity))
  change Gather.field (ActivePrefixParityOnlyBank.offsetWord sh) _ _=_ at h
  rw [h,hz]
  change Gather.gather _ _ (Gather.field (prefixWord sh.W rank) sh.startT (sh.n*sh.q)) _ _=_
  rw [hx]

theorem negative_row (sh : ActivePrefixParityOffsetBank.Shape) (rows rank : ℕ) (X Z : List Bool)
    (hrank : rank<rows*2^sh.W)
    (hx : Gather.field (prefixWord sh.W rank) sh.startT (sh.n*sh.q)=X)
    (hz : ActivePrefixSelectedOffsetData.controls sh.W sh.startX sh.q sh.rho sh.n sh.f (rank%2^sh.W)=Z) :
    Gather.field (copies (ActivePrefixParityNegativeData.negative sh) rows) (rank*(sh.n*sh.b)) (sh.n*sh.b)=
      TwosComplement.negWord (Gather.gather xor (PackedArith.parity sh.q sh.b sh.hb sh.hbq) X Z sh.n) := by
  rw [repeated_field _ (2^sh.W) _ rows rank (by positivity)
    (ActivePrefixParityNegativeData.negative_length sh) hrank,
    ActivePrefixParityNegativeData.negative_field sh _ (Nat.mod_lt _ (by positivity)),hz]
  change TwosComplement.negWord (Gather.gather _ _
    (Gather.field (prefixWord sh.W rank) sh.startT (sh.n*sh.q)) _ _)=_
  rw [hx]

theorem before_source_field (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤p.before) {rows : ℕ} (x : Address s p rows) :
    ActivePrefixSelectedOffsetData.source (backBeforeShape s p offset hfit).W
      (backBeforeShape s p offset hfit).startX p.q p.f
      (backRank s p x%2^(backBeforeShape s p offset hfit).W)=beforeSource s p x offset :=
  ActivePrefixLayoutGeometry.back_source_before s (p.n*p.b) (p.n*p.q) p.before p.after rows x offset (p.f*p.q) hfit

theorem after_source_field (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤p.after) {rows : ℕ} (x : Address s p rows) :
    ActivePrefixSelectedOffsetData.source (backAfterShape s p offset hfit).W
      (backAfterShape s p offset hfit).startX p.q p.f
      (backRank s p x%2^(backAfterShape s p offset hfit).W)=afterSource s p x offset :=
  ActivePrefixLayoutGeometry.back_source_after s (p.n*p.b) (p.n*p.q) p.before p.after rows x offset (p.f*p.q) hfit

theorem before_control_field (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤p.before) {rows : ℕ} (x : Address s p rows) :
    ActivePrefixSelectedOffsetData.controls (backBeforeShape s p offset hfit).W
      (backBeforeShape s p offset hfit).startX p.q p.rho p.n p.f
      (backRank s p x%2^(backBeforeShape s p offset hfit).W)=beforeControls s p x offset := by
  unfold ActivePrefixSelectedOffsetData.controls beforeControls
  rw [before_source_field s p offset hfit x]

theorem after_control_field (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤p.after) {rows : ℕ} (x : Address s p rows) :
    ActivePrefixSelectedOffsetData.controls (backAfterShape s p offset hfit).W
      (backAfterShape s p offset hfit).startX p.q p.rho p.n p.f
      (backRank s p x%2^(backAfterShape s p offset hfit).W)=afterControls s p x offset := by
  unfold ActivePrefixSelectedOffsetData.controls afterControls
  rw [after_source_field s p offset hfit x]

theorem pure_before (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤p.before) {rows : ℕ} (x : Address s p rows) :
    Gather.field (copies (ActivePrefixParityOnlyBank.offsetWord (backBeforeShape s p offset hfit)) rows)
      (backRank s p x*(p.n*p.b)) (p.n*p.b)=
      Gather.gather (fun z _ => z) (PackedArith.parity p.q p.b p.hb p.hbq)
        (row (p.n*p.q) x.target.val) (beforeControls s p x offset) p.n :=
  pure_row _ rows (backRank s p x) _ _ (back_rank_lt s p x)
    (ActivePrefixLayoutGeometry.back_target s (p.n*p.b) (p.n*p.q) p.before p.after rows x)
    (before_control_field s p offset hfit x)

theorem pure_after (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤p.after) {rows : ℕ} (x : Address s p rows) :
    Gather.field (copies (ActivePrefixParityOnlyBank.offsetWord (backAfterShape s p offset hfit)) rows)
      (backRank s p x*(p.n*p.b)) (p.n*p.b)=
      Gather.gather (fun z _ => z) (PackedArith.parity p.q p.b p.hb p.hbq)
        (row (p.n*p.q) x.target.val) (afterControls s p x offset) p.n :=
  pure_row _ rows (backRank s p x) _ _ (back_rank_lt s p x)
    (ActivePrefixLayoutGeometry.back_target s (p.n*p.b) (p.n*p.q) p.before p.after rows x)
    (after_control_field s p offset hfit x)

theorem negative_before (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤p.before) {rows : ℕ} (x : Address s p rows) :
    Gather.field (copies (ActivePrefixParityNegativeData.negative (backBeforeShape s p offset hfit)) rows)
      (backRank s p x*(p.n*p.b)) (p.n*p.b)=
      TwosComplement.negWord (Gather.gather xor (PackedArith.parity p.q p.b p.hb p.hbq)
        (row (p.n*p.q) x.target.val) (beforeControls s p x offset) p.n) :=
  negative_row _ rows (backRank s p x) _ _ (back_rank_lt s p x)
    (ActivePrefixLayoutGeometry.back_target s (p.n*p.b) (p.n*p.q) p.before p.after rows x)
    (before_control_field s p offset hfit x)

theorem negative_after (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤p.after) {rows : ℕ} (x : Address s p rows) :
    Gather.field (copies (ActivePrefixParityNegativeData.negative (backAfterShape s p offset hfit)) rows)
      (backRank s p x*(p.n*p.b)) (p.n*p.b)=
      TwosComplement.negWord (Gather.gather xor (PackedArith.parity p.q p.b p.hb p.hbq)
        (row (p.n*p.q) x.target.val) (afterControls s p x offset) p.n) :=
  negative_row _ rows (backRank s p x) _ _ (back_rank_lt s p x)
    (ActivePrefixLayoutGeometry.back_target s (p.n*p.b) (p.n*p.q) p.before p.after rows x)
    (after_control_field s p offset hfit x)

end IntegerMultBounds.Machine.ActivePrefixLayoutBack
