import IntegerMultBounds.Machine.ActivePrefixDirtyControlSourceGeometry
import IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativePureData

/-! The actual shifted source projection emits precisely the selected X bits
in compact b-bit digits. The source-load and unload streams are evaluated at
every serialized row, including addresses outside the guarded region. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlSourceSemantics
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixLayoutFields ActivePrefixLayoutBack
open ActivePrefixDirtyControlSourceGeometry
open ActivePrefixDirtyControlSemantics (tempRow controls)
open BinaryAddressOffsetRepeatData (copies)
open BinaryAddressTableData (row)

variable (s : Shape) (p : Parameters s) (offset : ℕ) (hfit : offset+p.f*p.q≤p.after)
variable {rows : ℕ}

def selectedCompact (x : Address s p rows) :=
  ((afterControls s p x offset).map (fun z => z::List.replicate (p.b-1) false)).flatten

theorem source_field (x : Address s p rows) :
    tempRow (sourceShape s p offset hfit)
      (backRank s p x%2^(sourceShape s p offset hfit).W)=
        Gather.field (row p.after x.activeAfter.val) (offset+p.rho) (p.n*p.q) :=
  ActivePrefixLayoutGeometry.back_source_after s (p.n*p.b) (p.n*p.q) p.before p.after rows x
    (offset+p.rho) (p.n*p.q) (source_fits_after s p offset hfit)

theorem pure_gather (x : Address s p rows) :
    Gather.gather (fun z _ => z) (PackedArith.parity p.q p.b p.hb p.hbq)
      (tempRow (sourceShape s p offset hfit) (backRank s p x%2^(sourceShape s p offset hfit).W))
      (controls (sourceShape s p offset hfit) (backRank s p x%2^(sourceShape s p offset hfit).W)) p.n=
        selectedCompact s p offset x := by
  rw [source_field s p offset hfit x,Compact.PowerTwo.gather_flatten]
  unfold selectedCompact afterControls SelectedSourceBitsData.selected
  rw [List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  have hjn := List.mem_range.mp hj
  have hjq : j*p.q<p.n*p.q := Nat.mul_lt_mul_of_pos_right hjn (by have := p.hbq; omega)
  have hjf : p.rho+j*p.q<p.f*p.q := by
    have := p.hnf
    have := p.hr
    nlinarith
  have hd (X Z : List Bool) :
      Gather.digitWord (fun z _ => z) (PackedArith.parity p.q p.b p.hb p.hbq) X Z j=
        X.getD (j*p.q) false::List.replicate (p.b-1) false := by
    simp [Gather.digitWord,PackedArith.parity,Gather.field]
  rw [hd,ActivePrefixSelectedOffsetData.field_bit _ _ _ _ hjq]
  unfold afterSource
  simp only [Function.comp_apply]
  rw [ActivePrefixSelectedOffsetData.field_bit _ _ _ _ hjf]
  simp only [Nat.add_assoc]

theorem positive_row (x : Address s p rows) :
    Gather.field (copies (ActivePrefixDirtyControlPureBank.offsetWord (sourceShape s p offset hfit)) rows)
      (backRank s p x*(p.n*p.b)) (p.n*p.b)=selectedCompact s p offset x := by
  let l := sourceShape s p offset hfit
  rw [repeated_field _ (2^l.W) (p.n*p.b) rows (backRank s p x) (by positivity)
    (ActivePrefixDirtyControlPureBank.offset_length l) (back_rank_lt s p x)]
  change Gather.field (ActivePrefixDirtyControlPureBank.offsetWord l)
    (backRank s p x%2^l.W*(l.n*l.b)) (l.n*l.b)=_
  rw [ActivePrefixDirtyControlPureSemantics.offset_row l (backRank s p x%2^l.W) (Nat.mod_lt _ (by positivity))]
  exact pure_gather s p offset hfit x

theorem negative_row (x : Address s p rows) :
    Gather.field (copies (ActivePrefixDirtyControlNegativePureData.negative (sourceShape s p offset hfit)) rows)
      (backRank s p x*(p.n*p.b)) (p.n*p.b)=TwosComplement.negWord (selectedCompact s p offset x) := by
  let l := sourceShape s p offset hfit
  rw [repeated_field _ (2^l.W) (p.n*p.b) rows (backRank s p x) (by positivity)
    (ActivePrefixDirtyControlNegativePureData.negative_length l) (back_rank_lt s p x)]
  change Gather.field (ActivePrefixDirtyControlNegativePureData.negative l)
    (backRank s p x%2^l.W*(l.n*l.b)) (l.n*l.b)=_
  rw [ActivePrefixDirtyControlNegativePureData.negative_field l (backRank s p x%2^l.W) (Nat.mod_lt _ (by positivity))]
  exact congrArg TwosComplement.negWord (pure_gather s p offset hfit x)

end IntegerMultBounds.Machine.ActivePrefixDirtyControlSourceSemantics
