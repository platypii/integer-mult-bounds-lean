import IntegerMultBounds.Machine.ActiveTargetHighestLayoutGlobal
import IntegerMultBounds.Machine.ActiveTargetHighestBitsWords
import IntegerMultBounds.Machine.ActiveRepairLayoutPermutationFiber

/-! Highest-bit destinations implement the literal omitted selected-bit XOR
on the retained high interval of the containing target word. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLayoutWords
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes (Parameters Address)
open ActiveTargetHighestPairLayoutGeometry (sourceHigh)
open ActiveTargetHighestBits ActiveTargetHighestBitsWords
open BinaryAddressTableData
open Compact.ActiveTargetSubsegmentWords

variable (s : Shape) (p : Parameters s) (offset rows : ℕ)

def earlyControl (x : Address s p rows) := Nat.testBit x.activeBefore.val (sourceHigh s p offset)
def lateControl (x : Address s p rows) := Nat.testBit x.activeAfter.val (sourceHigh s p offset)

theorem early_word (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset)
    (x : Address s p rows) :
    row p.before (ActiveTargetHighestLayoutEarlyCoordinates.destination s p offset rows hfit hsource x).activeBefore.val=
      highest (earlyControl s p offset rows x) (row p.before x.activeBefore.val) := by
  let h := ActiveTargetHighestPairLayoutGeometry.source_high_lt s p offset p.before hfit
  let c := split p.before (sourceHigh s p offset) h x.activeBefore
  have hc : bool c.1.2=earlyControl s p offset rows x := source_bit _ _ _ _
  have hn : row (sourceHigh s p offset) c.2.val≠[] := by
    intro hh
    have := congrArg List.length hh
    rw [row_length,List.length_nil] at this
    omega
  change row p.before (join p.before (sourceHigh s p offset) h
    (c.1,toggle (sourceHigh s p offset) 0 hsource c.1.2 c.2)).val=_
  rw [row_join p.before (sourceHigh s p offset) h
    (c.1,toggle (sourceHigh s p offset) 0 hsource c.1.2 c.2),
    row_toggle_low (sourceHigh s p offset) hsource c.1.2 c.2,←hc,
    row_split p.before (sourceHigh s p offset) h x.activeBefore]
  change (highest (bool c.1.2) (row (sourceHigh s p offset) c.2.val)++[bool c.1.2])++
    row (p.before-sourceHigh s p offset-1) c.1.1.val=
      highest (bool c.1.2) ((row (sourceHigh s p offset) c.2.val++[bool c.1.2])++
        row (p.before-sourceHigh s p offset-1) c.1.1.val)
  rw [List.append_assoc,List.append_assoc,highest_append _ _ _ hn]

theorem late_word (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before)
    (x : Address s p rows) :
    row p.before (ActiveTargetHighestLayoutLateCoordinates.destination s p offset rows hfit hbefore x).activeBefore.val=
      highest (lateControl s p offset rows x) (row p.before x.activeBefore.val) := by
  have hc := source_bit p.after (sourceHigh s p offset)
    (ActiveTargetHighestPairLayoutGeometry.source_high_lt s p offset p.after hfit) x.activeAfter
  change row p.before (toggle p.before 0 _ _ x.activeBefore).val=_
  rw [row_toggle_low]
  change highest (bool (split p.after (sourceHigh s p offset) _ x.activeAfter).1.2) _=_
  rw [hc]
  rfl

/-- An arbitrary nonempty high interval receives its first-bit control after
the low ideal map; the result is exactly the complete selected mask. -/
theorem full_word (q : ℕ) (lo V hi Z : List Bool) (z : Bool)
    (hq : 1≤q) (hV : V.length=Z.length*q) (hhi : hi≠[]) :
    lo++CountedIdealToggle.word q V Z++highest z hi=
      List.zipWith xor (lo++V++hi)
        (List.replicate lo.length false++Compact.PowerTwo.toggleMask q Z++
          (z::List.replicate (hi.length-1) false)) := by
  cases hi with
  | nil => exact (hhi rfl).elim
  | cons a hi =>
    simpa only [ideal,List.length_cons,Nat.add_sub_cancel] using
      (full_selected q lo V hi Z z a hq hV).symm

theorem early_full_word (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset)
    (x : Address s p rows) (lo Z : List Bool) (hZ : Z.length=p.n) :
    lo++CountedIdealToggle.word p.q (row (p.n*p.q) x.target.val) Z++
      row p.before (ActiveTargetHighestLayoutEarlyCoordinates.destination s p offset rows hfit hsource x).activeBefore.val=
      List.zipWith xor (lo++row (p.n*p.q) x.target.val++row p.before x.activeBefore.val)
        (List.replicate lo.length false++Compact.PowerTwo.toggleMask p.q Z++
          (earlyControl s p offset rows x::List.replicate (p.before-1) false)) := by
  rw [early_word]
  have hpos := ActiveTargetHighestPairLayoutGeometry.source_high_lt s p offset p.before hfit
  have hh : row p.before x.activeBefore.val≠[] := by
    intro he; have := congrArg List.length he; rw [row_length,List.length_nil] at this; omega
  simpa only [row_length] using full_word p.q lo (row (p.n*p.q) x.target.val)
    (row p.before x.activeBefore.val) Z (earlyControl s p offset rows x) (by have := p.hbq; omega)
    (by rw [row_length,hZ]) hh

theorem late_full_word (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before)
    (x : Address s p rows) (lo Z : List Bool) (hZ : Z.length=p.n) :
    lo++CountedIdealToggle.word p.q (row (p.n*p.q) x.target.val) Z++
      row p.before (ActiveTargetHighestLayoutLateCoordinates.destination s p offset rows hfit hbefore x).activeBefore.val=
      List.zipWith xor (lo++row (p.n*p.q) x.target.val++row p.before x.activeBefore.val)
        (List.replicate lo.length false++Compact.PowerTwo.toggleMask p.q Z++
          (lateControl s p offset rows x::List.replicate (p.before-1) false)) := by
  rw [late_word]
  have hh : row p.before x.activeBefore.val≠[] := by
    intro he; have := congrArg List.length he; rw [row_length,List.length_nil] at this; omega
  simpa only [row_length] using full_word p.q lo (row (p.n*p.q) x.target.val)
    (row p.before x.activeBefore.val) Z (lateControl s p offset rows x) (by have := p.hbq; omega)
    (by rw [row_length,hZ]) hh

/-- The physically read highest control is exactly the omitted final element
of the same stride-q source selection used by the low repair permutation. -/
theorem selected_field_succ (width q rho n f offset : ℕ) (x : Fin (2^width))
    (hn : n+1=f) (hr : rho<q) :
    SelectedSourceBitsData.selected (Gather.field (row width x.val) offset (f*q)) q rho (n+1)=
      SelectedSourceBitsData.selected (Gather.field (row width x.val) offset (f*q)) q rho n++
        [Nat.testBit x.val (offset+rho+n*q)] := by
  have hi : rho+n*q<f*q := by nlinarith
  rw [SelectedSourceBitsData.selected_succ,ActivePrefixSelectedOffsetData.field_bit _ _ _ _ hi,
    ←Compact.PowerTwo.testBit_value,row_rank _ _ x.isLt]
  rw [Nat.add_assoc]

theorem early_selected (x : Address s p rows) :
    SelectedSourceBitsData.selected
      (ActiveRepairLayoutPermutationFiber.sourceWord p.before p.after offset (p.f*p.q) .before
        (x.activeBefore,x.activeAfter)) p.q p.rho (p.n+1)=
      ActiveRepairLayoutPermutationFiber.controlWord p.before p.after p.q p.rho p.n offset (p.f*p.q) .before
        (x.activeBefore,x.activeAfter)++[earlyControl s p offset rows x] :=
  selected_field_succ p.before p.q p.rho p.n p.f offset x.activeBefore p.hnf p.hr

theorem late_selected (x : Address s p rows) :
    SelectedSourceBitsData.selected
      (ActiveRepairLayoutPermutationFiber.sourceWord p.before p.after offset (p.f*p.q) .after
        (x.activeBefore,x.activeAfter)) p.q p.rho (p.n+1)=
      ActiveRepairLayoutPermutationFiber.controlWord p.before p.after p.q p.rho p.n offset (p.f*p.q) .after
        (x.activeBefore,x.activeAfter)++[lateControl s p offset rows x] :=
  selected_field_succ p.after p.q p.rho p.n p.f offset x.activeAfter p.hnf p.hr

end
end IntegerMultBounds.Machine.ActiveTargetHighestLayoutWords
