import IntegerMultBounds.Machine.ActivePrefixDirtyControlUSwapPlaced

/-! Literal compact U/back interchange on the unchanged full-array address.
Every coordinate apart from U and the high back field remains in place. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlUSwapGeometry
noncomputable section
open ActivePrefixDirtyControlUSwapData
open CompactGadgetReservationShape (Shape)
open CompactActiveTargetGeometry
open ActivePrefixLayoutShapes
open RecursiveInterchangeRows (pack pack_val)

variable (s : Shape) (p : Parameters s) {rows : ℕ}

def swapU (x : Address s p rows) : Address s p rows :=
  { x with
    u := (splitBack s (p.n*p.b) p.compactFits x.back).1
    back := Fin.cast (back_size s (p.n*p.b) p.compactFits).symm
      (pack x.u (splitBack s (p.n*p.b) p.compactFits x.back).2) }

theorem split_swap (x : Address s p rows) :
    splitBack s (p.n*p.b) p.compactFits (swapU s p x).back=
      (x.u,(splitBack s (p.n*p.b) p.compactFits x.back).2) := by
  simp [swapU,splitBack,pack]

def prefixIndex (x : Address s p rows) : Fin (P s rows) :=
  Fin.cast (by simp [P,Shape.prefixRange,Shape.prefixBits]) x.row
def gapIndex (x : Address s p rows) : Fin (G s (p.n*p.b)) :=
  Fin.cast (u_gap_carved s (p.n*p.b) (p.n*p.q) p.before p.after p.compactFits p.activeSize)
    (pack (pack (pack (pack (pack (pack x.uTail x.t) x.tTail) x.frontSlack) x.activeBefore) x.target) x.activeAfter)
def suffixIndex (x : Address s p rows) : Fin (B s (p.n*p.b)) :=
  pack (splitBack s (p.n*p.b) p.compactFits x.back).2 x.payload

def index (x : Address s p rows) : Fin (volume s rows (p.n*p.b)) :=
  RadixRangePadding.index (prefixIndex s p x) x.u (gapIndex s p x)
    (splitBack s (p.n*p.b) p.compactFits x.back).1 (suffixIndex s p x)

theorem prefix_val (x : Address s p rows) : (prefixIndex s p x).val=x.row.val := rfl
theorem gap_val (x : Address s p rows) :
    (gapIndex s p x).val=(pack (pack (pack (pack (pack (pack x.uTail x.t) x.tTail) x.frontSlack) x.activeBefore) x.target) x.activeAfter).val := rfl
theorem suffix_val (x : Address s p rows) :
    (suffixIndex s p x).val=(pack (splitBack s (p.n*p.b) p.compactFits x.back).2 x.payload).val := rfl

theorem index_val (x : Address s p rows) :
    (index s p x).val=(uIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits x).val := by
  simp only [index,uIndex,RadixRangePadding.index,pack_val,prefix_val,gap_val,suffix_val]
  have he : G s (p.n*p.b)=2^(s.H-p.n*p.b)*2^(p.n*p.b)*2^(s.H-p.n*p.b)*
      2^s.F*2^p.before*2^(p.n*p.q)*2^p.after :=
    (u_gap_carved s (p.n*p.b) (p.n*p.q) p.before p.after p.compactFits p.activeSize).symm
  rw [he]
  rfl

theorem original_index (x : Address s p rows) :
    Fin.cast (volume_eq s rows (p.n*p.b) p.compactFits) (index s p x)=
      CompactActiveTargetLayout.index s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize x := by
  apply Fin.ext
  exact (index_val s p x).trans (congrArg Fin.val
    (u_index s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize x))

theorem transpose_entry (array : Array s rows (p.n*p.b)) (x : Address s p rows) :
    RadixRangePadding.transpose array (index s p x)=array (index s p (swapU s p x)) := by
  unfold index
  rw [RadixRangePadding.transpose_entry,split_swap]
  have hs : suffixIndex s p (swapU s p x)=suffixIndex s p x := by
    unfold suffixIndex
    rw [split_swap]
    rfl
  rw [hs]
  rfl

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlUSwapGeometry
