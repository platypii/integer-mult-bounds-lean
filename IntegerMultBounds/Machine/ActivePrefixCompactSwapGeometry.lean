import IntegerMultBounds.Machine.ActivePrefixCompactSwapRun

/-! Exact physical interchange geometry for compact T in the unchanged active
layout. Only compact n*b fits H; the target n*q remains in the active block. -/
namespace IntegerMultBounds.Machine.ActivePrefixCompactSwapGeometry
noncomputable section
open ActivePrefixCompactSwapData
open CompactGadgetReservationShape (Shape)
open CompactActiveTargetGeometry
open ActivePrefixLayoutShapes
open RecursiveInterchangeRows (pack pack_val)

variable (s : Shape) (p : Parameters s) {rows : ℕ}

def prefixIndex (x : Address s p rows) : Fin (P s rows) :=
  Fin.cast (t_prefix_carved s (p.n*p.b) rows p.compactFits) (pack (pack x.row x.u) x.uTail)
def gapIndex (x : Address s p rows) : Fin (G s (p.n*p.b)) :=
  Fin.cast (t_gap_carved s (p.n*p.b) (p.n*p.q) p.before p.after p.activeSize)
    (pack (pack (pack (pack x.tTail x.frontSlack) x.activeBefore) x.target) x.activeAfter)
def suffixIndex (x : Address s p rows) : Fin (B s (p.n*p.b)) :=
  pack (splitBack s (p.n*p.b) p.compactFits x.back).2 x.payload

def index (x : Address s p rows) : Fin (volume s rows (p.n*p.b)) :=
  RadixRangePadding.index (prefixIndex s p x) x.t (gapIndex s p x)
    (splitBack s (p.n*p.b) p.compactFits x.back).1 (suffixIndex s p x)

theorem prefix_val (x : Address s p rows) :
    (prefixIndex s p x).val=(pack (pack x.row x.u) x.uTail).val := rfl
theorem gap_val (x : Address s p rows) :
    (gapIndex s p x).val=(pack (pack (pack (pack x.tTail x.frontSlack) x.activeBefore) x.target) x.activeAfter).val := rfl
theorem suffix_val (x : Address s p rows) :
    (suffixIndex s p x).val=(pack (splitBack s (p.n*p.b) p.compactFits x.back).2 x.payload).val := rfl

theorem index_val (x : Address s p rows) :
    (index s p x).val=(tIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits x).val := by
  simp only [index,tIndex,RadixRangePadding.index,pack_val,prefix_val,gap_val,suffix_val]
  have he : G s (p.n*p.b)=2^(s.H-p.n*p.b)*2^s.F*2^p.before*2^(p.n*p.q)*2^p.after :=
    (t_gap_carved s (p.n*p.b) (p.n*p.q) p.before p.after p.activeSize).symm
  rw [he]
  rfl

theorem original_index (x : Address s p rows) :
    Fin.cast (volume_eq s rows (p.n*p.b) p.compactFits) (index s p x)=
      CompactActiveTargetLayout.index s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize x := by
  apply Fin.ext
  exact (index_val s p x).trans (congrArg Fin.val
    (t_index s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize x))

/-- The returned physical word implements exactly the actual compact T/back
swap, retaining target, both source regions, dirty tails and all payload bits. -/
theorem transpose_entry (array : Array s rows (p.n*p.b)) (x : Address s p rows) :
    RadixRangePadding.transpose array (index s p x)=
      array (index s p (ActivePrefixLayoutSwap.swapT s p x)) := by
  unfold index
  rw [RadixRangePadding.transpose_entry,ActivePrefixLayoutSwap.split_swap]
  have hs : suffixIndex s p (ActivePrefixLayoutSwap.swapT s p x)=suffixIndex s p x := by
    unfold suffixIndex
    rw [ActivePrefixLayoutSwap.split_swap]
    rfl
  rw [hs]
  rfl

end
end IntegerMultBounds.Machine.ActivePrefixCompactSwapGeometry
