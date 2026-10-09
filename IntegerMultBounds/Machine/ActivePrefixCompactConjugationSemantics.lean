import IntegerMultBounds.Machine.ActivePrefixCompactConjugationLayout

/-! Literal compact-T destination semantics of the complete physical
conjugation, for both source orders and both parity load branches. -/
namespace IntegerMultBounds.Machine.ActivePrefixCompactConjugationSemantics
noncomputable section
open ActivePrefixCompactConjugationData ActivePrefixCompactConjugationLayout
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes CompactActiveTargetGeometry
open ActivePrefixCompactSwapGeometry (index original_index transpose_entry)
open ActivePrefixLayoutSwap (swapT split_swap)
open RecursiveInterchangeRows (pack)

variable (side : Side) (s : Shape) (p : Parameters s) (offset : ℕ)
variable (hfit : offset+p.f*p.q≤sourceRoom side s p) {rows : ℕ}

def prefixIndex (x : Address s p rows) :
    Fin (ActivePrefixCompactParityLoadData.prefixCount (shape side s p offset hfit) rows) :=
  match side with
  | .before => ActivePrefixCompactParityLoadLayout.prefixIndex s p offset hfit x
  | .after => ActivePrefixCompactParityLoadLayoutAfter.prefixIndex s p offset hfit x

theorem index_to_fiber (x : Address s p rows) :
    Fin.cast (alignment side s p offset hfit rows) (index s p x)=
      FiberLayoutData.index (prefixIndex side s p offset hfit x)
        (splitBack s (p.n*p.b) p.compactFits x.back).1
        (pack (splitBack s (p.n*p.b) p.compactFits x.back).2 x.payload) := by
  apply Fin.ext
  have h₁ := congrArg Fin.val (original_index s p x)
  cases side with
  | before =>
    have h₂ := congrArg Fin.val (ActivePrefixCompactParityLoadLayout.source_index s p offset hfit x)
    exact h₁.trans h₂.symm
  | after =>
    have h₂ := congrArg Fin.val (ActivePrefixCompactParityLoadLayoutAfter.source_index s p offset hfit x)
    exact h₁.trans h₂.symm

theorem prefix_destination (kind : Kind) (x : Address s p rows) :
    prefixIndex side s p offset hfit (swapT s p (destination kind side s p offset x))=
      prefixIndex side s p offset hfit (swapT s p x) := by
  cases side <;> rfl

theorem load_entry (kind : Kind) (array : ActivePrefixCompactSwapData.Array s rows (p.n*p.b))
    (x : Address s p rows) :
    loadResult kind (shape side s p offset hfit) rows (suffix s p)
      (view (alignment side s p offset hfit rows) array)
      (Fin.cast (alignment side s p offset hfit rows)
        (index s p (swapT s p (destination kind side s p offset x))))=
      array (index s p (swapT s p x)) := by
  rw [index_to_fiber,prefix_destination,split_swap]
  let full := view (ActivePrefixCompactSwapData.volume_eq s rows (p.n*p.b) p.compactFits) array
  have hidx : full (CompactActiveTargetLayout.index s (p.n*p.b) (p.n*p.q) p.before p.after rows
      p.compactFits p.activeSize (swapT s p x))=array (index s p (swapT s p x)) := by
    rw [←original_index]
    rfl
  cases kind <;> cases side
  · have h := ActivePrefixCompactParityLoadLayout.after_swap_entry s p offset hfit full x
    rw [hidx] at h
    exact h
  · have h := ActivePrefixCompactParityLoadLayoutAfter.after_swap_entry s p offset hfit full x
    rw [hidx] at h
    exact h
  · have h := ActivePrefixCompactNegativeLoadLayout.after_swap_entry s p offset hfit full x
    rw [hidx] at h
    exact h
  · have h := ActivePrefixCompactNegativeLoadLayoutAfter.after_swap_entry s p offset hfit full x
    rw [hidx] at h
    exact h

/-- Original T alone is shifted by the actual target/source offset. Dirty back
bits, target, sources, other active coordinates and every payload bit survive. -/
theorem entry (kind : Kind) (array : ActivePrefixCompactSwapData.Array s rows (p.n*p.b))
    (x : Address s p rows) :
    ActivePrefixCompactConjugationRun.result kind s (shape side s p offset hfit) rows (p.n*p.b)
      (suffix s p) (alignment side s p offset hfit rows) array
      (index s p (destination kind side s p offset x))=array (index s p x) := by
  unfold ActivePrefixCompactConjugationRun.result
  rw [transpose_entry]
  change loadResult kind (shape side s p offset hfit) rows (suffix s p)
    (view (alignment side s p offset hfit rows) (RadixRangePadding.transpose array))
    (Fin.cast (alignment side s p offset hfit rows)
      (index s p (swapT s p (destination kind side s p offset x))))=_
  rw [load_entry]
  have h := transpose_entry s p (RadixRangePadding.transpose array) x
  rw [BinaryPackedFieldSwap.transpose_involutive] at h
  exact h.symm

end
end IntegerMultBounds.Machine.ActivePrefixCompactConjugationSemantics
