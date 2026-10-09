import IntegerMultBounds.Machine.ActivePrefixDirtyControlUSwapGeometry
import IntegerMultBounds.Machine.ActivePrefixCompactSwapGeometry
import IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationData

/-! Both executed compact swaps act at the literal original full-array index.
No reserialization or restricted-address assumption enters these equations. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalSwap
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes
open ActivePrefixDirtyControlConjugationData

variable (s : Shape) (p : Parameters s) {rows : ℕ}
def index (x : Address s p rows) := CompactActiveTargetLayout.index s (p.n*p.b) (p.n*p.q)
  p.before p.after rows p.compactFits p.activeSize x

theorem t_entry (array : FullArray s rows) (x : Address s p rows) :
    tSwap s rows (p.n*p.b) p.compactFits array (index s p x)=
      array (index s p (ActivePrefixLayoutSwap.swapT s p x)) := by
  rw [show index s p x=Fin.cast (ActivePrefixCompactSwapData.volume_eq s rows (p.n*p.b) p.compactFits)
    (ActivePrefixCompactSwapGeometry.index s p x) from (ActivePrefixCompactSwapGeometry.original_index s p x).symm]
  unfold tSwap view
  simp only [Fin.cast_cast,Fin.cast_eq_self]
  rw [ActivePrefixCompactSwapGeometry.transpose_entry]
  exact congrArg array (ActivePrefixCompactSwapGeometry.original_index s p _)

theorem u_entry (array : FullArray s rows) (x : Address s p rows) :
    uSwap s rows (p.n*p.b) p.compactFits array (index s p x)=
      array (index s p (ActivePrefixDirtyControlUSwapGeometry.swapU s p x)) := by
  rw [show index s p x=Fin.cast (ActivePrefixDirtyControlUSwapData.volume_eq s rows (p.n*p.b) p.compactFits)
    (ActivePrefixDirtyControlUSwapGeometry.index s p x) from (ActivePrefixDirtyControlUSwapGeometry.original_index s p x).symm]
  unfold uSwap view
  simp only [Fin.cast_cast,Fin.cast_eq_self]
  rw [ActivePrefixDirtyControlUSwapGeometry.transpose_entry]
  exact congrArg array (ActivePrefixDirtyControlUSwapGeometry.original_index s p _)

theorem t_involutive (x : Address s p rows) :
    ActivePrefixLayoutSwap.swapT s p (ActivePrefixLayoutSwap.swapT s p x)=x := by
  simp only [ActivePrefixLayoutSwap.swapT]
  have hr {a b : ℕ} (v : Fin (a*b)) : finProdFinEquiv (v.divNat,v.modNat)=v :=
    finProdFinEquiv.apply_symm_apply v
  simp [CompactActiveTargetGeometry.splitBack,RecursiveInterchangeRows.pack,hr]

theorem u_involutive (x : Address s p rows) :
    ActivePrefixDirtyControlUSwapGeometry.swapU s p (ActivePrefixDirtyControlUSwapGeometry.swapU s p x)=x := by
  simp only [ActivePrefixDirtyControlUSwapGeometry.swapU]
  have hr {a b : ℕ} (v : Fin (a*b)) : finProdFinEquiv (v.divNat,v.modNat)=v :=
    finProdFinEquiv.apply_symm_apply v
  simp [CompactActiveTargetGeometry.splitBack,RecursiveInterchangeRows.pack,hr]

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlGlobalSwap
