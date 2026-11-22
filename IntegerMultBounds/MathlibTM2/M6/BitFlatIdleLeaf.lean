module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleCall
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryLeaf

/-! Execute a stopped child directly at the physical interval of its remainder owner. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

theorem inheritedLeaf_exec [M8.Machine.Net] {n Q V : ℕ} {P U : Type}
    (capacity : columnCapacity ≤ Q) (body : P → Pr P (n+LeafCore.small) Q prime U)
    (src : Fin 6 → Fin n) (port : Fin n) (child interval : Descriptor)
    (size : volume prime interval = V) (position : Fin (volume prime child) ≃ Fin V)
    (width : interval.width = child.width) (coords : InheritedIntervalPositions child interval size position)
    (word : Fin V → ZMod 2) (u : HS (n+LeafCore.small) Q prime U) (S : Stacks (n+LeafCore.small) prime)
    (positive : 0 < V) (headers : ∀ j, S.R ((src j).castAdd LeafCore.small) = (Routines.hdr interval j).map bitSymbol)
    (payload : RecordPayload (port.castAdd LeafCore.small) (fun _ => blank) 0 word S)
    (free : ∀ j : Fin LeafCore.small, S.L (j.natAdd n) = [] ∧ S.R (j.natAdd n) = []) :
    ∃ z F steps changed, Exec body (hostedStoppedDirectory capacity src port) (mk u S) steps (mk z F) ∧
      (steps : ℝ) ≤ descriptorHeaderCost interval +
        ((LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|))*
        ((V : ℝ)*((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
      z.user = u.user ∧ RecordPayload (port.castAdd LeafCore.small) (fun _ => blank) 0 changed F ∧
      (∀ t, t ≠ port.castAdd LeafCore.small → F.L t = S.L t ∧ F.R t = S.R t) ∧
      ∀ k, changed (position k) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) k := by
  subst V
  obtain ⟨z,F,steps,user,run,paid,out,_,keep,clean⟩ :=
    hostedStoppedView_exec capacity body src port interval word u S positive headers payload free
  refine ⟨z,F,steps,_,run,width ▸ paid,user,out,?_,?_⟩
  · intro t
    refine Fin.addCases (fun j ne => keep j (fun eq => ne (congrArg (fun t : Fin n => t.castAdd LeafCore.small) eq)))
      (fun j _ => ⟨(clean j).1.trans (free j).1.symm,(clean j).2.trans (free j).2.symm⟩) t
  · exact (coords.transpose_iff width word _).2 (by rfl)

end IntegerMultBounds.MathlibTM2.M6.BitNode
