import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
import IntegerMultBounds.Machine.RawLinearCombination

/-! Physical erasure of marked arithmetic source fields at fixed tape slots.
The control list is compiled once; field lengths and values are runtime data. -/
namespace IntegerMultBounds.Machine.RadixControlCleanupList
noncomputable section
open SharedPlacementAlphabet (setTape)
open BinaryDescriptorCleanupList (states cleared cleared_frame cleared_slot)
variable {t q : ℕ}

def program (ht : 0<t) (ops : List (Fin t)) : Program t (states ops) q :=
  BinaryDescriptorCleanupList.program ht ops

theorem one_runs (slot : Fin t) (v : Tapes t q) (xs : List (Fin q))
    (ht : v.tape slot=MarkedRadixRefresh.source xs) (hh : v.head slot=1) :
    HoareTime (BinaryDescriptorCleanupList.oneProgram slot) (fun w => w=v)
      (fun w => w=setTape v slot (fun _ => blank) 0) (2*xs.length+4) := by
  have hi : Placement.active (FiniteReturnStackAt.placement slot) v=
      MarkedWordCleanup.one (MarkedWordCleanup.marked (xs.map RadixDigits.digitSymbol)) 1 := by
    rw [FiniteReturnStackAt.active_bank,ht,hh]
    rfl
  have h := Placement.hoare_at (RawLinearCombinationCleanup.marked_radix xs)
    (FiniteReturnStackAt.placement slot) v hi
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

def cost (ops : List (Fin t)) (xs : Fin t → List (Fin q)) : ℕ :=
  (ops.map (fun i => 2*(xs i).length+5)).sum

theorem runs (ht : 0<t) (ops : List (Fin t)) (hu : ops.Nodup)
    (xs : Fin t → List (Fin q)) (v : Tapes t q)
    (hs : ∀ i∈ops,v.head i=1 ∧ v.tape i=MarkedRadixRefresh.source (xs i)) :
    HoareTime (program ht ops) (fun w => w=v) (fun w => w=cleared ops v) (cost ops xs) := by
  induction ops generalizing v with
  | nil => exact skip_hoare ht v
  | cons i ops ih =>
    have hh := List.nodup_cons.mp hu
    have h0 := hs i List.mem_cons_self
    have htail := ih hh.2 (setTape v i (fun _ => blank) 0) (by
      intro j hj
      have hn : j≠i := fun he => hh.1 (he ▸ hj)
      simpa only [setTape,Function.update_of_ne hn] using hs j (List.mem_cons_of_mem _ hj))
    exact ((one_runs i v (xs i) h0.2 h0.1).seq htail).consequence
      (fun _ h => h) (fun _ h => h) (by simp only [cost,List.map_cons,List.sum_cons]; omega)

theorem cost_uniform (ops : List (Fin t)) (xs : Fin t → List (Fin q)) (w : ℕ)
    (hw : ∀ i∈ops,(xs i).length=w) : cost ops xs=ops.length*(2*w+5) := by
  induction ops with
  | nil => simp [cost]
  | cons i ops ih =>
    have h0 := hw i List.mem_cons_self
    have ht := ih (fun j hj => hw j (List.mem_cons_of_mem _ hj))
    simp only [cost,List.map_cons,List.sum_cons,h0,List.length_cons] at *
    rw [ht]
    ring

end
end IntegerMultBounds.Machine.RadixControlCleanupList
