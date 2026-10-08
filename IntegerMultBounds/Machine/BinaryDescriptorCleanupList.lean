import IntegerMultBounds.Machine.MarkedBinaryCleanup
import IntegerMultBounds.Machine.FiniteReturnStackAt
import IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip
import IntegerMultBounds.Machine.ExactFrame

/-! Physically erase a fixed list of retained binary headers. Every bit and
sentinel is erased, every head returns to zero, and all other tapes are framed.
Neither descriptor lengths nor a reset oracle enter the finite control. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorCleanupList
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}
noncomputable section

def oneProgram (slot : Fin t) : Program t 4 a :=
  Placement.placed MarkedBinaryCleanup.program (FiniteReturnStackAt.placement slot)

theorem one_hoare (slot : Fin t) (v : Tapes t a) (xs : List Bool)
    (ht : v.tape slot = BinaryDescriptorStack.descriptor xs) (hh : v.head slot = 1) :
    HoareTime (oneProgram slot) (fun w => w = v)
      (fun w => w = setTape v slot (fun _ => blank) 0) (2*xs.length+4) := by
  have hi : Placement.active (FiniteReturnStackAt.placement slot) v = RadixToBinary.binaryState a xs := by
    rw [FiniteReturnStackAt.active_bank,ht,hh,BinaryDescriptorStackRoundtrip.descriptor_encoded]
    rfl
  have h := Placement.hoare_at (MarkedBinaryCleanup.cleanup_hoare (q := a) xs)
    (FiniteReturnStackAt.placement slot) v hi
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

def states : List (Fin t) → ℕ
  | [] => 1
  | _::ops => 4+states ops

def program (ht : 0 < t) : (ops : List (Fin t)) → Program t (states ops) a
  | [] => skip t a ht
  | i::ops => seq (oneProgram i) (program ht ops)

def cleared : List (Fin t) → Tapes t a → Tapes t a
  | [],v => v
  | i::ops,v => cleared ops (setTape v i (fun _ => blank) 0)

def cost (ops : List (Fin t)) (xs : Fin t → List Bool) : ℕ :=
  (ops.map (fun i => 2*(xs i).length+5)).sum

theorem states_eq (ops : List (Fin t)) : states ops = 4*ops.length+1 := by
  induction ops with
  | nil => rfl
  | cons i ops ih => simp only [states,List.length_cons,ih]; omega

theorem cleared_frame (ops : List (Fin t)) (v : Tapes t a) (i : Fin t) (hi : i ∉ ops) :
    (cleared ops v).head i = v.head i ∧ (cleared ops v).tape i = v.tape i := by
  induction ops generalizing v with
  | nil => exact ⟨rfl,rfl⟩
  | cons j ops ih =>
    have hn : i ≠ j := fun h => hi (List.mem_cons.mpr (Or.inl h))
    have ht : i ∉ ops := fun h => hi (List.mem_cons_of_mem _ h)
    simpa only [cleared,setTape,Function.update_of_ne hn] using ih (setTape v j (fun _ => blank) 0) ht

theorem cleared_slot (ops : List (Fin t)) (hu : ops.Nodup) (v : Tapes t a) (i : Fin t) (hi : i ∈ ops) :
    (cleared ops v).head i = 0 ∧ (cleared ops v).tape i = fun _ => blank := by
  induction ops generalizing v with
  | nil => exact (List.not_mem_nil hi).elim
  | cons j ops ih =>
    have hh := List.nodup_cons.mp hu
    rcases List.mem_cons.mp hi with rfl | hi
    · simpa only [cleared,setTape,Function.update_self] using cleared_frame ops (setTape v i (fun _ => blank) 0) i hh.1
    · exact ih hh.2 _ hi

theorem cleanup_hoare (ht : 0 < t) (ops : List (Fin t)) (hu : ops.Nodup)
    (xs : Fin t → List Bool) (v : Tapes t a)
    (hs : ∀ i ∈ ops, v.head i = 1 ∧ v.tape i = BinaryDescriptorStack.descriptor (xs i)) :
    HoareTime (program ht ops) (fun w => w = v) (fun w => w = cleared ops v) (cost ops xs) := by
  induction ops generalizing v with
  | nil => exact skip_hoare ht v
  | cons i ops ih =>
    have hh := List.nodup_cons.mp hu
    have h0 := hs i List.mem_cons_self
    have ht' := ih hh.2 (setTape v i (fun _ => blank) 0) (by
      intro j hj
      have hn : j ≠ i := fun he => hh.1 (he ▸ hj)
      simpa only [setTape,Function.update_of_ne hn] using hs j (List.mem_cons_of_mem _ hj))
    exact ((one_hoare i v (xs i) h0.2 h0.1).seq ht').consequence (fun _ h => h) (fun _ h => h)
      (by simp only [cost,List.map_cons,List.sum_cons]; omega)

theorem cost_eq (ops : List (Fin t)) (xs : Fin t → List Bool) :
    cost ops xs = 2*(ops.map (fun i => (xs i).length)).sum+5*ops.length := by
  induction ops with
  | nil => rfl
  | cons i ops ih => simp only [cost,List.map_cons,List.sum_cons,List.length_cons] at *; omega

theorem cost_le (ops : List (Fin t)) (xs : Fin t → List Bool) (L : ℕ)
    (hL : ∀ i ∈ ops, (xs i).length ≤ L) : cost ops xs ≤ ops.length*(2*L+5) := by
  induction ops with
  | nil => simp [cost]
  | cons i ops ih =>
    have h0 := hL i List.mem_cons_self
    have ht := ih (fun j hj => hL j (List.mem_cons_of_mem _ hj))
    simp only [cost,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

end
end IntegerMultBounds.Machine.BinaryDescriptorCleanupList
