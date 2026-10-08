import IntegerMultBounds.Machine.Shared50NodePieceTransport

/-! Fixed original-World parking order for the actual recursive call sites. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveCallLayout
noncomputable section
open Networks
open Shared50TapeGlobal (roleCount roleEquiv)
open Shared50GlobalBudget (World)
open Shared50NodeSegments (payloadCount io)
open Shared50NodePieceTransport (worldSlot)

/-- Fixed finite parking order, retaining the original World enumeration. -/
def parked (w : World) : List (Fin payloadCount) :=
  ((List.finRange roleCount).filter (fun i => i ≠ roleEquiv.symm w)).map (Fin.castAdd 1)

theorem parked_nodup (w : World) : (parked w).Nodup :=
  ((List.nodup_finRange roleCount).filter _).map (Fin.castAdd_injective roleCount 1)

theorem mem_parked (w : World) (k : Fin payloadCount) :
    k ∈ parked w ↔ k ≠ worldSlot w ∧ k ≠ io := by
  induction k using Fin.addCases with
  | left k =>
    have hn : Fin.castAdd 1 k ≠ io := by
      simpa only [worldSlot,Equiv.symm_apply_apply] using (Shared50NodePieceTransport.io_ne_worldSlot (roleEquiv k)).symm
    simp only [parked,List.mem_map,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
    constructor
    · rintro ⟨j,hj,he⟩
      have hjk := Fin.castAdd_injective _ _ he
      subst j
      exact ⟨(Fin.castAdd_injective roleCount 1).ne hj,hn⟩
    · intro hk
      exact ⟨k,fun he => hk.1 (congrArg (Fin.castAdd 1) he),rfl⟩
  | right k =>
    have he : Fin.natAdd roleCount k = io := by apply Fin.ext; have hk := k.isLt; simp only [io,Fin.val_natAdd,Fin.val_last]; omega
    rw [he]
    simp only [ne_eq,not_true_eq_false,and_false,iff_false]
    intro h
    obtain ⟨j,_,hj⟩ := List.mem_map.mp h
    exact Shared50NodePieceTransport.io_ne_worldSlot (roleEquiv j)
      (by simpa only [worldSlot,Equiv.symm_apply_apply] using hj.symm)

theorem active_not_parked (w : World) : worldSlot w ∉ parked w := by
  rw [mem_parked]; simp

theorem io_not_parked (w : World) : io ∉ parked w := by
  rw [mem_parked]; simp

theorem active_ne_io (w : World) : worldSlot w ≠ io :=
  (Shared50NodePieceTransport.io_ne_worldSlot w).symm

end
end IntegerMultBounds.Machine.Shared50RecursiveCallLayout
