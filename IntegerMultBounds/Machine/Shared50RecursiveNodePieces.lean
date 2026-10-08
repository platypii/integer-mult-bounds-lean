import IntegerMultBounds.Machine.Shared50RecursiveNodeBinary
import IntegerMultBounds.Machine.RecursiveScalarIndex
import IntegerMultBounds.Machine.Shared50NodePieceTransport

/-! Actual segment/gate/recursive-call array execution produces the exact node
merge input. The only recursive premise is the explicit child interchange
contract at its selected wire; no replacement schedule or frame oracle. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveNodePieces
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50TapeGlobal (roleCount roleEquiv)
open RecursiveInterchangeLayout (Descriptor volume role)
open Shared50RecursiveNodeLayout (wires)
open Shared50RecursiveNodeSemantics (encoded networkData)
open Shared50RecursiveNodeBinary (splitWorld networkWorld)
open Shared50NodePieceTransport (Child ChildSpec run worldSlot)
variable {b u : ℕ} {v : Descriptor}

theorem run_network (hw : v.width=125000*b) (hd : roleCount ∣ v.rows)
    (child : Child (role v roleCount)) (hc : ChildSpec (v := role v roleCount) hw child)
    (x : Fin (volume prime v) → ZMod 2) :
    Shared50NodePieceTransport.run (v := role v roleCount) hw child Shared50PieceSchedule.pieces
      (RecursiveRowsSerialization.roleData wires (Equiv.refl _) hd (encoded x)) = networkData hw hd x := by
  rw [Shared50RecursiveNodeBinary.splitData_encoded,Shared50RecursiveNodeBinary.networkData_encoded]
  funext i z
  induction i using Fin.addCases with
  | left i =>
    obtain ⟨a,rfl⟩ := RecursiveScalarIndex.surjective (v := role v roleCount) hw z
    have he := Shared50NodePieceTransport.run_entry (v := role v roleCount) hw child hc (splitWorld hd x) (fun _ => blank) (roleEquiv i) a
    rw [← Shared50RecursiveNodeBinary.networkWorld_scalar hw hd x (roleEquiv i) a] at he
    simpa only [worldSlot,Equiv.symm_apply_apply,Shared50NodeGates.encoded,Shared50NodeGates.extend,
      Fin.addCases_left,Shared50RecursiveGates.encoded] using he
  | right i =>
    fin_cases i
    have he := congrFun (Shared50NodePieceTransport.run_io (v := role v roleCount) hw child hc Shared50PieceSchedule.pieces
      (Shared50NodeGates.encoded (splitWorld hd x) (fun _ => blank))) z
    exact he

/-- Physical restoration/merge now accepts the output of the actual piece
execution, rather than a separately supplied mathematical network result. -/
theorem exit_actual (hw : v.width=125000*b) (hd : roleCount ∣ v.rows)
    (child : Child (role v roleCount)) (hc : ChildSpec (v := role v roleCount) hw child)
    (x : Fin (volume prime v) → ZMod 2) (old hs : Fin 6 → List Bool)
    (st : Tapes 1 prime) (aux : Tapes u prime) (hav : RecursiveStackAllocation.Available 0 st)
    (hv : RecursiveDimensionBank.Headers v old) (hp : v.Positive) :
    HoareTime (Shared50RecursiveNodeLayout.exit (u := u)).program
      (fun w => w = SharedBankStageInput.raw
        (RecursiveViewFrameRoleBank.bank (RecursiveRoleSerialization.roles
          (Shared50NodePieceTransport.run (v := role v roleCount) hw child Shared50PieceSchedule.pieces
            (RecursiveRowsSerialization.roleData wires (Equiv.refl _) hd (encoded x))))
          hs (RecursiveViewFrame.savedStack old st) aux) (Shared50RecursiveNodeLayout.exit (u := u)).tapes)
      (fun w => w = SharedBankStageInput.raw
        (RecursiveViewFrameRoleBank.bank (RecursiveRoleSerialization.roles
          (RecursiveRowsSerialization.sourceData wires (Shared50RecursiveNodeRows.transpose hd (encoded x))))
          old st aux) (Shared50RecursiveNodeLayout.exit (u := u)).tapes)
      (RecursiveViewFrame.restoreCost old hs+RecursiveRowsClean.bound roleCount (volume prime v)+1) := by
  apply (Shared50RecursiveNodeSemantics.exit_network hw hd x old hs st aux hav hv hp).consequence _
    (fun _ h => h) le_rfl
  intro w he
  simpa only [run_network hw hd child hc x] using he

end
end IntegerMultBounds.Machine.Shared50RecursiveNodePieces
