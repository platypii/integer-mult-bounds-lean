import IntegerMultBounds.Machine.Shared50RecursiveNodeBinary

/-! Actual fixed Shared50 node entry/exit contracts on the binary World bank.
All header and movement work is charged; the saved descriptor stack supports
nested calls through its preserved blank suffix. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveNodeBoundary
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50TapeGlobal (roleCount)
open RecursiveInterchangeLayout (Descriptor volume role)
open Shared50RecursiveNodeLayout (wires entry exit)
open Shared50RecursiveNodeSemantics (encoded)
open Shared50RecursiveNodeBinary (splitWorld networkWorld)
open RecursiveViewFrameRoleBank (bank)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)
variable {u : ℕ} {v : Descriptor}

def entryConstant := 74+RecursiveRowsNode.rowConstant roleCount+RecursiveRowsNodeRoleBank.constant roleCount
def exitConstant := 128+RecursiveRowsNode.rowConstant roleCount

theorem enter_binary (hd : roleCount ∣ v.rows) (x : Fin (volume prime v) → ZMod 2)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive)
    (st : Tapes 1 prime) (aux : Tapes u prime) (hav : RecursiveStackAllocation.Available 0 st) :
    ∃ rs : List Bool, RecursiveDimensionBank.Headers (role v roleCount) (RecursiveRowsNodeHeaders.headers hs rs) ∧
      RecursiveStackAllocation.Available 0 (RecursiveViewFrame.savedStack hs st) ∧
      HoareTime (entry (u := u)).program
        (fun w => w = raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs st aux)
          (entry (u := u)).tapes)
        (fun w => w = raw (bank (roles (Shared50NodeGates.encoded (splitWorld hd x) (fun _ => blank)))
          (RecursiveRowsNodeHeaders.headers hs rs) (RecursiveViewFrame.savedStack hs st) aux)
          (entry (u := u)).tapes)
        ((74+RecursiveRowsNode.rowConstant roleCount+RecursiveRowsNodeRoleBank.constant roleCount)*volume prime v) := by
  obtain ⟨rs,hrs,hh⟩ := RecursiveRowsNode.entry_hoare (c := roleCount) wires Shared50RecursiveNodeLayout.wires_injective
    hs st aux v (by decide) hv hp hd (encoded x)
  refine ⟨rs,hrs,RecursiveRowsNode.saved_available hs st hav,?_⟩
  apply hh.consequence (fun _ h => h) _ (RecursiveRowsNode.entry_cost_linear (c := roleCount) v hp hs hv)
  intro w h
  simpa only [Shared50RecursiveNodeBinary.splitData_encoded,entry] using h

theorem exit_binary {b : ℕ} (hw : v.width=125000*b) (hd : roleCount ∣ v.rows)
    (x : Fin (volume prime v) → ZMod 2) (old hs : Fin 6 → List Bool)
    (ho : RecursiveDimensionBank.Headers v old) (hh : RecursiveDimensionBank.Headers (role v roleCount) hs)
    (hp : v.Positive) (st : Tapes 1 prime) (aux : Tapes u prime)
    (hav : RecursiveStackAllocation.Available 0 st) :
    HoareTime (exit (u := u)).program
      (fun w => w = raw (bank (roles (Shared50NodeGates.encoded (networkWorld hw hd x) (fun _ => blank)))
        hs (RecursiveViewFrame.savedStack old st) aux) (exit (u := u)).tapes)
      (fun w => w = raw (bank (roles (RecursiveRowsSerialization.sourceData wires
        (encoded (Shared50RecursiveNodeRows.transpose hd x)))) old st aux) (exit (u := u)).tapes)
      ((128+RecursiveRowsNode.rowConstant roleCount)*volume prime v) := by
  have h := Shared50RecursiveNodeSemantics.exit_network hw hd x old hs st aux hav ho hp
  apply h.consequence _ _ (RecursiveRowsNode.exit_cost_linear (c := roleCount) v hp (by decide) hd old hs ho hh)
  · intro w hw
    simpa only [Shared50RecursiveNodeBinary.networkData_encoded,exit] using hw
  · intro w hw
    simpa only [Shared50RecursiveNodeSemantics.encoded_transpose,exit] using hw

end
end IntegerMultBounds.Machine.Shared50RecursiveNodeBoundary
