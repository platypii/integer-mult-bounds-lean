import IntegerMultBounds.Machine.Shared50RecursiveNodeTranspose
import IntegerMultBounds.Machine.Shared50NodeGates

/-! Binary node fiber state uses the same encoding and World enumeration as the
actual segment/gate compiler; the additional input/output role is blank. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveNodeBinary
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50TapeGlobal (roleCount roleEquiv)
open Shared50GlobalBudget (World)
open RecursiveInterchangeLayout (Descriptor volume role)
open Shared50RecursiveNodeLayout (wires wires_injective)
open Shared50RecursiveNodeSemantics
variable {v : Descriptor}

def splitWorld (hd : roleCount ∣ v.rows) (x : Fin (volume prime v) → ZMod 2) :
    World → Fin (volume prime (role v roleCount)) → ZMod 2 :=
  fun i => splitBits hd x (roleEquiv.symm i)

theorem splitData_encoded (hd : roleCount ∣ v.rows) (x : Fin (volume prime v) → ZMod 2) :
    RecursiveRowsSerialization.roleData wires (Equiv.refl _) hd (encoded x) =
      Shared50NodeGates.encoded (splitWorld hd x) (fun _ => blank) := by
  funext i z
  induction i using Fin.addCases with
  | left i =>
    rw [← Shared50RecursiveNodeLayout.wires_role,RecursiveRowsSerialization.roleData_entry wires wires_injective]
    simp only [Equiv.refl_symm,Equiv.refl_apply]
    rw [← encode_split]
    simp only [Shared50NodeGates.encoded,Shared50NodeGates.extend,Shared50RecursiveNodeLayout.wires_role,
      Fin.addCases_left,Shared50RecursiveGates.encoded,splitWorld,Equiv.symm_apply_apply]
  | right i =>
    fin_cases i
    change RecursiveRowsSerialization.roleData wires (Equiv.refl _) hd (encoded x)
      (wires (Fin.castAdd roleCount (0 : Fin 1))) z = blank
    exact congrFun (RecursiveRowsSerialization.roleData_common_blank wires wires_injective _ hd _) z

def networkWorld {b : ℕ} (hw : v.width=125000*b) (hd : roleCount ∣ v.rows)
    (x : Fin (volume prime v) → ZMod 2) : World → Fin (volume prime (role v roleCount)) → ZMod 2 :=
  fun i => networkBits hw hd x (roleEquiv.symm i)

theorem networkData_encoded {b : ℕ} (hw : v.width=125000*b) (hd : roleCount ∣ v.rows)
    (x : Fin (volume prime v) → ZMod 2) :
    networkData hw hd x = Shared50NodeGates.encoded (networkWorld hw hd x) (fun _ => blank) := by
  funext i z
  induction i using Fin.addCases with
  | left i =>
    unfold networkData
    rw [← Shared50RecursiveNodeLayout.wires_role,RecursiveRowsSerialization.putData_selected wires wires_injective]
    simp only [Fin.addCases_right,Shared50NodeGates.encoded,Shared50NodeGates.extend,
      Shared50RecursiveNodeLayout.wires_role,Fin.addCases_left,Shared50RecursiveGates.encoded,
      networkWorld,Equiv.symm_apply_apply]
  | right i =>
    fin_cases i
    change RecursiveRowsSerialization.putData wires _ (wires (Fin.castAdd roleCount (0 : Fin 1))) z = blank
    rw [RecursiveRowsSerialization.putData_selected wires wires_injective]
    rfl

theorem roleSwap_scalar {b : ℕ} (hw : v.width=125000*b)
    (a : RecursiveScalarCoordinates.Address 125000 b (role v roleCount)) :
    Shared50RecursiveNodeRows.roleSwap (RecursiveScalarCoordinates.index (v := role v roleCount) hw a) =
      RecursiveScalarCoordinates.index (v := role v roleCount) hw {a with h := a.d,d := a.h} := by
  rw [scalar_index,scalar_index]
  simp only [Shared50RecursiveNodeRows.roleSwap,RecursiveInterchangeRows.roleIndex,Fin.cast_cast,
    Fin.cast_eq_self,RecursiveInterchangeRows.pack,Equiv.symm_apply_apply]
  exact congrArg (fun k => RecursiveInterchangeRows.roleIndex prime roleCount v
    (RecursiveInterchangeRows.pack a.beforeRows a.row) k)
    (Shared50RecursiveNodeRows.swapSuffix_pack (v := v) a.before (rank hw a.h) a.middle (rank hw a.d) a.after)

theorem networkWorld_scalar {b : ℕ} (hw : v.width=125000*b) (hd : roleCount ∣ v.rows)
    (x : Fin (volume prime v) → ZMod 2) (i : World)
    (a : RecursiveScalarCoordinates.Address 125000 b (role v roleCount)) :
    networkWorld hw hd x i (RecursiveScalarCoordinates.index (v := role v roleCount) hw a) =
      splitWorld hd x (Shared50ShearEndpoints.route i)
        (RecursiveScalarCoordinates.index (v := role v roleCount) hw {a with h := a.d,d := a.h}) := by
  unfold networkWorld
  rw [networkBits_exact,roleSwap_scalar]
  simp only [Shared50RecursiveNodeLayout.mergeRoute_symm,Equiv.apply_symm_apply,splitWorld]

end
end IntegerMultBounds.Machine.Shared50RecursiveNodeBinary
