module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Leaf
public import IntegerMultBounds.Machine.HoareWithinFrame

/-! Payload contents and immutable header values do not move boundary heads.
These equalities are structural before concrete tape counts are instantiated. -/
@[expose] public section
namespace IntegerMultBounds.Machine.SharedBankStageInput
variable {t a : ℕ} {v w : Tapes t a}

theorem raw_head_congr (h : v.head = w.head) (n : ℕ) : (raw v n).head = (raw w n).head := by
  funext j
  change (if hj : j.val < t then v.head ⟨j.val,hj⟩ else 0) =
    (if hj : j.val < t then w.head ⟨j.val,hj⟩ else 0)
  split_ifs with hj
  · exact congrFun h ⟨j.val,hj⟩
  · rfl

end IntegerMultBounds.Machine.SharedBankStageInput

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.CommonBank
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
noncomputable section
variable {t : ℕ}

theorem bank_head_congr (roles roles' : Tapes t prime) (hs hs' : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (c : Fin K → Option ℕ) (st : Tapes 2 prime) (hr : roles.head = roles'.head) :
    (bank roles hs f p node scalar c st).head = (bank roles' hs' f p node scalar c st).head := by
  unfold bank Shared50RecursiveBank.bank RecursiveCallBank.bank RecursiveShiftRoleBank.common
  exact Tapes.append_head_congr _ _ _ _ hr
    (Tapes.append_head_congr _ _ _ _ (Tapes.append_head_congr _ _ _ _ rfl rfl) rfl)

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.CommonBank

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Leaf
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor)
open RevMachine
noncomputable section

theorem leafBank_head_eq (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (c : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime)
    (u v : Descriptor) (X Y : ℕ → ZMod 2) :
    (leafBank f p node scalar c st u X).head = (leafBank f p node scalar c st v Y).head := by
  apply CommonBank.bank_head_congr
  funext j
  simp [FamilyStep.rolesAt,FamilyRoot.rolesOf,NodePark.childRoles,SharedPlacementAlphabet.setTape,SharedBank.empty]

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Leaf
