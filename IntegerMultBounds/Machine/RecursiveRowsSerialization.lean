import IntegerMultBounds.Machine.RecursiveRowsRoleBank
import IntegerMultBounds.Machine.RecursiveRoleSerialization
import IntegerMultBounds.Machine.RecursiveAffineViews

/-! Four-symbol recursive data specialization of the physical cyclic moves.
Parent and role-volume data use the exact serialization of the fixed mixed
blocks. Splitting changes array volume without an uncharged conversion, and
child spectator regrouping is a literal equality of serialized words. -/
namespace IntegerMultBounds.Machine.RecursiveRowsSerialization
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume role child)
open RecursiveRoleSerialization (encode roles)
variable {c t u : ℕ}
noncomputable section

abbrev Data (t : ℕ) (v : Descriptor) := Fin t → Fin (volume prime v) → Fin 4

def encodeArray {n : ℕ} (x : Fin n → Fin 4) : Fin n → Fin (prime+4) := fun i => encode (x i)

def roleArray {v : Descriptor} (hd : c ∣ v.rows) (x : Fin (volume prime v) → Fin 4) (j : Fin c) :
    Fin (volume prime (role v c)) → Fin 4 := RecursiveInterchangeRows.roleArray prime c v hd x j

theorem encode_role {v : Descriptor} (hd : c ∣ v.rows) (x : Fin (volume prime v) → Fin 4) (j : Fin c) :
    RecursiveInterchangeRows.roleArray prime c v hd (encodeArray x) j = encodeArray (roleArray hd x j) := rfl

theorem source_word {v : Descriptor} (x : Fin (volume prime v) → Fin 4) :
    RecursiveShiftRoleBank.source x = RecursiveRowsConstruct.word (encodeArray x) :=
  RecursiveRoleSerialization.source_eq_word x

private theorem blank_replicate (n : ℕ) (p : ℤ) :
    putWord (fun _ => blank (a := prime)) p (List.replicate n blank) = fun _ => blank := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,putWord]
    funext z
    by_cases hz : z = p
    · subst z; simp
    · simp only [Function.update_of_ne hz]
      exact congrFun (ih (p+1)) z

theorem source_blank (v : Descriptor) :
    RecursiveShiftRoleBank.source (v := v) (fun _ => blank) = fun _ => blank := by
  rw [source_word]
  have he : encodeArray (n := volume prime v) (fun _ => blank) = fun _ => blank := rfl
  rw [he]
  unfold RecursiveRowsConstruct.word
  rw [List.ofFn_const]
  exact blank_replicate _ _

/-- Fill only the selected permanent slots; every other slot is the canonical
blank array at this volume. This permits parent/child dependent types to differ. -/
def putData {v : Descriptor} (wires : Fin (1+c) → Fin t) (data : Data (1+c) v) : Data t v :=
  fun i => if h : ∃ j, wires j = i then data h.choose else fun _ => blank

theorem roles_putData {v : Descriptor} (wires : Fin (1+c) → Fin t) (data : Data (1+c) v) :
    roles (putData wires data) = RecursiveRowsRoleBank.updated wires (SharedBank.empty t prime) (roles data) := by
  apply congrArg₂ Tapes.mk
  · funext i
    simp only [roles,RecursiveRowsRoleBank.updated,SharedBank.empty]
    split_ifs <;> rfl
  · funext i
    simp only [roles,putData,RecursiveRowsRoleBank.updated,SharedBank.empty]
    split_ifs with h
    · rfl
    · exact source_blank v

theorem payload_putData {v : Descriptor} (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires)
    (data : Data (1+c) v) : SharedBank.payload (roles (putData wires data)) wires = roles data := by
  rw [roles_putData,RecursiveRowsRoleBank.updated_payload wires hw]

theorem updated_putData {v w : Descriptor} (wires : Fin (1+c) → Fin t)
    (before : Data (1+c) v) (after : Data (1+c) w) :
    RecursiveRowsRoleBank.updated wires (roles (putData wires before)) (roles after) = roles (putData wires after) := by
  rw [roles_putData,roles_putData]
  apply congrArg₂ Tapes.mk <;> funext i <;> simp only [RecursiveRowsRoleBank.updated] <;> split_ifs <;> rfl

def sourceLocal {v : Descriptor} (x : Fin (volume prime v) → Fin 4) : Data (1+c) v :=
  Fin.addCases (fun _ => x) (fun _ _ => blank)

def roleLocal {v : Descriptor} (rho : Equiv.Perm (Fin c)) (hd : c ∣ v.rows)
    (x : Fin (volume prime v) → Fin 4) : Data (1+c) (role v c) :=
  Fin.addCases (fun _ _ => blank) (fun j => roleArray hd x (rho.symm j))

def sourceData {v : Descriptor} (wires : Fin (1+c) → Fin t) (x : Fin (volume prime v) → Fin 4) :=
  putData wires (sourceLocal (c := c) x)
def roleData {v : Descriptor} (wires : Fin (1+c) → Fin t) (rho : Equiv.Perm (Fin c))
    (hd : c ∣ v.rows) (x : Fin (volume prime v) → Fin 4) := putData wires (roleLocal rho hd x)

theorem sourceLocal_tapes {v : Descriptor} (x : Fin (volume prime v) → Fin 4) :
    roles (sourceLocal (c := c) x) = RecursiveRowsConstruct.sourcePayload (c := c) (encodeArray x) := by
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases <;> simp [roles,RecursiveRowsConstruct.sourcePayload,CyclicRowCopy.payload,Tapes.append]
  · funext i
    induction i using Fin.addCases with
    | left i => simpa only [roles,sourceLocal,Fin.addCases_left,RecursiveRowsConstruct.sourcePayload,
        CyclicRowCopy.payload,Tapes.append] using source_word x
    | right i => simpa only [roles,sourceLocal,Fin.addCases_right,RecursiveRowsConstruct.sourcePayload,
        CyclicRowCopy.payload,Tapes.append] using source_blank v

theorem roleLocal_tapes {v : Descriptor} (rho : Equiv.Perm (Fin c)) (hd : c ∣ v.rows)
    (x : Fin (volume prime v) → Fin 4) :
    roles (roleLocal rho hd x) = RecursiveRowsConstruct.mergePayload rho hd (encodeArray x) (fun _ => blank) := by
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases <;> simp [roles,RecursiveRowsConstruct.mergePayload,CyclicRowCopy.payload,Tapes.append]
  · funext i
    induction i using Fin.addCases with
    | left i => simpa only [roles,roleLocal,Fin.addCases_left,RecursiveRowsConstruct.mergePayload,
        CyclicRowCopy.payload,Tapes.append] using source_blank (role v c)
    | right i => simpa only [roles,roleLocal,Fin.addCases_right,RecursiveRowsConstruct.mergePayload,
        CyclicRowCopy.payload,Tapes.append,encode_role] using source_word (roleArray hd x (rho.symm i))

theorem splitLocal_tapes {v : Descriptor} (hd : c ∣ v.rows) (x : Fin (volume prime v) → Fin 4) :
    roles (roleLocal (Equiv.refl _) hd x) = RecursiveRowsMove.rolePayload hd (encodeArray x) :=
  roleLocal_tapes (Equiv.refl _) hd x

/-- Actual split from parent-volume Data into role-volume Data on the same
permanent bank, including a physically blank common source and private work. -/
theorem split_hoare (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires)
    (hs : Fin 6 → List Bool) (aux : Tapes u prime) (v : Descriptor) (hc : 0 < c)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (x : Fin (volume prime v) → Fin 4) :
    HoareTime (RecursiveRowsRoleBank.splitProgram Shared50ModularControl.prime_prime.two_le (u := u) wires hw)
      (fun w => w = CleanSubbank.bank (s := RecursiveRowsRoleBank.LocalTapes c)
        (RecursiveShiftRoleBank.common (roles (sourceData wires x)) hs aux))
      (fun w => w = CleanSubbank.bank (s := RecursiveRowsRoleBank.LocalTapes c)
        (RecursiveShiftRoleBank.common (roles (roleData wires (Equiv.refl _) hd x)) hs aux))
      (RecursiveRowsClean.bound c (volume prime v)) := by
  have h := RecursiveRowsRoleBank.split_realizes Shared50ModularControl.prime_prime.two_le wires hw (roles (sourceData wires x)) hs aux v
    hc hv hp hd (encodeArray x) (by rw [sourceData,payload_putData wires hw,sourceLocal_tapes])
  rw [← splitLocal_tapes,sourceData,updated_putData] at h
  exact h

/-- The physical permutation is undone while merging; the result is the
literal parent array Data and every role tape is physically blank again. -/
theorem merge_hoare (rho : Equiv.Perm (Fin c)) (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires)
    (hs : Fin 6 → List Bool) (aux : Tapes u prime) (v : Descriptor) (hc : 0 < c)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (x : Fin (volume prime v) → Fin 4) :
    HoareTime (RecursiveRowsRoleBank.mergeProgram Shared50ModularControl.prime_prime.two_le (u := u) rho wires hw)
      (fun w => w = CleanSubbank.bank (s := RecursiveRowsRoleBank.LocalTapes c)
        (RecursiveShiftRoleBank.common (roles (roleData wires rho hd x)) hs aux))
      (fun w => w = CleanSubbank.bank (s := RecursiveRowsRoleBank.LocalTapes c)
        (RecursiveShiftRoleBank.common (roles (sourceData wires x)) hs aux))
      (RecursiveRowsClean.bound c (volume prime v)) := by
  have h := RecursiveRowsRoleBank.merge_realizes Shared50ModularControl.prime_prime.two_le rho wires hw (roles (roleData wires rho hd x)) hs aux v
    hc hv hp hd (encodeArray x) (by rw [roleData,payload_putData wires hw,roleLocal_tapes])
  rw [← sourceLocal_tapes,roleData,updated_putData] at h
  exact h

/-- The selected child spectator layout has the same literal role word. Only
its dependent array indexing changes; header replacement remains charged by
its own physical constructor. -/
def childData {m : ℕ} (b : ℕ) (v : Descriptor) (hw : v.width=m*b) (i j : Fin m)
    (data : Data t (role v c)) : Data t (child prime c b v i j) :=
  fun wire => RecursiveAffineViews.array prime (RecursiveInterchangeLayout.child_volume prime c b v i j hw) (data wire)

theorem childData_roles {m : ℕ} (b : ℕ) (v : Descriptor) (hw : v.width=m*b) (i j : Fin m)
    (data : Data t (role v c)) : roles (childData b v hw i j data) = roles data := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext wire
    change FlatRepeatedControlNormalize.encoded (putWord (fun _ => blank) 0
      (List.ofFn (RecursiveAffineViews.array prime (RecursiveInterchangeLayout.child_volume prime c b v i j hw) (data wire)))) =
      FlatRepeatedControlNormalize.encoded (putWord (fun _ => blank) 0 (List.ofFn (data wire)))
    rw [RecursiveAffineViews.array_word]

theorem childData_entry {m : ℕ} (b : ℕ) (v : Descriptor) (hw : v.width=m*b) (i j : Fin m)
    (data : Data t (role v c)) (wire : Fin t) (z : Fin (volume prime (child prime c b v i j))) :
    childData b v hw i j data wire z = data wire (Fin.cast (RecursiveInterchangeLayout.child_volume prime c b v i j hw) z) := rfl


theorem putData_selected {v : Descriptor} (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires)
    (data : Data (1+c) v) (j : Fin (1+c)) : putData wires data (wires j) = data j := by
  unfold putData
  split_ifs with h
  · rw [hw h.choose_spec]
  · exact (h ⟨j,rfl⟩).elim

theorem putData_unselected {v : Descriptor} (wires : Fin (1+c) → Fin t) (data : Data (1+c) v)
    (i : Fin t) (hi : ¬∃ j, wires j = i) : putData wires data i = fun _ => blank := by
  simp [putData,hi]

theorem roleData_entry {v : Descriptor} (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires)
    (rho : Equiv.Perm (Fin c)) (hd : c ∣ v.rows) (x : Fin (volume prime v) → Fin 4)
    (j : Fin c) (z : Fin (volume prime (role v c))) :
    roleData wires rho hd x (wires (Fin.natAdd 1 j)) z = roleArray hd x (rho.symm j) z := by
  simp only [roleData,putData_selected wires hw,roleLocal,Fin.addCases_right]

theorem roleData_common_blank {v : Descriptor} (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires)
    (rho : Equiv.Perm (Fin c)) (hd : c ∣ v.rows) (x : Fin (volume prime v) → Fin 4) :
    roleData wires rho hd x (wires (Fin.castAdd c (0 : Fin 1))) = fun _ => blank := by
  simp only [roleData,putData_selected wires hw,roleLocal,Fin.addCases_left]

theorem cyclic_entry {v : Descriptor} (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires)
    (rho : Equiv.Perm (Fin c)) (hd : c ∣ v.rows) (x : Fin (volume prime v) → Fin 4)
    (g : Fin (RecursiveInterchangeRows.groups c v)) (j : Fin c)
    (k : Fin (RecursiveInterchangeRows.rowLength prime v)) :
    roleData wires rho hd x (wires (Fin.natAdd 1 j)) (RecursiveInterchangeRows.roleIndex prime c v g k) =
      x (Fin.cast (RecursiveInterchangeRows.volume_split prime c v hd).symm
        (RecursiveInterchangeRows.pack g (RecursiveInterchangeRows.pack (rho.symm j) k))) := by
  rw [roleData_entry wires hw]
  exact RecursiveInterchangeRows.role_entry prime c v hd x g (rho.symm j) k

theorem childRole_entry {m : ℕ} (b : ℕ) (v : Descriptor) (hwidth : v.width=m*b) (i j : Fin m)
    (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires) (rho : Equiv.Perm (Fin c))
    (hd : c ∣ v.rows) (x : Fin (volume prime v) → Fin 4) (wire : Fin c)
    (z : Fin (volume prime (child prime c b v i j))) :
    childData b v hwidth i j (roleData wires rho hd x) (wires (Fin.natAdd 1 wire)) z =
      roleArray hd x (rho.symm wire) (Fin.cast (RecursiveInterchangeLayout.child_volume prime c b v i j hwidth) z) := by
  rw [childData_entry,roleData_entry wires hw]

/-- Exact child-volume output type, on literally the same physical words.
This theorem retains the parent headers; the child-header setup is a separate
charged program and is not replaced by this dependent array cast. -/
theorem split_child_hoare {m : ℕ} (b : ℕ) (v : Descriptor) (hwidth : v.width=m*b) (i j : Fin m)
    (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires)
    (hs : Fin 6 → List Bool) (aux : Tapes u prime) (hc : 0 < c)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (x : Fin (volume prime v) → Fin 4) :
    HoareTime (RecursiveRowsRoleBank.splitProgram Shared50ModularControl.prime_prime.two_le (u := u) wires hw)
      (fun w => w = CleanSubbank.bank (s := RecursiveRowsRoleBank.LocalTapes c)
        (RecursiveShiftRoleBank.common (roles (sourceData wires x)) hs aux))
      (fun w => w = CleanSubbank.bank (s := RecursiveRowsRoleBank.LocalTapes c)
        (RecursiveShiftRoleBank.common (roles (childData b v hwidth i j (roleData wires (Equiv.refl _) hd x))) hs aux))
      (RecursiveRowsClean.bound c (volume prime v)) := by
  rw [childData_roles]
  exact split_hoare wires hw hs aux v hc hv hp hd x

theorem merge_child_hoare {m : ℕ} (b : ℕ) (v : Descriptor) (hwidth : v.width=m*b) (i j : Fin m)
    (rho : Equiv.Perm (Fin c)) (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires)
    (hs : Fin 6 → List Bool) (aux : Tapes u prime) (hc : 0 < c)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (x : Fin (volume prime v) → Fin 4) :
    HoareTime (RecursiveRowsRoleBank.mergeProgram Shared50ModularControl.prime_prime.two_le (u := u) rho wires hw)
      (fun w => w = CleanSubbank.bank (s := RecursiveRowsRoleBank.LocalTapes c)
        (RecursiveShiftRoleBank.common (roles (childData b v hwidth i j (roleData wires rho hd x))) hs aux))
      (fun w => w = CleanSubbank.bank (s := RecursiveRowsRoleBank.LocalTapes c)
        (RecursiveShiftRoleBank.common (roles (sourceData wires x)) hs aux))
      (RecursiveRowsClean.bound c (volume prime v)) := by
  rw [childData_roles]
  exact merge_hoare rho wires hw hs aux v hc hv hp hd x

end
end IntegerMultBounds.Machine.RecursiveRowsSerialization
