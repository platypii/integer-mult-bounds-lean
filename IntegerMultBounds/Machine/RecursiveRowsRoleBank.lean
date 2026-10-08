import IntegerMultBounds.Machine.RecursiveRowsClean
import IntegerMultBounds.Machine.CleanSubbank

/-! Physical placement of clean cyclic moves onto permanent source/role tapes
and the six shared headers. Every other permanent tape and the common scratch
are framed, and all private tape space is blank again on return. -/
namespace IntegerMultBounds.Machine.RecursiveRowsRoleBank
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRowsMove (TapeCount)
variable {q c t u : ℕ} (hq : 2 ≤ q)
noncomputable section

abbrev LocalTapes (c : ℕ) := TapeCount c+TapeCount c
abbrev Ports (c : ℕ) := (1+c)+6

def ports : Fin (Ports c) → Fin (LocalTapes c) :=
  Fin.addCases RecursiveRowsClean.payloadSlot RecursiveRowsClean.headerSlot

theorem ports_injective : Function.Injective (ports (c := c)) := by
  intro i j h
  have hv := congrArg Fin.val h
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [ports,Fin.addCases_left,RecursiveRowsClean.payloadSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
      exact congrArg (Fin.castAdd 6) (Fin.ext (by omega))
    | right j =>
      simp only [ports,Fin.addCases_left,Fin.addCases_right,RecursiveRowsClean.payloadSlot,
        RecursiveRowsClean.headerSlot,RecursiveRowsDimensions.headerSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [ports,Fin.addCases_left,Fin.addCases_right,RecursiveRowsClean.payloadSlot,
        RecursiveRowsClean.headerSlot,RecursiveRowsDimensions.headerSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    | right j =>
      simp only [ports,Fin.addCases_right,RecursiveRowsClean.headerSlot,RecursiveRowsDimensions.headerSlot,
        Fin.val_castAdd] at hv
      exact congrArg (Fin.natAdd (1+c)) (Fin.ext (by omega))

def headers (hs : Fin 6 → List Bool) : Tapes 6 q :=
  ⟨fun _ => 1,fun j => RadixZeroFill.encodedBinary (hs j)⟩

theorem local_payload (hs : Fin 6 → List Bool) (payload : Tapes (1+c) q) :
    SharedBank.payload (RecursiveRowsClean.bank hs payload) ports = payload.append (headers hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i =>
    simp only [SharedBank.payload,ports,Tapes.append,Fin.addCases_left]
    first
    | exact (RecursiveRowsClean.payload hs payload i).1
    | exact (RecursiveRowsClean.payload hs payload i).2
  | right i =>
    simp only [SharedBank.payload,ports,Tapes.append,Fin.addCases_right,headers]
    first
    | exact (RecursiveRowsClean.headers hs payload i).1
    | exact (RecursiveRowsClean.headers hs payload i).2

private theorem selected_kept (i : Fin (TapeCount c)) (hi : RecursiveRowsClean.keep i = true) :
    ∃ j, ports j = Fin.castAdd (TapeCount c) i := by
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      have hr : 3 ≤ i.val ∧ i.val < 9 := by simpa [RecursiveRowsClean.keep,RecursiveRowsClean.dimRight] using hi
      refine ⟨Fin.natAdd (1+c) ⟨i.val-3,by omega⟩,?_⟩
      apply Fin.ext
      simp only [ports,Fin.addCases_right,RecursiveRowsClean.headerSlot,RecursiveRowsDimensions.headerSlot,Fin.val_castAdd]
      omega
    | right i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i => exact ⟨Fin.castAdd 6 i,by simp [ports,RecursiveRowsClean.payloadSlot]⟩
        | right i => simp [RecursiveRowsClean.keep,RecursiveRowsClean.localKeep] at hi
      | right i => simp [RecursiveRowsClean.keep,RecursiveRowsClean.localKeep] at hi
  | right i => simp [RecursiveRowsClean.keep] at hi

theorem local_clean (hs : Fin 6 → List Bool) (payload : Tapes (1+c) q) :
    SharedBank.strip (RecursiveRowsClean.bank hs payload) ports = SharedBank.empty (LocalTapes c) q := by
  have hblank (i : Fin (LocalTapes c)) (hi : ¬∃ j, ports j = i) :
      (RecursiveRowsClean.bank hs payload).head i = 0 ∧
      (RecursiveRowsClean.bank hs payload).tape i = fun _ => blank := by
    induction i using Fin.addCases with
    | left i =>
      exact RecursiveRowsClean.private_blank hs payload i
        (Bool.eq_false_iff.mpr (fun hk => hi (selected_kept i hk)))
    | right i => exact RecursiveRowsClean.trackers_blank hs payload i
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j, ports j = i
    · simp [SharedBank.strip,hi,SharedBank.empty]
    · simpa only [SharedBank.strip,hi,ite_false,SharedBank.empty] using (hblank i hi).1
  · funext i
    by_cases hi : ∃ j, ports j = i
    · simp [SharedBank.strip,hi,SharedBank.empty]
    · simpa only [SharedBank.strip,hi,ite_false,SharedBank.empty] using (hblank i hi).2

/-- The permanent bank convention shared by recursive shift/affine routines:
role tapes, then one common scratch tape, six headers, and an arbitrary frame. -/
def common (roles : Tapes t q) (hs : Fin 6 → List Bool) (aux : Tapes u q) : Tapes (t+(7+u)) q :=
  roles.append (((SharedBank.empty 1 q).append (headers hs)).append aux)

def commonPorts (wires : Fin (1+c) → Fin t) : Fin (Ports c) → Fin (t+(7+u)) :=
  Fin.addCases (fun i => Fin.castAdd (7+u) (wires i))
    (fun j => Fin.natAdd t (Fin.castAdd u (Fin.natAdd 1 j)))

theorem commonPorts_injective (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires) :
    Function.Injective (commonPorts (u := u) wires) := by
  intro i j h
  have hv := congrArg Fin.val h
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      apply congrArg (Fin.castAdd 6)
      apply hw
      apply Fin.ext
      simpa only [commonPorts,Fin.addCases_left,Fin.val_castAdd] using hv
    | right j =>
      simp only [commonPorts,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
      have := (wires i).isLt
      omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [commonPorts,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
      have := (wires j).isLt
      omega
    | right j =>
      simp only [commonPorts,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
      exact congrArg (Fin.natAdd (1+c)) (Fin.ext (by omega))

theorem common_payload (wires : Fin (1+c) → Fin t) (roles : Tapes t q) (hs : Fin 6 → List Bool) (aux : Tapes u q) :
    SharedBank.payload (common roles hs aux) (commonPorts wires) =
      (SharedBank.payload roles wires).append (headers hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
    simp [SharedBank.payload,common,commonPorts,Tapes.append,headers]

def splitProgram (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires) :=
  Placement.placed (RecursiveRowsClean.splitProgram hq (c := c))
    (CleanSubbank.placement ports (commonPorts (u := u) wires) (commonPorts_injective wires hw))
def mergeProgram (rho : Equiv.Perm (Fin c)) (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires) :=
  Placement.placed (RecursiveRowsClean.mergeProgram hq rho)
    (CleanSubbank.placement ports (commonPorts (u := u) wires) (commonPorts_injective wires hw))

/-- Actual split on the permanent bank. The frame equality permits arbitrary
untouched roles and auxiliary data; it is not a supplied time certificate. -/
theorem split_hoare (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires)
    (before after : Tapes t q) (hs : Fin 6 → List Bool) (aux : Tapes u q) (v : Descriptor)
    (hc : 0 < c) (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (x : Fin (volume q v) → Fin (q+4))
    (hin : SharedBank.payload before wires = RecursiveRowsConstruct.sourcePayload (c := c) x)
    (hout : SharedBank.payload after wires = RecursiveRowsMove.rolePayload hd x)
    (hf : SharedBank.strip (common before hs aux) (commonPorts wires) =
      SharedBank.strip (common after hs aux) (commonPorts wires)) :
    HoareTime (splitProgram hq (u := u) wires hw)
      (fun w => w = CleanSubbank.bank (s := LocalTapes c) (common before hs aux))
      (fun w => w = CleanSubbank.bank (s := LocalTapes c) (common after hs aux))
      (RecursiveRowsClean.bound c (volume q v)) := by
  apply CleanSubbank.realizes _ ports (commonPorts wires) ports_injective (commonPorts_injective wires hw)
    _ _ (RecursiveRowsClean.bank hs (RecursiveRowsConstruct.sourcePayload (c := c) x))
    (RecursiveRowsClean.bank hs (RecursiveRowsMove.rolePayload hd x)) _
  · rw [local_payload,common_payload,hin]
  · rw [local_payload,common_payload,hout]
  · exact local_clean hs _
  · exact local_clean hs _
  · exact hf
  · exact RecursiveRowsClean.split_hoare hq hc hs v hv hp hd x

theorem merge_hoare (rho : Equiv.Perm (Fin c)) (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires)
    (before after : Tapes t q) (hs : Fin 6 → List Bool) (aux : Tapes u q) (v : Descriptor)
    (hc : 0 < c) (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (x : Fin (volume q v) → Fin (q+4))
    (hin : SharedBank.payload before wires = RecursiveRowsConstruct.mergePayload rho hd x (fun _ => blank))
    (hout : SharedBank.payload after wires = RecursiveRowsConstruct.sourcePayload (c := c) x)
    (hf : SharedBank.strip (common before hs aux) (commonPorts wires) =
      SharedBank.strip (common after hs aux) (commonPorts wires)) :
    HoareTime (mergeProgram hq (u := u) rho wires hw)
      (fun w => w = CleanSubbank.bank (s := LocalTapes c) (common before hs aux))
      (fun w => w = CleanSubbank.bank (s := LocalTapes c) (common after hs aux))
      (RecursiveRowsClean.bound c (volume q v)) := by
  apply CleanSubbank.realizes _ ports (commonPorts wires) ports_injective (commonPorts_injective wires hw)
    _ _ (RecursiveRowsClean.bank hs (RecursiveRowsConstruct.mergePayload rho hd x (fun _ => blank)))
    (RecursiveRowsClean.bank hs (RecursiveRowsConstruct.sourcePayload (c := c) x)) _
  · rw [local_payload,common_payload,hin]
  · rw [local_payload,common_payload,hout]
  · exact local_clean hs _
  · exact local_clean hs _
  · exact hf
  · exact RecursiveRowsClean.merge_hoare hq rho hc hs v hv hp hd x


def updated (wires : Fin (1+c) → Fin t) (roles : Tapes t q) (payload : Tapes (1+c) q) : Tapes t q where
  head i := if h : ∃ j, wires j = i then payload.head h.choose else roles.head i
  tape i := if h : ∃ j, wires j = i then payload.tape h.choose else roles.tape i

theorem updated_payload (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires)
    (roles : Tapes t q) (payload : Tapes (1+c) q) :
    SharedBank.payload (updated wires roles payload) wires = payload := by
  apply congrArg₂ Tapes.mk <;> funext j <;> simp only [SharedBank.payload,updated]
  all_goals split_ifs with h
  all_goals first | (rw [hw h.choose_spec]) | exact (h ⟨j,rfl⟩).elim

theorem common_frame (wires : Fin (1+c) → Fin t) (roles : Tapes t q) (payload : Tapes (1+c) q)
    (hs : Fin 6 → List Bool) (aux : Tapes u q) :
    SharedBank.strip (common roles hs aux) (commonPorts wires) =
      SharedBank.strip (common (updated wires roles payload) hs aux) (commonPorts wires) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i =>
    by_cases hi : ∃ j, wires j = i
    · obtain ⟨j,hj⟩ := hi
      have hsel : ∃ z, commonPorts (u := u) wires z = Fin.castAdd (7+u) i :=
        ⟨Fin.castAdd 6 j,by simp only [commonPorts,Fin.addCases_left,hj]⟩
      simp only [SharedBank.strip,hsel,ite_true]
    · simp only [SharedBank.strip,common,Tapes.append,Fin.addCases_left,updated,hi,↓reduceDIte]
  | right i => simp only [SharedBank.strip,common,Tapes.append,Fin.addCases_right]

/-- Deterministic whole-bank result: only the selected source and roles change.
No output-bank or frame certificate needs to be supplied by the caller. -/
theorem split_realizes (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires)
    (roles : Tapes t q) (hs : Fin 6 → List Bool) (aux : Tapes u q) (v : Descriptor)
    (hc : 0 < c) (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (x : Fin (volume q v) → Fin (q+4))
    (hin : SharedBank.payload roles wires = RecursiveRowsConstruct.sourcePayload (c := c) x) :
    HoareTime (splitProgram hq (u := u) wires hw)
      (fun w => w = CleanSubbank.bank (s := LocalTapes c) (common roles hs aux))
      (fun w => w = CleanSubbank.bank (s := LocalTapes c)
        (common (updated wires roles (RecursiveRowsMove.rolePayload hd x)) hs aux))
      (RecursiveRowsClean.bound c (volume q v)) :=
  split_hoare hq wires hw roles _ hs aux v hc hv hp hd x hin
    (updated_payload wires hw roles _) (common_frame wires roles _ hs aux)

theorem merge_realizes (rho : Equiv.Perm (Fin c)) (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires)
    (roles : Tapes t q) (hs : Fin 6 → List Bool) (aux : Tapes u q) (v : Descriptor)
    (hc : 0 < c) (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (x : Fin (volume q v) → Fin (q+4))
    (hin : SharedBank.payload roles wires = RecursiveRowsConstruct.mergePayload rho hd x (fun _ => blank)) :
    HoareTime (mergeProgram hq (u := u) rho wires hw)
      (fun w => w = CleanSubbank.bank (s := LocalTapes c) (common roles hs aux))
      (fun w => w = CleanSubbank.bank (s := LocalTapes c)
        (common (updated wires roles (RecursiveRowsConstruct.sourcePayload (c := c) x)) hs aux))
      (RecursiveRowsClean.bound c (volume q v)) :=
  merge_hoare hq rho wires hw roles _ hs aux v hc hv hp hd x hin
    (updated_payload wires hw roles _) (common_frame wires roles _ hs aux)

end
end IntegerMultBounds.Machine.RecursiveRowsRoleBank
