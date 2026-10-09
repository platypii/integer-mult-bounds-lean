import IntegerMultBounds.Machine.RecursiveCallProtocol
import IntegerMultBounds.Machine.Shared50RecursiveCallLayout

/-! Exact payload semantics of the actual fixed recursive-call parking list.
All original World roles except the active one are parked; the final I/O role
is the sole child payload. Updating that child payload is literally entry of
the transformed parent bank, the endpoint required by physical recovery. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveCallSemantics
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50TapeGlobal (roleCount roleEquiv)
open Shared50GlobalBudget (World)
open Shared50NodeSegments (payloadCount io)
open Shared50NodePieceTransport (worldSlot)
open SharedPlacementAlphabet (setTape)
open RecursiveCallBank
open Shared50RecursiveCallLayout
variable {u : ℕ}
attribute [local irreducible] Shared50RecursiveCallLayout.parked Shared50FixedControl.control
  Shared50GlobalCircuit.program50 Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code


/-- Parking never observes or changes an excluded tape: a source replacement
commutes through the entire physical parking endpoint. -/
theorem saved_setTape {t a : ℕ} (L : RoleArrayFrames.Layout t) (ops : List (RoleArrayFrames.Role L))
    (src : RoleArrayFrames.Role L) (hn : src ∉ ops) (n : ℕ) (v : Tapes t a)
    (out : ℤ → Fin (a+4)) (p : ℤ) :
    RoleArrayFrames.saved L ops n (setTape v src.val out p) =
      setTape (RoleArrayFrames.saved L ops n v) src.val out p := by
  induction ops generalizing v with
  | nil => rfl
  | cons i ops ih =>
    have hne : i.val ≠ src.val := fun he => ((by simpa only [List.mem_cons,not_or] using hn : src ≠ i ∧ src ∉ ops)).1 (Subtype.ext he.symm)
    have hone : RoleArrayFrames.saveOne L i n (setTape v src.val out p) =
        setTape (RoleArrayFrames.saveOne L i n v) src.val out p := by
      apply congrArg₂ Tapes.mk <;> funext k <;> by_cases hs : k = src.val <;>
        by_cases hi : k = i.val <;> by_cases hk : k = L.stack <;>
        simp_all [RoleArrayFrames.saveOne,RoleArrayStackAt.pushed,RoleArrayFrames.slots,setTape,
          src.property.1,src.property.1.symm,i.property.1]
    rw [RoleArrayFrames.saved,hone,ih ((by simpa only [List.mem_cons,not_or] using hn : src ≠ i ∧ src ∉ ops)).2,RoleArrayFrames.saved]

/-- Moving the active array into the child I/O transfers precisely a source
replacement, while the physical source slot becomes blank. -/
theorem entered_setTape {t a : ℕ} (L : RoleArrayFrames.Layout t) (ops : List (RoleArrayFrames.Role L))
    (src dst : RoleArrayFrames.Role L) (hne : src ≠ dst) (hn : src ∉ ops)
    (n : ℕ) (v : Tapes t a) (out : ℤ → Fin (a+4)) :
    RoleArrayCall.entered L ops src dst n (setTape v src.val out 0) =
      setTape (RoleArrayCall.entered L ops src dst n v) dst.val out 0 := by
  rw [RoleArrayCall.entered,saved_setTape L ops src hn]
  have hv : src.val ≠ dst.val := fun he => hne (Subtype.ext he)
  apply congrArg₂ Tapes.mk <;> funext k <;> by_cases hs : k = src.val <;> by_cases hd : k = dst.val <;>
    simp_all [RoleArrayCall.entered,RoleArrayMove.moved,RoleArrayCall.slots,setTape]

/-- A blank stack suffix stays blank above the new payload stack head. No
bound on future recursive depth, initialized space or reset is supplied. -/
theorem saved_blank_suffix {t a : ℕ} (L : RoleArrayFrames.Layout t) (ops : List (RoleArrayFrames.Role L))
    (n : ℕ) (v : Tapes t a) (hf : ∀ z, v.head L.stack ≤ z → v.tape L.stack z = blank) :
    ∀ z, (RoleArrayFrames.saved L ops n v).head L.stack ≤ z →
      (RoleArrayFrames.saved L ops n v).tape L.stack z = blank := by
  intro z hz
  rw [RoleArrayFrames.saved_head] at hz
  rw [RoleArrayFrames.saved_outside L ops n v z (Or.inr hz)]
  apply hf z
  have hn : (0 : ℤ) ≤ (ops.length*n : ℕ) := by positivity
  omega

theorem entered_blank_suffix {t a : ℕ} (L : RoleArrayFrames.Layout t) (ops : List (RoleArrayFrames.Role L))
    (src dst : RoleArrayFrames.Role L) (n : ℕ) (v : Tapes t a)
    (hf : ∀ z, v.head L.stack ≤ z → v.tape L.stack z = blank) :
    ∀ z, (RoleArrayCall.entered L ops src dst n v).head L.stack ≤ z →
      (RoleArrayCall.entered L ops src dst n v).tape L.stack z = blank := by
  simpa [RoleArrayCall.entered,RoleArrayMove.moved,RoleArrayCall.slots,setTape,
    src.property.1.symm,dst.property.1.symm] using saved_blank_suffix L ops n v hf

/-- The entry state required for recovery of an updated parent is exactly the
old entry state with only the child I/O payload replaced. -/
theorem entered_updated (w : World) (n : ℕ) (v : Tapes (TapeCount payloadCount u) prime)
    (out : ℤ → Fin (prime+4)) :
    RecursiveCallProtocol.entered (parked w) (worldSlot w) io n
      (setTape v (role (u := u) (worldSlot w)).val out 0) =
      setTape (RecursiveCallProtocol.entered (parked w) (worldSlot w) io n v)
        (role (u := u) io).val out 0 := by
  apply entered_setTape
  · exact role_injective.ne (active_ne_io w)
  · intro h
    obtain ⟨k,hk,he⟩ := List.mem_map.mp h
    exact active_not_parked w (role_injective he ▸ hk)


private theorem moved_source {t a : ℕ} (L : RoleArrayFrames.Layout t)
    (src dst : RoleArrayFrames.Role L) (hne : src.val ≠ dst.val) (v : Tapes t a) :
    let out := RoleArrayMove.moved (RoleArrayCall.slots L src dst) v
    out.head src.val = 0 ∧ out.tape src.val = fun _ => blank := by
  simp only [RoleArrayMove.moved,RoleArrayCall.slots,Matrix.cons_val_zero,Matrix.cons_val_one,
    setTape,Function.update_of_ne hne,Function.update_self]
  trivial

private theorem moved_destination {t a : ℕ} (L : RoleArrayFrames.Layout t)
    (src dst : RoleArrayFrames.Role L) (v : Tapes t a) :
    let out := RoleArrayMove.moved (RoleArrayCall.slots L src dst) v
    out.head dst.val = 0 ∧ out.tape dst.val = v.tape src.val := by
  simp only [RoleArrayMove.moved,RoleArrayCall.slots,Matrix.cons_val_zero,Matrix.cons_val_one,
    setTape,Function.update_self]
  trivial

private theorem moved_other {t a : ℕ} (L : RoleArrayFrames.Layout t)
    (src dst : RoleArrayFrames.Role L) (v : Tapes t a) (k : Fin t)
    (hs : k ≠ src.val) (hd : k ≠ dst.val) :
    let out := RoleArrayMove.moved (RoleArrayCall.slots L src dst) v
    out.head k = v.head k ∧ out.tape k = v.tape k := by
  simp only [RoleArrayMove.moved,RoleArrayCall.slots,Matrix.cons_val_zero,Matrix.cons_val_one,
    setTape,Function.update_of_ne hs,Function.update_of_ne hd]
  trivial

/-- Every original World slot is physically blank after parking and moving
its selected active array into the separate child I/O slot. -/
theorem entered_world_blank (w k : World) (n : ℕ)
    (v : Tapes (TapeCount payloadCount u) prime) :
    let mid := RecursiveCallProtocol.entered (parked w) (worldSlot w) io n v
    mid.head (role (worldSlot k)).val = 0 ∧ mid.tape (role (worldSlot k)).val = fun _ => blank := by
  have hio : (role (u := u) (worldSlot k)).val ≠ (role io).val := by
    intro he
    exact active_ne_io k (role_injective (Subtype.ext he))
  by_cases hk : k = w
  · subst k
    exact moved_source layout (role (worldSlot w)) (role io) hio _
  · have hkw : worldSlot k ≠ worldSlot w := Shared50NodePieceTransport.worldSlot_injective.ne hk
    have hkw' : (role (u := u) (worldSlot k)).val ≠ (role (worldSlot w)).val := by
      intro he; exact hkw (role_injective (Subtype.ext he))
    have hm : role (u := u) (worldSlot k) ∈ (parked w).map role :=
      List.mem_map.mpr ⟨_,(mem_parked _ _).mpr ⟨hkw,active_ne_io k⟩,rfl⟩
    have hh := RoleArrayFrames.saved_role layout ((parked w).map role)
      ((parked_nodup w).map (role_injective (u := u))) n v (role (worldSlot k)) hm
    have hf := moved_other layout (role (worldSlot w)) (role io)
      (RoleArrayFrames.saved layout ((parked w).map role) n v) (role (worldSlot k)).val hkw' hio
    exact ⟨hf.1.trans hh.1,hf.2.trans hh.2⟩

/-- The child I/O payload is literally the former active parent tape. -/
theorem entered_io (w : World) (n : ℕ) (v : Tapes (TapeCount payloadCount u) prime) :
    let mid := RecursiveCallProtocol.entered (parked w) (worldSlot w) io n v
    mid.head (role io).val = 0 ∧ mid.tape (role io).val = v.tape (role (worldSlot w)).val := by
  have hs := RoleArrayFrames.saved_frame layout ((parked w).map role) n v
    (role (u := u) (worldSlot w)).val (role (worldSlot w)).property.1 (by
      intro k hk he
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hk
      exact active_not_parked w (role_injective (Subtype.ext he) ▸ hj))
  have hh := moved_destination layout (role (worldSlot w)) (role io)
    (RoleArrayFrames.saved layout ((parked w).map role) n v)
  exact ⟨hh.1,hh.2.trans hs.2⟩

/-- The parent's actual raw-word representation supplies every finite support
premise required by counted entry and recovery, for arbitrary four symbols. -/
theorem roles_supported {v : RecursiveInterchangeLayout.Descriptor}
    (data : RecursiveMixedSchedule.Data payloadCount v) (k : Fin payloadCount) :
    (RecursiveRoleSerialization.roles data).head k = 0 ∧
      RoleArrayStack.Supported ((RecursiveRoleSerialization.roles data).tape k)
        (RecursiveInterchangeLayout.volume prime v) := by
  constructor
  · rfl
  · change RoleArrayStack.Supported (RecursiveShiftRoleBank.source (data k)) _
    rw [RecursiveRoleSerialization.source_eq_word]
    exact RoleArrayStack.supported_word _ _ (by simp [List.length_ofFn])

/-- Replacing an active parent role is a literal update of its fixed bank slot. -/
theorem bank_setTape (roles : Tapes payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (aux : Tapes u prime) (st : Tapes 2 prime)
    (k : Fin payloadCount) (out : ℤ → Fin (prime+4)) :
    bank (setTape roles k out 0) hs f p aux st =
      setTape (bank roles hs f p aux st) (role (u := u) k).val out 0 := by
  apply congrArg₂ Tapes.mk <;> funext j <;> induction j using Fin.addCases with
  | left j =>
    by_cases hj : j = k
    · subst j; simp [bank,RecursiveShiftRoleBank.common,Tapes.append,role,setTape]
    · have hn := (Fin.castAdd_injective payloadCount (7+((3+u)+2))).ne hj
      simp only [bank,RecursiveShiftRoleBank.common,Tapes.append,Fin.addCases_left,role,setTape,
        Function.update_of_ne hj,Function.update_of_ne hn]
  | right j =>
    have hn : Fin.natAdd payloadCount j ≠ (role (u := u) k).val := by
      intro he; have hv := congrArg Fin.val he; have hk := k.isLt
      simp only [role,Fin.val_natAdd,Fin.val_castAdd] at hv; omega
    change Fin.natAdd payloadCount j ≠ Fin.castAdd (7+((3+u)+2)) k at hn
    simp only [bank,RecursiveShiftRoleBank.common,Tapes.append,Fin.addCases_right,role,setTape,
      Function.update_of_ne hn]

/-- Literal transformed-parent endpoint for `RecursiveCallProtocol.recovers`.
The old parked stack is unchanged because the active role is excluded. -/
theorem entered_bank_updated (w : World) (n : ℕ) (roles : Tapes payloadCount prime)
    (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (aux : Tapes u prime) (st : Tapes 2 prime) (out : ℤ → Fin (prime+4)) :
    RecursiveCallProtocol.entered (parked w) (worldSlot w) io n
      (bank (setTape roles (worldSlot w) out 0) hs f p aux st) =
    setTape (RecursiveCallProtocol.entered (parked w) (worldSlot w) io n
      (bank roles hs f p aux st)) (role (u := u) io).val out 0 := by
  exact (congrArg (RecursiveCallProtocol.entered (parked w) (worldSlot w) io n)
    (bank_setTape roles hs f p aux st (worldSlot w) out)).trans
      (entered_updated w n (bank roles hs f p aux st) out)


/-- Canonical child roles: blank original World workspaces and one I/O word. -/
def childRoles (input : ℤ → Fin (prime+4)) : Tapes payloadCount prime :=
  setTape (SharedBank.empty payloadCount prime) io input 0

private theorem childRoles_unique (vv : Tapes payloadCount prime) (input : ℤ → Fin (prime+4))
    (hw : ∀ w, vv.head (worldSlot w) = 0 ∧ vv.tape (worldSlot w) = fun _ => blank)
    (hi : vv.head io = 0 ∧ vv.tape io = input) : vv = childRoles input := by
  have hp (k : Fin payloadCount) : vv.head k = (childRoles input).head k ∧
      vv.tape k = (childRoles input).tape k := by
    induction k using Fin.addCases with
    | left k =>
      have hh := hw (roleEquiv k)
      have hn : Fin.castAdd 1 k ≠ io := by
        simpa only [worldSlot,Equiv.symm_apply_apply] using active_ne_io (roleEquiv k)
      simpa only [worldSlot,Equiv.symm_apply_apply,childRoles,setTape,Function.update_of_ne hn,SharedBank.empty] using hh
    | right k =>
      have he : Fin.natAdd roleCount k = io := by
        apply Fin.ext; have hk := k.isLt; simp only [io,Fin.val_natAdd,Fin.val_last]; omega
      rw [he]
      simpa only [childRoles,setTape,Function.update_self] using hi
  exact congrArg₂ Tapes.mk (funext fun k => (hp k).1) (funext fun k => (hp k).2)

/-- Literal canonical role bank after the physical payload entry. -/
theorem entered_rolePart (w : World) (n : ℕ) (v : Tapes (TapeCount payloadCount u) prime) :
    rolePart (RecursiveCallProtocol.entered (parked w) (worldSlot w) io n v) =
      childRoles (v.tape (role (worldSlot w)).val) :=
  childRoles_unique _ _ (fun k => entered_world_blank w k n v) (entered_io w n v)

/-- Header setup changes only descriptors/stacks; the actual child bank starts
with canonical blank work roles and the unchanged active parent word. -/
theorem childBank_exact (w : World) (n : ℕ) (v : Tapes (TapeCount payloadCount u) prime)
    (ch : Fin 6 → List Bool) (aux : Tapes u prime) (st : Tapes 2 prime) :
    let mid := RecursiveCallProtocol.entered (parked w) (worldSlot w) io n v
    RecursiveCallProtocol.childBank mid ch aux st =
      bank (childRoles (v.tape (role (worldSlot w)).val)) ch
        (mid.tape (controlSlot 2)) (mid.head (controlSlot 2)) aux st := by
  exact congrArg (fun rr => bank rr ch
    ((RecursiveCallProtocol.entered (parked w) (worldSlot w) io n v).tape (controlSlot 2))
    ((RecursiveCallProtocol.entered (parked w) (worldSlot w) io n v).head (controlSlot 2)) aux st)
      (entered_rolePart w n v)

/-- The actual payload stack retains a blank unbounded suffix for every
nested call, starting at its new physically advanced stack head. -/
theorem entered_bank_blank_suffix (w : World) (n : ℕ) (roles : Tapes payloadCount prime)
    (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (aux : Tapes u prime) (st : Tapes 2 prime) (hf : ∀ z, p ≤ z → f z = blank) :
    let mid := RecursiveCallProtocol.entered (parked w) (worldSlot w) io n (bank roles hs f p aux st)
    ∀ z, mid.head (controlSlot 2) ≤ z → mid.tape (controlSlot 2) z = blank := by
  apply entered_blank_suffix layout ((parked w).map role) (role (worldSlot w)) (role io) n _
  simpa only [layout,(payload_stack roles hs f p aux st).1,(payload_stack roles hs f p aux st).2] using hf

/-- A blank suffix supplies exactly the finite free region required for the
actual reverse parking proof, without a separately provisioned bound. -/
theorem free_of_suffix (w : World) (n : ℕ) (roles : Tapes payloadCount prime)
    (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (aux : Tapes u prime) (st : Tapes 2 prime) (hf : ∀ z, p ≤ z → f z = blank) :
    RoleArrayFrames.Free layout ((parked w).map role) n (bank roles hs f p aux st) := by
  intro z hz _
  simpa only [layout,(payload_stack roles hs f p aux st).2] using
    hf z (by simpa only [layout,(payload_stack roles hs f p aux st).1] using hz)

end
end IntegerMultBounds.Machine.Shared50RecursiveCallSemantics
