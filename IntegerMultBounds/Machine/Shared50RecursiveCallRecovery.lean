import IntegerMultBounds.Machine.Shared50RecursiveCallSemantics
import IntegerMultBounds.Machine.RecursiveRowsSerialization

/-! Actual counted recovery after a child has transformed its I/O word. The
child result is moved back to the active World role and all parked arrays,
stack cells and controls are physically restored. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveCallRecovery
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50GlobalBudget (World)
open Shared50TapeGlobal (roleCount roleEquiv)
open Shared50NodeSegments (payloadCount io)
open Shared50NodePieceTransport (worldSlot)
open Shared50RecursiveCallLayout
open Shared50RecursiveCallSemantics
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveMixedSchedule (Data)
open RecursiveRoleSerialization (roles)
open RecursiveCallBank
open SharedBankStageInput (raw)
open SharedPlacementAlphabet (setTape)
variable {u : ℕ} {v : Descriptor}
attribute [local irreducible] Shared50RecursiveCallLayout.parked Shared50FixedControl.control
  Shared50GlobalCircuit.program50 Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code

theorem roles_update (data : Data payloadCount v) (k : Fin payloadCount) (out : Fin (volume prime v) → Fin 4) :
    roles (Function.update data k out) = setTape (roles data) k (RecursiveShiftRoleBank.source out) 0 := by
  apply congrArg₂ Tapes.mk <;> funext j <;> by_cases hj : j = k
  · subst j; simp only [roles,Function.update_self]
  · simp only [roles,Function.update_of_ne hj]
  · subst j; simp only [roles,Function.update_self]
  · simp only [roles,Function.update_of_ne hj]

/-- A binary child result keeps every World stream binary, including arbitrary
original dirty work-role bits; the separate I/O stream is retained literally. -/
theorem encoded_update (bits : World → Fin (volume prime v) → ZMod 2)
    (extra : Fin (volume prime v) → Fin 4) (w : World) (out : Fin (volume prime v) → ZMod 2) :
    Function.update (Shared50NodeGates.encoded bits extra) (worldSlot w)
      (fun z => SparseRoleCircuit.encode (a := 0) (out z)) =
      Shared50NodeGates.encoded (Function.update bits w out) extra := by
  funext k z
  induction k using Fin.addCases with
  | left k =>
    by_cases hk : roleEquiv k = w
    · have he : Fin.castAdd 1 k = worldSlot w := by rw [← hk]; simp only [worldSlot,Equiv.symm_apply_apply]
      simp only [he,Function.update_self,Shared50NodePieceTransport.encoded_entry]
    · have hn : Fin.castAdd 1 k ≠ worldSlot w := by
        intro he
        have he' := Fin.castAdd_injective _ _ he
        have hh := congrArg roleEquiv he'
        exact hk (hh.trans (roleEquiv.apply_symm_apply w))
      simp only [Function.update_of_ne hn,Shared50NodeGates.encoded,Shared50NodeGates.extend,
        Fin.addCases_left,Shared50RecursiveGates.encoded,Function.update_of_ne hk]
  | right k =>
    have he : Fin.natAdd roleCount k = io := by
      apply Fin.ext; have hk := k.isLt; simp only [io,Fin.val_natAdd,Fin.val_last]; omega
    rw [he,Function.update_of_ne (Shared50NodePieceTransport.io_ne_worldSlot w)]
    change Shared50NodeGates.extend _ extra io z = Shared50NodeGates.extend _ extra io z
    have hi : io = Fin.natAdd roleCount (0 : Fin 1) := by apply Fin.ext; simp [io]
    rw [hi]
    simp only [Shared50NodeGates.extend,Fin.addCases_right]


/-- Exact updated-parent entry endpoint in the canonical array serialization. -/
theorem entered_data_updated (w : World) (data : Data payloadCount v)
    (out : Fin (volume prime v) → Fin 4) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (aux : Tapes u prime) (st : Tapes 2 prime) :
    RecursiveCallProtocol.entered (parked w) (worldSlot w) io (volume prime v)
      (bank (roles (Function.update data (worldSlot w) out)) hs f p aux st) =
    setTape (RecursiveCallProtocol.entered (parked w) (worldSlot w) io (volume prime v)
      (bank (roles data) hs f p aux st)) (role (u := u) io).val (RecursiveShiftRoleBank.source out) 0 :=
  (congrArg (fun rr => RecursiveCallProtocol.entered (parked w) (worldSlot w) io (volume prime v)
    (bank rr hs f p aux st)) (roles_update data (worldSlot w) out)).trans
      (entered_bank_updated w (volume prime v) (roles data) hs f p aux st (RecursiveShiftRoleBank.source out))

/-- Actual count generation, move-back, reverse parking and count erasure.
Its input is the existing entered bank with exactly the returned child word;
its output is the parent data with exactly one updated World stream. -/
theorem recovers (w : World) (data : Data payloadCount v)
    (out : Fin (volume prime v) → Fin 4) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (aux : Tapes u prime) (st : Tapes 2 prime)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive)
    (hf : ∀ z, p ≤ z → f z = blank) (hio : data io = fun _ => blank) :
    HoareTime (RecursiveCallProtocol.recover (u := u) (parked w) (worldSlot w) io (active_ne_io w)).program
      (fun ww => ww = raw (setTape
        (RecursiveCallProtocol.entered (parked w) (worldSlot w) io (volume prime v)
          (bank (roles data) hs f p aux st)) (role (u := u) io).val (RecursiveShiftRoleBank.source out) 0)
        (RecursiveCallProtocol.recover (u := u) (parked w) (worldSlot w) io (active_ne_io w)).tapes)
      (fun ww => ww = raw (bank (roles (Function.update data (worldSlot w) out)) hs f p aux st)
        (RecursiveCallProtocol.recover (u := u) (parked w) (worldSlot w) io (active_ne_io w)).tapes)
      ((92*(parked w).length+51883)*volume prime v) := by
  have hh := RecursiveCallProtocol.recovers (parked w) (parked_nodup w) (worldSlot w) io
    (active_ne_io w) (active_not_parked w) (io_not_parked w) v
    (roles (Function.update data (worldSlot w) out)) hs f p aux st hv hp
    (fun k _ => roles_supported _ k) (fun z hz _ => hf z hz)
    (roles_supported _ _) (by
      constructor
      · rfl
      · change RecursiveShiftRoleBank.source ((Function.update data (worldSlot w) out) io) = _
        rw [Function.update_of_ne (Shared50NodePieceTransport.io_ne_worldSlot w),hio]
        exact RecursiveRowsSerialization.source_blank v)
  apply hh.consequence _ (fun _ h => h) le_rfl
  intro ww hww
  exact hww.trans (congrArg (fun vv => raw vv
    (RecursiveCallProtocol.recover (u := u) (parked w) (worldSlot w) io (active_ne_io w)).tapes)
      (entered_data_updated w data out hs f p aux st).symm)

end
end IntegerMultBounds.Machine.Shared50RecursiveCallRecovery
