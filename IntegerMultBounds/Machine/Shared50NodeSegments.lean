import IntegerMultBounds.Machine.Shared50RecursiveSegments

/-! Actual nonrecursive segment adapters for the complete node payload layout:
all original World roles first, then the separate node input/output role. -/
namespace IntegerMultBounds.Machine.Shared50NodeSegments
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50TapeGlobal (roleCount)
open Shared50OrderedPieces (Segment stages)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveScalarCoordinates (Address index)
open RecursiveViewedAction (Data)
open RecursiveViewFrameRoleBank (bank)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)
variable {b u : ℕ} {v : Descriptor}

abbrev payloadCount := roleCount+1

def wire (seg : Segment) : Fin payloadCount := Fin.castAdd 1 (Shared50RecursiveSegments.wire seg)
def io : Fin payloadCount := Fin.last roleCount

def machine (seg : Segment) := RecursiveScalarSchedule.machine (u := u) (wire seg) (stages seg)
def coefficient (seg : Segment) := RecursiveScalarSchedule.coefficient (wire seg) (stages seg)
def array (seg : Segment) (hw : v.width=125000*b) (data : Data payloadCount v) :=
  RecursiveScalarSchedule.run (wire seg) (stages seg) hw data

/-- Original nonrecursive field semantics on the cast-in World role. -/
theorem array_entry (seg : Segment) (hw : v.width=125000*b) (data : Data payloadCount v)
    (x : Address 125000 b v) :
    array seg hw data (wire seg) (index hw (Shared50RecursiveSegments.execute seg x)) =
      data (wire seg) (index hw x) := by
  rw [← Shared50RecursiveSegments.execute_exact]
  exact RecursiveScalarSchedule.run_entry (wire seg) (stages seg) hw data x

theorem array_other (seg : Segment) (hw : v.width=125000*b) (data : Data payloadCount v)
    (other : Fin payloadCount) (hne : other ≠ wire seg) : array seg hw data other = data other :=
  RecursiveScalarSchedule.run_other (wire seg) (stages seg) hw data other hne

/-- The separate node input/output stream is always a literal spectator. -/
theorem array_io (seg : Segment) (hw : v.width=125000*b) (data : Data payloadCount v) :
    array seg hw data io = data io := by
  apply array_other
  intro he
  have hv := congrArg Fin.val he
  have hi := (Shared50RecursiveSegments.wire seg).isLt
  simp only [io,wire,Fin.val_last,Fin.val_castAdd] at hv
  omega

/-- Exact common-prefix contract for the same role-plus-I/O bank used by
physical node split, recursive calls and final merge. -/
theorem realizes (seg : Segment) (hw : v.width=125000*b) (hp : v.Positive)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (aux : Tapes u prime) (data : Data payloadCount v) :
    HoareTime (machine (u := u) seg).program
      (fun w => w = raw (bank (roles data) hs (SharedBank.empty 1 prime) aux) (machine (u := u) seg).tapes)
      (fun w => w = raw (bank (roles (array seg hw data)) hs (SharedBank.empty 1 prime) aux)
          (machine (u := u) seg).tapes)
      (coefficient seg*volume prime v) :=
  RecursiveScalarSchedule.realizes (wire seg) (stages seg) hw hp hs hv aux data

end
end IntegerMultBounds.Machine.Shared50NodeSegments
