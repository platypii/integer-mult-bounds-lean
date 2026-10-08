import IntegerMultBounds.Machine.RecursiveScalarSchedule
import IntegerMultBounds.Machine.Shared50OrderedPieces

/-! Complete nonrecursive pieces of the actual fixed Shared50 control on the
heterogeneous recursive role bank. Scalar stages construct their own varying
views and restore the original six headers and blank stack. No regrouped
headers, initialized scratch or replacement schedule are supplied. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveSegments
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50TapeGlobal (roleCount roleEquiv)
open Shared50OrderedPieces (Segment stages segment_spec)
open ActualAffineScaling (modulus)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveScalarCoordinates (Address index)
open RecursiveViewedAction (Data)
open RecursiveViewFrameRoleBank (bank)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)
variable {b u : ℕ} {v : Descriptor}
local instance : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
attribute [local irreducible] Shared50FixedControl.control Shared50GlobalCircuit.program50
  Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code

/-- The actual original role number is retained by the physical compiler. -/
def wire (seg : Segment) : Fin roleCount := roleEquiv.symm seg.wire

def machine (seg : Segment) := RecursiveScalarSchedule.machine (u := u) (wire seg) (stages seg)

def coefficient (seg : Segment) := RecursiveScalarSchedule.coefficient (wire seg) (stages seg)

def array (seg : Segment) (hw : v.width=125000*b) (data : Data roleCount v) :=
  RecursiveScalarSchedule.run (wire seg) (stages seg) hw data

/-- Original field-program semantics, keeping all spectators and rows fixed. -/
def execute (seg : Segment) (x : Address 125000 b v) : Address 125000 b v :=
  let out := AffineFieldProgram.run
    (seg.ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))) (x.h,x.d)
  {x with h := out.1, d := out.2}

/-- Actual scalar expansion, including reflection-before-shift subtraction,
executes the original field segment at its retained position in fixed control. -/
theorem execute_exact (seg : Segment) (x : Address 125000 b v) :
    RecursiveScalarSchedule.execute (stages seg) x = execute seg x := by
  have hn : ∀ op ∈ seg.ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b))),
      AffineFieldCoordinates.Nonrecursive op := by
    intro op hop
    obtain ⟨src,hsrc,rfl⟩ := List.mem_map.mp hop
    have hh := (segment_spec seg).2.2 src hsrc
    cases src <;> exact hh
  rw [RecursiveScalarSchedule.execute_eq]
  have he := Shared50NonrecursiveSegments.description_actions seg.parent (segment_spec seg).1 seg.ops
    (segment_spec seg).2.1 (segment_spec seg).2.2 b
  change (stages seg).map (fun op => op.action b) = _ at he
  rw [he]
  change RecursiveScalarSchedule.replaceFields x (OrderedAffine.run _ (AffineFieldCoordinates.embed (x.h,x.d))) = _
  rw [AffineFieldCoordinates.segment_run _ hn]
  simp only [RecursiveScalarSchedule.replaceFields,AffineFieldCoordinates.embed_h,AffineFieldCoordinates.embed_d,execute]

/-- Every input symbol appears at its exact original field-program destination. -/
theorem array_entry (seg : Segment) (hw : v.width=125000*b) (data : Data roleCount v)
    (x : Address 125000 b v) :
    array seg hw data (wire seg) (index hw (execute seg x)) = data (wire seg) (index hw x) := by
  rw [← execute_exact]
  exact RecursiveScalarSchedule.run_entry (wire seg) (stages seg) hw data x

/-- Every other original role tape is unchanged. -/
theorem array_other (seg : Segment) (hw : v.width=125000*b) (data : Data roleCount v)
    (other : Fin roleCount) (hne : other ≠ wire seg) : array seg hw data other = data other :=
  RecursiveScalarSchedule.run_other (wire seg) (stages seg) hw data other hne

/-- One fixed clean program simultaneously satisfies the exact whole-bank
contract, original field permutation and compile-time linear-volume bound. -/
theorem realizes (seg : Segment) (hw : v.width=125000*b) (hp : v.Positive)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (aux : Tapes u prime) (data : Data roleCount v) :
    HoareTime (machine (u := u) seg).program
      (fun w => w = raw (bank (roles data) hs (SharedBank.empty 1 prime) aux) (machine (u := u) seg).tapes)
      (fun w => w = raw (bank (roles (array seg hw data)) hs (SharedBank.empty 1 prime) aux)
          (machine (u := u) seg).tapes ∧
        (∀ x : Address 125000 b v,
          array seg hw data (wire seg) (index hw (execute seg x)) = data (wire seg) (index hw x)) ∧
        ∀ other : Fin roleCount, other ≠ wire seg → array seg hw data other = data other)
      (coefficient seg*volume prime v) := by
  apply (RecursiveScalarSchedule.realizes (wire seg) (stages seg) hw hp hs hv aux data).consequence
    (fun _ h => h) ?_ le_rfl
  intro w hw'
  exact ⟨hw',array_entry seg hw data,array_other seg hw data⟩

end
end IntegerMultBounds.Machine.Shared50RecursiveSegments
