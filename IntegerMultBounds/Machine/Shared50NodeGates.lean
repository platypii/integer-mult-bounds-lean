import IntegerMultBounds.Machine.Shared50RecursiveGates
import IntegerMultBounds.Machine.Shared50NodeSegments

/-! Actual Shared50 scalar gates on the complete node payload layout: original
World roles followed by one untouched input/output role. Every generated clock
and volume bit is physically constructed and erased on private tapes. -/
namespace IntegerMultBounds.Machine.Shared50NodeGates
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50TapeGlobal (roleCount)
open Shared50GlobalBudget (World)
open Shared50OrderedPieces (Gate)
open Shared50NodeSegments (payloadCount io)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewFrameRoleBank (bank)
open RecursiveRoleSerialization (roles)
open RecursiveMixedSchedule (Data)
open SharedBankStageInput (raw)
variable {u : ℕ} {v : Descriptor}

def physical (g : Gate) : PointwiseRoleGate.Gate payloadCount where
  src := Fin.castAdd 1 (Shared50RecursiveGates.physical g).src
  dst := Fin.castAdd 1 (Shared50RecursiveGates.physical g).dst
  distinct := (Fin.castAdd_injective _ _).ne (Shared50RecursiveGates.physical g).distinct

def ops (g : Gate) : List (RecursiveMixedSchedule.Op payloadCount) := [.xor (physical g)]
def machine (g : Gate) := RecursiveMixedRoleBank.machine (u := u) (ops g)
def array (g : Gate) (data : Data payloadCount v) := RecursiveMixedSchedule.run (ops g) data

def extend (data : Data roleCount v) (inputOutput : Fin (volume prime v) → Fin 4) : Data payloadCount v :=
  Fin.addCases data (fun _ => inputOutput)

def encoded (data : World → Fin (volume prime v) → ZMod 2) (inputOutput : Fin (volume prime v) → Fin 4) :=
  extend (Shared50RecursiveGates.encoded data) inputOutput

/-- Adding the node I/O tape changes no original role or gate semantics. -/
theorem array_extend (g : Gate) (data : Data roleCount v) (inputOutput : Fin (volume prime v) → Fin 4) :
    array g (extend data inputOutput) = extend (Shared50RecursiveGates.array g data) inputOutput := by
  funext k
  induction k using Fin.addCases with
  | left k =>
    by_cases hk : k = (Shared50RecursiveGates.physical g).dst
    · subst k
      simp only [array,ops,RecursiveMixedSchedule.run,List.foldl_cons,List.foldl_nil,RecursiveMixedSchedule.transform,
        physical,Function.update_self,extend,Fin.addCases_left,Shared50RecursiveGates.array,Shared50RecursiveGates.ops]
    · have hn := (Fin.castAdd_injective roleCount 1).ne hk
      simp only [array,ops,RecursiveMixedSchedule.run,List.foldl_cons,List.foldl_nil,RecursiveMixedSchedule.transform,
        physical,Function.update_of_ne hn,extend,Fin.addCases_left,Shared50RecursiveGates.array,
        Shared50RecursiveGates.ops,Function.update_of_ne hk]
  | right k =>
    have hn : Fin.natAdd roleCount k ≠ Fin.castAdd 1 (Shared50RecursiveGates.physical g).dst := by
      intro he
      have hv := congrArg Fin.val he
      have hd := (Shared50RecursiveGates.physical g).dst.isLt
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    simp only [array,ops,RecursiveMixedSchedule.run,List.foldl_cons,List.foldl_nil,RecursiveMixedSchedule.transform,
      physical,Function.update_of_ne hn,extend,Fin.addCases_right]

/-- The original module gate acts on arbitrary World bit streams; the separate
node I/O stream, including any separator or blank symbols, is retained. -/
theorem array_encoded (g : Gate) (data : World → Fin (volume prime v) → ZMod 2)
    (inputOutput : Fin (volume prime v) → Fin 4) :
    array g (encoded data inputOutput) = encoded (FramedCircuit.moduleGate g.scalar data) inputOutput := by
  unfold encoded
  rw [array_extend,Shared50RecursiveGates.array_encoded]

theorem array_other (g : Gate) (data : Data payloadCount v) (other : Fin payloadCount)
    (hne : other ≠ (physical g).dst) : array g data other = data other := by
  simp only [array,ops,RecursiveMixedSchedule.run,List.foldl_cons,List.foldl_nil,
    RecursiveMixedSchedule.transform,Function.update_of_ne hne]

theorem array_io (g : Gate) (data : Data payloadCount v) : array g data io = data io := by
  apply array_other
  intro he
  have hv := congrArg Fin.val he
  have hd := (Shared50RecursiveGates.physical g).dst.isLt
  simp only [io,physical,Fin.val_last,Fin.val_castAdd] at hv
  omega

/-- Same whole-bank endpoint as node segments and recursive call boundaries,
with arbitrary saved-stack contents and other auxiliary tapes framed exactly. -/
theorem realizes_array (g : Gate) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (st : Tapes 1 prime) (aux : Tapes u prime)
    (data : Data payloadCount v) :
    HoareTime (machine (u := u) g).program
      (fun w => w = raw (bank (roles data) hs st aux) (machine (u := u) g).tapes)
      (fun w => w = raw (bank (roles (array g data)) hs st aux) (machine (u := u) g).tapes)
      (51858*volume prime v) := by
  have hh := RecursiveMixedRoleBank.realizes (ops g) hs st aux hv hp data
  simp only [RecursiveMixedClean.coefficient,ops,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    RecursiveMixedSchedule.coefficient,List.length_cons,List.length_nil] at hh
  norm_num only [Nat.reduceAdd] at hh
  exact hh

theorem realizes (g : Gate) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (st : Tapes 1 prime) (aux : Tapes u prime)
    (data : World → Fin (volume prime v) → ZMod 2) (inputOutput : Fin (volume prime v) → Fin 4) :
    HoareTime (machine (u := u) g).program
      (fun w => w = raw (bank (roles (encoded data inputOutput)) hs st aux) (machine (u := u) g).tapes)
      (fun w => w = raw (bank (roles (encoded (FramedCircuit.moduleGate g.scalar data) inputOutput)) hs st aux)
        (machine (u := u) g).tapes)
      (51858*volume prime v) := by
  simpa only [array_encoded] using realizes_array g hp hs hv st aux (encoded data inputOutput)

end
end IntegerMultBounds.Machine.Shared50NodeGates
