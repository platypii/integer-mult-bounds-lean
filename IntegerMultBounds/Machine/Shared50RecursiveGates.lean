import IntegerMultBounds.Machine.RecursiveMixedRoleBank
import IntegerMultBounds.Machine.Shared50OrderedPieces

/-! Actual fixed Shared50 gate pieces on the recursive permanent bank, starting
with only the six layout headers. The stream-volume controls are constructed,
used, and physically erased. Arbitrary original dirty temporary values are
included in the exact module-gate semantics rather than assumed zero. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveGates
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50TapeGlobal (roleCount roleEquiv)
open Shared50GlobalBudget (World)
open Shared50OrderedPieces (Gate gate_xor)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewFrameRoleBank (bank)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)
variable {u : ℕ} {v : Descriptor}
attribute [local irreducible] Shared50FixedControl.control Shared50GlobalCircuit.program50
  Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code

private theorem witness (g : Gate) :
    ∃ dst src, dst ≠ src ∧ g.scalar = ReversibleFanout.add dst src :=
  gate_xor g g.scalar List.mem_cons_self

/-- The original scalar gate, with its original World names enumerated as
permanent role slots. The occurrence certificate supplies distinctness. -/
def physical (g : Gate) : PointwiseRoleGate.Gate roleCount where
  dst := roleEquiv.symm (Classical.choose (witness g))
  src := roleEquiv.symm (Classical.choose (Classical.choose_spec (witness g)))
  distinct := roleEquiv.symm.injective.ne (Classical.choose_spec (Classical.choose_spec (witness g))).1.symm

theorem physical_scalar (g : Gate) :
    SparseRoleCircuit.scalar (physical g) = g.scalar.rename roleEquiv.symm := by
  conv_rhs => rw [(Classical.choose_spec (Classical.choose_spec (witness g))).2]
  rfl

def ops (g : Gate) : List (RecursiveMixedSchedule.Op roleCount) := [.xor (physical g)]

def machine (g : Gate) := RecursiveMixedRoleBank.machine (u := u) (ops g)

def array (g : Gate) (data : RecursiveMixedSchedule.Data roleCount v) :=
  RecursiveMixedSchedule.run (ops g) data

/-- Bits on every original role, including dirty temporaries and spectators. -/
def encoded (data : World → Fin (volume prime v) → ZMod 2) : RecursiveMixedSchedule.Data roleCount v :=
  fun k i => SparseRoleCircuit.encode (a := 0) (data (roleEquiv k) i)

/-- No semantic replacement gate is introduced: the output is the original
module gate at each symbol of its original physical role streams. -/
theorem array_encoded (g : Gate) (data : World → Fin (volume prime v) → ZMod 2) :
    array g (encoded data) = encoded (FramedCircuit.moduleGate g.scalar data) := by
  have hh := SparseRoleCircuit.execute_encoded (a := 0) [physical g] (fun k i => data (roleEquiv k) i)
  simp only [List.map_cons,List.map_nil,Circuit.run_cons,Circuit.run_nil,physical_scalar] at hh
  have he (k : Fin roleCount) (i : Fin (volume prime v)) :
      (g.scalar.rename roleEquiv.symm).run (fun k => data (roleEquiv k) i) k =
        FramedCircuit.moduleGate g.scalar data (roleEquiv k) i := by
    rw [FramedCircuit.moduleGate_pointwise]
    have hr := congrFun (Circuit.Gate.run_rename roleEquiv.symm g.scalar (fun k => data (roleEquiv k) i)) (roleEquiv k)
    simpa only [Function.comp_apply,Function.comp_def,Equiv.symm_apply_apply,Equiv.apply_symm_apply] using hr
  change array g (encoded data) = SparseRoleCircuit.encoded
    (fun k i => (g.scalar.rename roleEquiv.symm).run (fun k => data (roleEquiv k) i) k) at hh
  simp only [he] at hh
  exact hh

/-- Generic four-symbol output also preserves every non-target role literally. -/
theorem array_other (g : Gate) (data : RecursiveMixedSchedule.Data roleCount v)
    (other : Fin roleCount) (hne : other ≠ (physical g).dst) : array g data other = data other := by
  simp only [array,ops,RecursiveMixedSchedule.run,List.foldl_cons,List.foldl_nil,
    RecursiveMixedSchedule.transform,Function.update_of_ne hne]

/-- All generated control bits, sentinels and work tapes are erased; the
original stack and arbitrary auxiliaries are retained without any reset. -/
theorem realizes_array (g : Gate) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (st : Tapes 1 prime) (aux : Tapes u prime)
    (data : RecursiveMixedSchedule.Data roleCount v) :
    HoareTime (machine (u := u) g).program
      (fun w => w = raw (bank (roles data) hs st aux) (machine (u := u) g).tapes)
      (fun w => w = raw (bank (roles (array g data)) hs st aux) (machine (u := u) g).tapes)
      (51858*volume prime v) := by
  have hh := RecursiveMixedRoleBank.realizes (ops g) hs st aux hv hp data
  simp only [RecursiveMixedClean.coefficient,ops,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    RecursiveMixedSchedule.coefficient,List.length_cons,List.length_nil] at hh
  norm_num only [Nat.reduceAdd] at hh
  exact hh

/-- Fully initialized and cleaned physical realization of the actual Shared50
gate, for arbitrary bit values on every role. In particular no dirty temporary
is initialized or discarded for free. -/
theorem realizes (g : Gate) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (st : Tapes 1 prime) (aux : Tapes u prime)
    (data : World → Fin (volume prime v) → ZMod 2) :
    HoareTime (machine (u := u) g).program
      (fun w => w = raw (bank (roles (encoded data)) hs st aux) (machine (u := u) g).tapes)
      (fun w => w = raw (bank (roles (encoded (FramedCircuit.moduleGate g.scalar data))) hs st aux)
        (machine (u := u) g).tapes)
      (51858*volume prime v) := by
  simpa only [array_encoded] using realizes_array g hp hs hv st aux (encoded data)

end
end IntegerMultBounds.Machine.Shared50RecursiveGates
