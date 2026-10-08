import IntegerMultBounds.Machine.Shared50RecursiveNodeRows

/-! Full fixed Shared50 control, including its pre/post moves, on every binary
cyclic row fiber. Its routed result is exactly the permuted merge input for the
parent H/D transpose. The common I/O slot never participates in the network. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveNodeSemantics
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50TapeGlobal (roleCount roleEquiv)
open Shared50GlobalBudget (World)
open RecursiveInterchangeLayout (Descriptor volume role)
open RecursiveInterchangeRows (groups rowLength pack roleIndex)
open Shared50RecursiveNodeRows
open Shared50RecursiveNodeLayout (wires mergeRoute)
variable {b : ℕ} {v : Descriptor}
local instance : NeZero (ActualAffineScaling.modulus b) := ⟨ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
local instance : NeZero (prime^b) := ⟨ne_of_gt (pow_pos Shared50ModularControl.prime_prime.pos _)⟩

def rank (hw : v.width=125000*b) (x : Fin 125000 → ZMod (prime^b)) : Fin (prime^v.width) :=
  Fin.cast (by rw [← pow_mul,Nat.mul_comm b,hw]) (FlatCoordinateLayout.rank x)

def coordinates (hw : v.width=125000*b) (x : Fin (prime^v.width)) : Fin 125000 → ZMod (prime^b) :=
  FlatCoordinateLayout.coordinates (Fin.cast (by rw [← pow_mul,Nat.mul_comm b,hw]) x)

@[simp] theorem rank_coordinates (hw : v.width=125000*b) (x : Fin (prime^v.width)) :
    rank hw (coordinates hw x) = x := by
  simp [rank,coordinates]

@[simp] theorem coordinates_rank (hw : v.width=125000*b) (x : Fin 125000 → ZMod (prime^b)) :
    coordinates hw (rank hw x) = x := by
  simp [rank,coordinates]

/-- Original field coordinates and cyclic row serialization name the same cell. -/
theorem scalar_index (hw : v.width=125000*b)
    (a : RecursiveScalarCoordinates.Address 125000 b (role v roleCount)) :
    RecursiveScalarCoordinates.index (v := role v roleCount) hw a = roleIndex prime roleCount v
      (pack a.beforeRows a.row) (suffixPack (a.before,rank hw a.h,a.middle,rank hw a.d,a.after)) := by
  apply Fin.ext
  trans RecursiveInterchangeLayout.index prime (role v roleCount) a.beforeRows.val a.row.val a.before.val
    (FlatCoordinateLayout.rank a.h).val a.middle.val (FlatCoordinateLayout.rank a.d).val a.after.val
  · exact RecursiveScalarCoordinates.index_val (v := role v roleCount) hw a
  · change RecursiveInterchangeLayout.index prime (role v roleCount) a.beforeRows.val a.row.val a.before.val
      (FlatCoordinateLayout.rank a.h).val a.middle.val (FlatCoordinateLayout.rank a.d).val a.after.val =
        (pack (pack a.beforeRows a.row) (suffixPack (a.before,rank hw a.h,a.middle,rank hw a.d,a.after))).val
    simp only [RecursiveInterchangeRows.pack_val,suffixPack,RecursiveInterchangeRows.suffixIndex,
      rank,RecursiveInterchangeLayout.index,role,rowLength]
    dsimp only [Fin.cast,ActualAffineScaling.modulus]
    ring


def splitBits (hd : roleCount ∣ v.rows) (x : Fin (volume prime v) → ZMod 2)
    (j : Fin roleCount) (z : Fin (volume prime (role v roleCount))) : ZMod 2 :=
  let gk := finProdFinEquiv.symm (Fin.cast (RecursiveInterchangeRows.role_volume prime roleCount v) z)
  x (Fin.cast (RecursiveInterchangeRows.volume_split prime roleCount v hd).symm (pack gk.1 (pack j gk.2)))

def encoded (x : Fin (volume prime v) → ZMod 2) : Fin (volume prime v) → Fin 4 :=
  fun i => SparseRoleCircuit.encode (x i)

theorem encoded_transpose (hd : roleCount ∣ v.rows) (x : Fin (volume prime v) → ZMod 2) :
    encoded (transpose hd x) = transpose hd (encoded x) := rfl


theorem encode_split (hd : roleCount ∣ v.rows) (x : Fin (volume prime v) → ZMod 2)
    (j : Fin roleCount) (z : Fin (volume prime (role v roleCount))) :
    SparseRoleCircuit.encode (splitBits hd x j z) = RecursiveRowsSerialization.roleArray hd (encoded x) j z := rfl

def stored (hw : v.width=125000*b) (hd : roleCount ∣ v.rows)
    (x : Fin (volume prime v) → ZMod 2) (g : Fin (groups roleCount v))
    (a : Fin v.beforeH) (m : Fin v.between) (e : Fin v.afterD) :
    World → Shared50ModularExecution.Arrays (prime^b) := fun i z =>
  splitBits hd x (roleEquiv.symm i)
    (roleIndex prime roleCount v g (suffixPack (a,rank hw z.1,m,rank hw z.2,e)))

/-- Literal semantics of the fixed list on a flat role array. -/
def networkBits (hw : v.width=125000*b) (hd : roleCount ∣ v.rows)
    (x : Fin (volume prime v) → ZMod 2) (i : Fin roleCount)
    (z : Fin (volume prime (role v roleCount))) : ZMod 2 :=
  let gk := finProdFinEquiv.symm (Fin.cast (RecursiveInterchangeRows.role_volume prime roleCount v) z)
  let s := suffixUnpack gk.2
  FramedControlSchedule.run (Shared50OrderedControl.edgeAction b) Shared50FixedControl.control
    (stored hw hd x gk.1 s.1 s.2.2.1 s.2.2.2.2) (roleEquiv i)
    (coordinates hw s.2.1,coordinates hw s.2.2.2.1)

/-- Full routed transpose, not just the middle shear circuit. -/
theorem networkBits_exact (hw : v.width=125000*b) (hd : roleCount ∣ v.rows)
    (x : Fin (volume prime v) → ZMod 2) (i : Fin roleCount)
    (z : Fin (volume prime (role v roleCount))) :
    networkBits hw hd x i z = splitBits hd x (mergeRoute.symm i) (roleSwap z) := by
  dsimp only [networkBits]
  rw [Shared50FixedControl.run_identity]
  simp only [stored,rank_coordinates,Shared50RecursiveNodeLayout.mergeRoute_symm,roleSwap,swapSuffix]

/-- Network output with the separate common slot still physically blank. -/
def networkData (hw : v.width=125000*b) (hd : roleCount ∣ v.rows)
    (x : Fin (volume prime v) → ZMod 2) :
    RecursiveRowsSerialization.Data (roleCount+1) (role v roleCount) :=
  RecursiveRowsSerialization.putData wires
    (Fin.addCases (fun _ _ => blank) (fun i z => SparseRoleCircuit.encode (networkBits hw hd x i z)))

theorem networkData_merge_input (hw : v.width=125000*b) (hd : roleCount ∣ v.rows)
    (x : Fin (volume prime v) → ZMod 2) :
    networkData hw hd x = RecursiveRowsSerialization.roleData wires mergeRoute hd
      (transpose hd (encoded x)) := by
  unfold networkData RecursiveRowsSerialization.roleData
  congr 1
  funext i z
  induction i using Fin.addCases with
  | left i => simp only [Fin.addCases_left,RecursiveRowsSerialization.roleLocal]
  | right i =>
    simp only [Fin.addCases_right,RecursiveRowsSerialization.roleLocal]
    rw [networkBits_exact,encode_split,split_transpose]

/-- The actual physical node exit consumes the proven fixed-control result. -/
theorem exit_network {u : ℕ} (hw : v.width=125000*b) (hd : roleCount ∣ v.rows)
    (x : Fin (volume prime v) → ZMod 2) (old hs : Fin 6 → List Bool)
    (st : Tapes 1 prime) (aux : Tapes u prime)
    (hav : RecursiveStackAllocation.Available 0 st)
    (hv : RecursiveDimensionBank.Headers v old) (hp : v.Positive) :
    HoareTime (Shared50RecursiveNodeLayout.exit (u := u)).program
      (fun w => w = SharedBankStageInput.raw
        (RecursiveViewFrameRoleBank.bank (RecursiveRoleSerialization.roles (networkData hw hd x))
          hs (RecursiveViewFrame.savedStack old st) aux) (Shared50RecursiveNodeLayout.exit (u := u)).tapes)
      (fun w => w = SharedBankStageInput.raw
        (RecursiveViewFrameRoleBank.bank (RecursiveRoleSerialization.roles
          (RecursiveRowsSerialization.sourceData wires (transpose hd (encoded x)))) old st aux)
        (Shared50RecursiveNodeLayout.exit (u := u)).tapes)
      (RecursiveViewFrame.restoreCost old hs+RecursiveRowsClean.bound roleCount (volume prime v)+1) := by
  rw [networkData_merge_input]
  exact RecursiveRowsNode.exit_hoare mergeRoute wires Shared50RecursiveNodeLayout.wires_injective old hs st aux
    (RecursiveRowsNode.free_of_available old st hav) v (by decide) hv hp hd (transpose hd (encoded x))

end
end IntegerMultBounds.Machine.Shared50RecursiveNodeSemantics
