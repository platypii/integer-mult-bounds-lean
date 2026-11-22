module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyChildLayout
public import IntegerMultBounds.Machine.CyclicRowNormalized

/-! Split recursive rows from the trailing spectator field of an inherited interval. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)

open RecursiveInterchangeLayout RecursiveInterchangeScaling in
/-- A subgroup of the trailing spectator field can serve as the cyclic row
index. Its physical offset is the remainder modulo the number of rows. -/
theorem transpose_trailingRows {α : Type} (v : Descriptor) (rows : ℕ) :
    let wide := {v with afterD := v.afterD*rows}
    let size : volume prime v * rows = volume prime wide := by simp [wide,volume,Nat.mul_assoc]
    let locate := fun (i : Fin (volume prime v)) (j : Fin rows) => (finProdFinEquiv (i,j)).cast size
    ∀ (word : Fin (volume prime wide) → α) i j,
      Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word (locate i j) =
        Shared50RecursiveNodeRows.transpose (one_dvd v.rows) (fun k => word (locate k j)) i := by
  intro wide size locate word i j
  let extend (a : Address v) : Address wide :=
    ⟨a.beforeRows,a.row,a.before,a.h,a.middle,a.d,finProdFinEquiv (a.after,j)⟩
  have physical (a : Address v) : locate (RecursiveInterchangeScaling.index a) j = RecursiveInterchangeScaling.index (extend a) := by
    apply Fin.ext
    simp [locate,RecursiveInterchangeScaling.index_val,RecursiveInterchangeLayout.index,extend,wide,finProdFinEquiv]
    ring
  obtain ⟨a,rfl⟩ := (CopyChildLayout.flatAddress v).surjective i
  have old := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) (one_dvd v.rows)
    (fun k => word (locate k j)) (Shared50RecursiveNodeTranspose.swapAddress a)
  have full := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) (one_dvd wide.rows)
    word (Shared50RecursiveNodeTranspose.swapAddress (extend a))
  change Shared50RecursiveNodeRows.transpose (one_dvd v.rows) _ (RecursiveInterchangeScaling.index a) = _ at old
  change Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) _ (RecursiveInterchangeScaling.index (extend a)) = _ at full
  change Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word (locate (RecursiveInterchangeScaling.index a) j) = _
  rw [physical,full]
  exact (congrArg word (physical (Shared50RecursiveNodeTranspose.swapAddress a)).symm).trans old.symm

private theorem singletonRows {a m c : ℕ} (word : Fin (m*c) → Fin (a+4)) :
    let rows := fun (i : Fin m) (j : Fin c) => [word (finProdFinEquiv (i,j))]
    CyclicRowSplit.sourceWord rows = List.ofFn word ∧
    ∀ j, CyclicRowSplit.roleWord rows j = List.ofFn fun i => word (finProdFinEquiv (i,j)) := by
  intro rows
  have singles {n : ℕ} (f : Fin n → Fin (a+4)) : (List.ofFn fun i => [f i]).flatten = List.ofFn f := by
    change (List.ofFn ((fun x => [x]) ∘ f)).flatten = _
    rw [← List.map_ofFn]
    generalize List.ofFn f = xs
    induction xs <;> simp [*]
  constructor
  · change (List.ofFn fun i : Fin m => (List.ofFn fun j : Fin c => [word (finProdFinEquiv (i,j))]).flatten).flatten = _
    simp only [singles]
    simpa only [finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using (List.ofFn_mul word).symm
  · intro j
    exact singles _

/-- The cyclic splitter and merger read one symbol per row at each visit.
They restore all heads and counters and each costs at most 149 steps per input symbol. -/
theorem trailingRows_exec {a m c q b : ℕ} (groups : 0 < m) (lanes : 0 < c)
    (common : ℤ → Fin (a+4)) (roles : Fin c → ℤ → Fin (a+4))
    (x y : Fin (m*c) → Fin (a+4)) (inner : Program (((1+c)+2)+2) q a) :
    let bs := FlatCoordinateSchedule.bits 1
    let gs := FlatCoordinateSchedule.bits m
    let bank := fun src streams => CyclicRowSplit.bank (CyclicRowCopy.bank src streams 0 (fun _ => 0) bs) gs
    let parts := fun (word : Fin (m*c) → Fin (a+4)) j =>
      putWord (roles j) 0 (List.ofFn fun i : Fin m => word (finProdFinEquiv (i,j)))
    let src := putWord common 0 (List.ofFn x)
    HoareTime inner (fun z => z = bank src (parts x)) (fun z => z = bank src (parts y)) b →
    HoareTime (seq (seq (CyclicRowNormalized.splitProgram c a) inner) (CyclicRowNormalized.mergeProgram c a))
      (fun z => z = bank src roles) (fun z => z = bank (putWord common 0 (List.ofFn y)) (parts y))
      (298*(m*c)+b+2) := by
  intro bs gs bank parts src run
  let rows := fun (word : Fin (m*c) → Fin (a+4)) (i : Fin m) (j : Fin c) => [word (finProdFinEquiv (i,j))]
  have bound := CyclicRowNormalized.cost_linear 1 bs gs lanes groups (by decide)
    (FlatCoordinateSchedule.bits_value 1) (FlatCoordinateSchedule.bits_value m)
    (FlatCoordinateSchedule.bits_canonical 1) (FlatCoordinateSchedule.bits_canonical m)
  rw [Nat.mul_one] at bound
  have split := CyclicRowNormalized.split_hoare common roles 0 (fun _ => 0) (rows x) 1 (fun _ _ => rfl)
    bs gs (FlatCoordinateSchedule.bits_value 1) (FlatCoordinateSchedule.bits_value m)
  have merge := CyclicRowNormalized.merge_hoare src roles 0 (fun _ => 0) (rows y) 1 (fun _ _ => rfl)
    bs gs (FlatCoordinateSchedule.bits_value 1) (FlatCoordinateSchedule.bits_value m)
  obtain ⟨sx,px⟩ := singletonRows x
  obtain ⟨sy,py⟩ := singletonRows y
  change CyclicRowSplit.sourceWord (rows x) = _ at sx
  change CyclicRowSplit.sourceWord (rows y) = _ at sy
  change ∀ j, CyclicRowSplit.roleWord (rows x) j = _ at px
  change ∀ j, CyclicRowSplit.roleWord (rows y) j = _ at py
  simp only [sx,px] at split
  simp only [sy,py] at merge
  have overwrite : putWord src 0 (List.ofFn y) = putWord common 0 (List.ofFn y) :=
    FlatControlledShiftArray.overwrite _ _ _ _ (by simp)
  rw [overwrite] at merge
  exact ((split.seq run).seq merge).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.M6.BitNode
