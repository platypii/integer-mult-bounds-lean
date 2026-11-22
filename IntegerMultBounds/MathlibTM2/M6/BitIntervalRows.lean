module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyChildLayout
public import IntegerMultBounds.Machine.CyclicRowNormalized

/-! Split recursive rows from the trailing spectator field of an inherited interval. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)

section
open RecursiveInterchangeLayout
/-- Select the same contiguous field in each active word, retaining the
parent's prefix, middle and trailing spectator tapes in physical order. -/
noncomputable def inheritedInterval (v : Descriptor) (p width s : ℕ) : Descriptor :=
  { v with
    beforeH := v.beforeH*prime^p
    width := width
    between := prime^s*v.between*prime^p
    afterD := prime^s*v.afterD }

theorem inheritedInterval_volume (v : Descriptor) (p w s : ℕ) (split : v.width = p+w+s) :
    volume prime (inheritedInterval v p w s) = volume prime v := by
  simp only [volume,inheritedInterval,split,pow_add]
  ring

theorem inheritedInterval_nested (v : Descriptor) (p w s p' w' s' : ℕ) :
    inheritedInterval (inheritedInterval v p w s) p' w' s' =
      inheritedInterval v (p+p') w' (s'+s) := by
  simp only [inheritedInterval,pow_add,Nat.mul_assoc]

theorem inheritedInterval_flat (lo hi axes w W : ℕ) :
    inheritedInterval ⟨1,1,1,axes*w,1,W⟩ (lo*w) ((hi-lo)*w) ((axes-hi)*w) =
      phaseIntervalChild lo hi w W axes := by
  simp only [inheritedInterval,phaseIntervalChild,Nat.one_mul,Nat.mul_one,pow_add,
    ← pow_mul,Nat.mul_comm w]

/-- Regrouping the spectator digits and narrowing both active fields retains
the same serialized cell, including on a parent with a nontrivial middle. -/
theorem inheritedInterval_index (v : Descriptor) (p w s : ℕ) (split : v.width = p+w+s)
    (a row before middle after hp h hs dp d ds : ℕ) :
    index prime (inheritedInterval v p w s) a row (before*prime^p+hp) h
      ((hs*v.between+middle)*prime^p+dp) d (ds*v.afterD+after) =
    index prime v a row before ((hp*prime^w+h)*prime^s+hs) middle
      ((dp*prime^w+d)*prime^s+ds) after := by
  simp only [index,inheritedInterval,split,pow_add]
  ring

/-- In the parent word, the child's transpose exchanges only the selected
digits. Both prefixes, both suffixes and the middle spectator stay fixed. -/
theorem inheritedInterval_transpose {α : Type*} (v : Descriptor) (p w s : ℕ)
    (split : v.width = p+w+s) (word : Fin (volume prime v) → α)
    (a : RecursiveInterchangeScaling.Address v) (hp dp : Fin (prime^p))
    (hs ds : Fin (prime^s)) (h d : Fin (prime^w)) :
    let child := inheritedInterval v p w s
    let size := inheritedInterval_volume v p w s split
    let fieldSize : prime^p*prime^w*prime^s = prime^v.width := by rw [split,pow_add,pow_add]
    let field := fun u x z => (finProdFinEquiv (finProdFinEquiv (u,x),z)).cast fieldSize
    let locate := fun x y => RecursiveInterchangeScaling.index
      {a with h := field hp x hs, d := field dp y ds}
    Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (fun i => word (i.cast size))
      ((locate d h).cast size.symm) = word (locate h d) := by
  intro child size fieldSize field locate
  let addr (x y : Fin (prime^w)) : RecursiveInterchangeScaling.Address child :=
    ⟨a.beforeRows,a.row,finProdFinEquiv (a.before,hp),x,
      finProdFinEquiv (finProdFinEquiv (hs,a.middle),dp),y,finProdFinEquiv (ds,a.after)⟩
  have physical (x y : Fin (prime^w)) :
      RecursiveInterchangeScaling.index (addr x y) = (locate x y).cast size.symm := by
    apply Fin.ext
    simp only [Fin.val_cast,locate,RecursiveInterchangeScaling.index_val,addr,field,
      finProdFinEquiv,Equiv.coe_fn_mk,Fin.val_cast]
    simpa only [Nat.add_comm,Nat.mul_comm] using
      inheritedInterval_index v p w s split a.beforeRows a.row a.before a.middle a.after hp x hs dp y ds
  have swap := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) (one_dvd child.rows)
    (fun i => word (i.cast size)) (addr h d)
  change Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (fun i => word (i.cast size)) (RecursiveInterchangeScaling.index (addr d h)) = word ((RecursiveInterchangeScaling.index (addr h d)).cast size) at swap
  simpa only [physical,Fin.cast_cast,Fin.cast_refl,id_eq] using swap
end

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

theorem singletonRows {a m c : ℕ} (word : Fin (m*c) → Fin (a+4)) :
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
