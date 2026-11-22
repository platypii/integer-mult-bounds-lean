module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyChildLayout
public import IntegerMultBounds.Machine.Shared50RecursiveNodeTranspose
public import IntegerMultBounds.MathlibTM2.M6.BitPackedStageHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitScheduledFlatRuns

/-! Assemble the PR589 node directly in the flat layout used by the recursive stages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open Certificates.PR589.Nine
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeScaling (Address index)

/-- One contiguous pair of active fields followed by the spectator word. -/
def flatNodeDescriptor (w W : ℕ) : Descriptor := ⟨1,1,1,64*w,1,W⟩

theorem flatNodeVolume (w W : ℕ) :
    volume prime (flatNodeDescriptor w W) = (prime^w)^128*W := by
  simp only [volume,flatNodeDescriptor,one_mul,mul_one,← pow_add,← pow_mul]
  congr 2
  omega

/-- Once the inherited fields are packed, the resulting offset already is the
flat node offset. No further permutation of the spectator is required. -/
theorem packActive_flatNode (w W : ℕ) (i : Fin (volume prime (flatNodeDescriptor w W))) :
    (CopyChildLayout.packActive (flatNodeDescriptor w W) i).val = i.val := by
  obtain ⟨a,rfl⟩ := (CopyChildLayout.flatAddress (flatNodeDescriptor w W)).surjective i
  change (CopyChildLayout.packActive _ (index a)).val = (index a).val
  rw [CopyChildLayout.packActive_index,RecursiveInterchangeScaling.index_val]
  have zero (k : Fin 1) : k.val = 0 := Nat.lt_one_iff.mp k.isLt
  change (a.after.val + W*(a.middle.val + 1*(a.before.val + 1*(a.row.val + 1*a.beforeRows.val)))) +
    (1*1*1*1*W)*(a.d.val + prime^(64*w)*a.h.val) = _
  simp only [RecursiveInterchangeLayout.index,flatNodeDescriptor,zero,zero_mul,zero_add,
    mul_one,one_mul,add_zero]
  ring

/-- Packing an inherited address gives exactly the flat node's physical
address under the spectator-preserving layout change. -/
theorem packActive_nodeAddress (v : Descriptor) (w : ℕ) (width : v.width = 64*w)
    (a : Address v) :
    let node := flatNodeDescriptor w (CopyChildLayout.spectators v)
    let size : CopyChildLayout.spectators v = CopyChildLayout.spectators node := by
      simp [node,flatNodeDescriptor,CopyChildLayout.spectators]
    (CopyChildLayout.packActive v (index a)).val =
      (index (CopyChildLayout.changeLayout v node width size a)).val := by
  intro node size
  exact (CopyChildLayout.packActive_change v node width size a).symm.trans
    (packActive_flatNode w _ _)

/-- The flat node's physical field swap is the recursive descriptor transpose
at the same serialized cells. -/
theorem flatNodeTranspose {w W : ℕ} {α : Type} (x : Fin ((prime^w)^128*W) → α)
    (h d : Fin 64 → ZMod (prime^w)) (j : Fin W) :
    Shared50RecursiveNodeRows.transpose (one_dvd (flatNodeDescriptor w W).rows)
      (fun i => x (i.cast (flatNodeVolume w W)))
      ((FlatCoordinateLayout.index (Fin.append h d) j).cast (flatNodeVolume w W).symm) =
      x (FlatCoordinateLayout.index (Fin.append d h) j) := by
  have width : (prime^w)^64 = prime^(64*w) := by rw [← pow_mul,Nat.mul_comm]
  let addr (a b : Fin 64 → ZMod (prime^w)) : Address (flatNodeDescriptor w W) :=
    ⟨(0 : Fin 1),(0 : Fin 1),(0 : Fin 1),(FlatCoordinateLayout.rank a).cast width,(0 : Fin 1),(FlatCoordinateLayout.rank b).cast width,j⟩
  have cell (a b) : index (addr a b) =
      (FlatCoordinateLayout.index (Fin.append a b) j).cast (flatNodeVolume w W).symm := by
    apply Fin.ext
    rw [RecursiveInterchangeScaling.index_val,Fin.val_cast,FlatCoordinateLayout.index_val]
    have digits : (FlatCoordinateLayout.rank (Fin.append a b)).val =
        (FlatCoordinateLayout.rank a).val*(prime^w)^64+(FlatCoordinateLayout.rank b).val :=
      ArbitraryWidthSliceTranspose.rank_append a b
    rw [digits]
    simp only [addr,flatNodeDescriptor,RecursiveInterchangeLayout.index,Fin.val_zero,
      zero_mul,zero_add,mul_one,add_zero,width]
    rfl
  rw [← cell]
  have swap := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1)
    (one_dvd (flatNodeDescriptor w W).rows) (fun i => x (i.cast (flatNodeVolume w W))) (addr d h)
  calc
    _ = x ((index (addr d h)).cast (flatNodeVolume w W)) := swap
    _ = _ := by rw [cell]; rfl

/-- Sweeps and idle windows on exact flat words compose to interchange the two
parent fields on every role. The spectator and the two piece-cost sums are preserved. -/
theorem assembledFlatNode {U : Type} :
    ∃ states : ℕ, ∀ {Q w W V : ℕ}, states ≤ Q → (size : (prime^w)^128*W = V) → 0 < V →
      let address := fun (j : Fin W) s => (flatWindowEquiv w W (s,j)).cast size
      let reads := fun (piece : Piece) (x y : Fin 142081 → Fin V → ZMod 2) =>
        ∀ j, let addr := fun z => address j (windowState w z)
          readRoles addr y = piece.run (readRoles addr x)
      ∀ (sweepCost idleCost : Fin 9 → ℕ),
      (∀ n, ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst seed,
        PackedPieceHandoff V (reads (.stage n)) body code src dst seed (sweepCost n)) →
      (∀ n, ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst seed,
        PackedPieceHandoff V (reads (.remainder n.val)) body code src dst seed (idleCost n)) →
      ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst seed,
        PackedPieceHandoff V (fun x y => ∀ (r : Role) (i : Fin ((prime^w)^128*W)),
          let tape := sweepRoleTape r
          y tape (i.cast size) = Shared50RecursiveNodeRows.transpose
            (one_dvd (flatNodeDescriptor w W).rows)
            (fun k => x tape (k.cast ((flatNodeVolume w W).trans size)))
            (i.cast (flatNodeVolume w W).symm)) body code src dst seed
          ((∑ i, sweepCost i)+(∑ i, idleCost i)+9*(2*(76*17760*V*(142081+7)+6)+1+(142081*(8*V+10)+1))+2) := by
  obtain ⟨states,build⟩ := assembledPackedNode (U := U)
  refine ⟨states,?_⟩
  intro Q w W V fits size pos address reads sweepCost idleCost sweeps windows
  have volume : (prime^w)^16*(1*((prime^w)^112*W)) = V := by
    simpa only [Nat.one_mul] using (ordinaryCompact_width (prime^w) W).trans size
  cases volume
  obtain ⟨P,T,body,code,src,dst,seed,run⟩ := build fits w 1 W pos
    (fun n => reads (.stage n)) (fun n => reads (.remainder n.val)) sweepCost idleCost sweeps windows
  refine ⟨P,T,body,code,src,dst,seed,?_⟩
  intro x u S words privateTapes
  obtain ⟨z,F,k,y,exec,paid,user,out,trace⟩ := run x u S words privateTapes
  refine ⟨z,F,k,y,exec,paid,user,out,?_⟩
  intro r i
  obtain ⟨⟨s,j⟩,rfl⟩ := (flatWindowEquiv w W).surjective i
  have swapped := modularEndpoint r (fun _ => address j) x y
    (nodePieceEffect_read _ (fun n a d h => h j) (fun n a d h => h j) trace) s
  have transposed := flatNodeTranspose (fun k => x (sweepRoleTape r) (k.cast size))
    (s.1 ∘ stageAxis.symm) (s.2 ∘ stageAxis.symm) j
  rw [flatWindowEquiv_fields]
  exact (by simpa only [address,flatWindowEquiv_fields,sweepRoleTape_eq] using swapped :
    y (sweepRoleTape r) _ = x (sweepRoleTape r) _).trans transposed.symm

end IntegerMultBounds.MathlibTM2.M6.BitNode
