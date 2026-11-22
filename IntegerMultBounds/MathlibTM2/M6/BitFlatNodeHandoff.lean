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

/-- Address a packed child by its physical tape volume. -/
noncomputable def packedChildPosition {V : ℕ} (child : Descriptor) (size : volume prime child = V) :
    Fin (volume prime child) ≃ Fin V :=
  (CopyChildLayout.packActive child).trans (finCongr (by
    have card := Fintype.card_congr (CopyChildLayout.packActive child)
    simp only [Fintype.card_fin] at card
    exact card.symm.trans size))

/-- On a packed tape, the flat node's output equation is exactly the
scheduled child's transpose in its original descriptor order. -/
theorem flatNodeOutput_iff {w W V : ℕ} (size : (prime^w)^128*W = V)
    (child : Descriptor) (width : child.width = 64*w)
    (position : Fin (volume prime child) ≃ Fin V)
    (packed : ∀ i, (position i).val = (CopyChildLayout.packActive child i).val)
    {α : Type} (word changed : Fin V → α) :
    (∀ k, changed (position k) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows)
      (word ∘ position) k) ↔ ∀ i : Fin ((prime^w)^128*W),
      changed (i.cast size) = Shared50RecursiveNodeRows.transpose
        (one_dvd (flatNodeDescriptor w W).rows)
        (fun k => word (k.cast ((flatNodeVolume w W).trans size)))
        (i.cast (flatNodeVolume w W).symm) := by
  have coords : InheritedIntervalPositions child (flatNodeDescriptor w W)
      ((flatNodeVolume w W).trans size) position := fun k =>
    (packed k).symm.trans (packActive_flatNode w W ((position k).cast ((flatNodeVolume w W).trans size).symm)).symm
  rw [coords.transpose_iff width.symm]
  constructor
  · intro result i
    exact congrFun result (i.cast size)
  · intro result
    funext i
    exact result (i.cast size.symm)

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

/-- Copy the live owner rows into the child input bank.  Its spare tape
receives another copy of row zero, so it also starts with a full-length word. -/
theorem prepareChildOwners_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (live : Fin (142080+2) ↪ Fin T) (dst : Fin (142081+2) ↪ Fin T) (tmp : Fin T)
    (apart : ∀ (i : Fin 142080) (j : Fin 142081), live (i.castAdd 2) ≠ dst (j.castAdd 2))
    (srcTmp : ∀ i : Fin 142080, live (i.castAdd 2) ≠ tmp)
    (dstTmp : ∀ i : Fin 142081, dst (i.castAdd 2) ≠ tmp) :
    let row : Fin 142081 → Fin 142080 := Fin.lastCases 0 id
    ∃ code, ∀ {V : ℕ} (data : Fin 142080 → Fin V → ZMod 2) u S,
      HelperFan live data S → (∀ j : Fin 2, dst (j.natAdd 142081) = live (j.natAdd 142080)) →
      S.L tmp = [] → S.R tmp = [] →
      (∀ i : Fin 142081, S.L (dst (i.castAdd 2)) = [] ∧ S.R (dst (i.castAdd 2)) = []) →
      ∃ z R n, Exec body code (mk u S) n (mk z {S with R := R}) ∧
        n ≤ 142081*(8*V+10)+1 ∧ z.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst V (data ∘ row) {S with R := R} ∧
        ∀ j, (∀ i : Fin 142081, dst (i.castAdd 2) ≠ j) → R j = S.R j := by
  intro row
  let dest := (Fin.castAddEmb 2 (n := 142081)).trans dst
  let src := fun i => live ((row i).castAdd 2)
  let copy : Fin 142081 → Pr P T Q prime U := fun i => loadCompactWord (src i) tmp (dest i)
  refine ⟨Cover.LabelTraversal.sequence copy (List.finRange 142081),?_⟩
  intro V data u S rep controls left right empty
  obtain ⟨z,R,n,user,paid,exec,written,off⟩ := distinctTapeSequence body dest copy (List.finRange 142081)
    (List.nodup_finRange _) (fun _ => []) (fun i => List.ofFn fun a => SparseRoleCircuit.encode (data (row i) a))
    (fun _ => 8*V+10) u S (fun i => (empty i).2) (by
      intro i v F same vacant keep
      have ready : WordAtZero (data (row i)) (F.L (src i)) (F.R (src i)) := by
        intro j
        rw [same,keep _ (fun a => (apart (row i) a).symm)]
        simpa only [src,encodedOwnerCell,sub_zero] using fanPayload rep (row i) j
      have h₁ : src i ≠ tmp := srcTmp _
      have h₂ : src i ≠ dest i := apart _ _
      have h₃ : tmp ≠ dest i := (dstTmp _).symm
      obtain ⟨y,hy,run⟩ := loadCompactWord_exec body (src i) tmp (dest i)
        (by simp [List.nodup_cons,h₁,h₂,h₃]) _ v F ready
        (same ▸ left) ((keep _ dstTmp).trans right)
      exact ⟨y,_,hy,le_rfl,by simpa only [vacant,List.append_nil,copy] using run⟩)
  have frame j (outside : ∀ i, dest i ≠ j) := off j (fun i _ => outside i)
  refine ⟨z,R,n,exec,by simpa only [List.map_const',List.sum_replicate_nat,List.length_finRange] using paid,
    user,⟨fun i => (empty i).1,fun i => written i (List.mem_finRange i),?_⟩,frame⟩
  intro j t
  have keep := frame (dst (j.natAdd 142081)) (fun i => dst.injective.ne (by
    intro eq; have h := congrArg Fin.val eq; change i.val = 142081+j.val at h; omega))
  change _ = readAt blank _ (R _) _
  rw [keep,controls]
  simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,CountedLoopReuseAlphabet.controls,
    ite_self,embStk,Function.comp_apply] using rep (j.natAdd 142080) t

def packedChildOutput (w V : ℕ) (x y : Fin 142081 → Fin V → ZMod 2) : Prop :=
  ∀ (r : Fin 142080) (child : Descriptor), child.width = 64*w →
    ∀ size : volume prime child = V, let position := packedChildPosition child size
      y r.castSucc ∘ position = Shared50RecursiveNodeRows.transpose (one_dvd child.rows)
        (x r.castSucc ∘ position)

/-- Apply the assembled program to packed owner rows and read each returned
row in the inherited order consumed by the cyclic merger. -/
theorem runPackedChild {P U : Type} {T Q V w price : ℕ} {body : P → Pr P T Q prime U}
    {code src dst seed} (run : PackedPieceHandoff V (packedChildOutput w V) body code src dst seed price)
    (lane : Descriptor) (width : lane.width = 64*w) (size : volume prime lane = V)
    (data : Fin 142081 → Fin (volume prime lane) → ZMod 2) :
    let position := packedChildPosition lane size
    ∀ u S, ParentStageWords (fun i => src (i.castAdd 2)) src V (fun r => data r ∘ position.symm) S →
      (∀ j, (∀ i, src i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
      ∃ z F n y, Exec body code (mk u S) n (mk z F) ∧ n ≤ price ∧ z.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst V y F ∧
        ∀ r : Fin 142080, y r.castSucc ∘ position =
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r.castSucc) := by
  intro position u S words ready
  obtain ⟨z,F,n,y,exec,paid,user,out,effect⟩ := run _ u S words ready
  refine ⟨z,F,n,y,exec,paid,user,out,?_⟩
  intro r
  simpa [position,Function.comp_def] using effect r lane width size

/-- Prepare the live rows and execute the child on an adjacent private bank.
Only the owner words and the two volume counters cross the bank boundary. -/
theorem prepareRunPackedChild {P U : Type} {T N Q V w price : ℕ} {body : P → Pr P N Q prime U}
    {code src dst seed} (run : PackedPieceHandoff V (packedChildOutput w V) body code src dst seed price)
    (live : Fin (142080+2) ↪ Fin T) (out : Fin (142081+2) ↪ Fin T) (tmp : Fin T)
    (apart : ∀ (i : Fin 142080) (j : Fin 142081), live (i.castAdd 2) ≠ out (j.castAdd 2))
    (srcTmp : ∀ i : Fin 142080, live (i.castAdd 2) ≠ tmp)
    (dstTmp : ∀ i : Fin 142081, out (i.castAdd 2) ≠ tmp)
    (controls : ∀ j : Fin 2, out (j.natAdd 142081) = live (j.natAdd 142080)) :
    ∃ (bank : Fin N ↪ Fin (T+N)) (host : Empty ⊕ P → Pr (Empty ⊕ P) (T+N) Q prime U) (program : Pr (Empty ⊕ P) (T+N) Q prime U),
    ∀ (lane : Descriptor) (_width : lane.width = 64*w) (size : volume prime lane = V)
      (data : Fin 142080 → Fin (volume prime lane) → ZMod 2) u S,
      let position := packedChildPosition lane size
      HelperFan live (fun r => data r ∘ position.symm) S →
      S.L tmp = [] → S.R tmp = [] →
      (∀ i : Fin 142081, S.L (out (i.castAdd 2)) = [] ∧ S.R (out (i.castAdd 2)) = []) →
      ∃ z F n y, Exec host program (mk u (adjacentStageStacks S seed)) n (mk z F) ∧
        n ≤ 142081*(8*V+10)+1+price ∧ z.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk bank F) ∧
        ∀ r : Fin 142080, y r.castSucc ∘ position =
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r) := by
  obtain ⟨prep,prepare⟩ := prepareChildOwners_exec (P := Empty) (U := U) (Q := Q)
    Empty.elim live out tmp apart srcTmp dstTmp
  obtain ⟨bank,_,join⟩ := runAdjacentStages (P := Empty) (R := P) (U := U) (q := Q) (A := prime) out src
  let left := Fin.castAdd N (n := T)
  refine ⟨bank,Sum.elim (fun e : Empty => embProg left Sum.inl (Empty.elim e)) (fun p => embProg bank Sum.inr (body p)),(embProg left Sum.inl prep).seq (embProg bank Sum.inr code),?_⟩
  intro lane width size data u S position rep tl tr empty
  obtain ⟨v,R,t,loaded,paid,user,words,_⟩ := prepare _ (embDn left u) S rep controls tl tr empty
  let row : Fin 142081 → Fin 142080 := Fin.lastCases 0 id
  let post := fun (a : U) (F : Stacks N prime) => a = u.user ∧ ∃ y,
    ParentStageWords (fun i => dst (i.castAdd 2)) dst V y F ∧ ∀ r : Fin 142080,
      y r.castSucc ∘ position = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)
  obtain ⟨z,F,n,exec,bill,⟨same,y,returned,reads⟩,_⟩ :=
    join Empty.elim body prep code u S seed v _ t price post loaded (by
      intro a D state shared privateTapes
      obtain ⟨b,G,k,y,exec,bill,hb,returned,reads⟩ := runPackedChild run lane width size (data ∘ row) a D (by
        constructor
        · intro i; exact (shared _).1.trans (words.left i)
        · intro i; exact (shared _).2.trans (words.right i)
        · intro j l; rw [(shared _).1,(shared _).2]; exact words.controls j l) privateTapes
      exact ⟨b,G,k,exec,bill,hb.trans (state.trans user),y,returned,fun r => by
        simpa only [Function.comp_apply,row,Fin.lastCases_castSucc,id_eq,position] using reads r⟩)
  exact ⟨z,F,n,y,exec,bill.trans (Nat.add_le_add_right paid _),same,returned,reads⟩

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
        PackedPieceHandoff V (packedChildOutput w V) body code src dst seed
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
  intro lane child width childSize
  let roles := (Fintype.equivFin Role).trans (finCongr card_role)
  obtain ⟨r,rfl⟩ := roles.surjective lane
  apply funext
  change ∀ k, y (sweepRoleTape r) _ = _
  apply (flatNodeOutput_iff size child width (packedChildPosition child childSize) (fun _ => rfl) _ _).2
  intro i
  obtain ⟨⟨s,j⟩,rfl⟩ := (flatWindowEquiv w W).surjective i
  have swapped := modularEndpoint r (fun _ => address j) x y
    (nodePieceEffect_read _ (fun n a d h => h j) (fun n a d h => h j) trace) s
  have transposed := flatNodeTranspose (fun k => x (sweepRoleTape r) (k.cast size))
    (s.1 ∘ stageAxis.symm) (s.2 ∘ stageAxis.symm) j
  rw [flatWindowEquiv_fields]
  exact (by simpa only [address,flatWindowEquiv_fields,sweepRoleTape_eq] using swapped :
    y (sweepRoleTape r) _ = x (sweepRoleTape r) _).trans transposed.symm

end IntegerMultBounds.MathlibTM2.M6.BitNode
