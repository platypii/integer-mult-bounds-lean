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

/-- Use fresh owner and scratch tapes while sharing just the splitter's
outer controls. The splitter's payload and inner counters stay outside. -/
def childInputFan {T : ℕ} (live : Fin (142080+2) ↪ Fin T) :
    Fin (142081+2) ↪ Fin (142082+T) :=
  finSumFinEquiv.symm.toEmbedding.trans
    ((Fin.castSuccEmb.sumMap ((Fin.natAddEmb 142080).trans live)).trans finSumFinEquiv.toEmbedding)

theorem childInputFan_owner {T : ℕ} (live : Fin (142080+2) ↪ Fin T) (r : Fin 142081) :
    childInputFan live (r.castAdd 2) = r.castSucc.castAdd T := by
  change finSumFinEquiv (Sum.map Fin.castSucc (fun j : Fin 2 => live (j.natAdd 142080))
    ((@finSumFinEquiv 142081 2).symm (r.castAdd 2))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem childInputFan_control {T : ℕ} (live : Fin (142080+2) ↪ Fin T) (j : Fin 2) :
    childInputFan live (j.natAdd 142081) = (live (j.natAdd 142080)).natAdd 142082 := by
  change finSumFinEquiv (Sum.map Fin.castSucc (fun j : Fin 2 => live (j.natAdd 142080))
    ((@finSumFinEquiv 142081 2).symm (j.natAdd 142081))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem childInputFan_outside {T : ℕ} (live : Fin (142080+2) ↪ Fin T) (t : Fin T)
    (outside : ∀ j : Fin 2, live (j.natAdd 142080) ≠ t) :
    ∀ i, childInputFan live i ≠ t.natAdd 142082 := by
  intro i
  induction i using Fin.addCases with
  | left r =>
    rw [childInputFan_owner]
    intro eq
    have h := congrArg Fin.val eq
    change r.val = 142082+t.val at h
    omega
  | right j =>
    rw [childInputFan_control]
    exact (Fin.natAddEmb 142082).injective.ne (outside j)

/-- Prepare the live rows and execute the child on an adjacent private bank.
Only the owner words and the two volume counters cross the bank boundary. -/
theorem prepareRunChild {P U : Type} {T N Q V price : ℕ} {body : P → Pr P N Q prime U}
    {code src dst seed} {effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop}
    (run : PackedPieceHandoff V effect body code src dst seed price)
    (live : Fin (142080+2) ↪ Fin T) (out : Fin (142081+2) ↪ Fin T) (tmp : Fin T)
    (apart : ∀ (i : Fin 142080) (j : Fin 142081), live (i.castAdd 2) ≠ out (j.castAdd 2))
    (srcTmp : ∀ i : Fin 142080, live (i.castAdd 2) ≠ tmp)
    (dstTmp : ∀ i : Fin 142081, out (i.castAdd 2) ≠ tmp)
    (controls : ∀ j : Fin 2, out (j.natAdd 142081) = live (j.natAdd 142080)) :
    ∃ (bank : Fin N ↪ Fin (T+N)) (host : Empty ⊕ P → Pr (Empty ⊕ P) (T+N) Q prime U) (program : Pr (Empty ⊕ P) (T+N) Q prime U),
    ∀ (data : Fin 142080 → Fin V → ZMod 2) u S,
      HelperFan live data S →
      S.L tmp = [] → S.R tmp = [] →
      (∀ i : Fin 142081, S.L (out (i.castAdd 2)) = [] ∧ S.R (out (i.castAdd 2)) = []) →
      ∃ z F n y, Exec host program (mk u (adjacentStageStacks S seed)) n (mk z F) ∧
        n ≤ 142081*(8*V+10)+1+price ∧ z.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk bank F) ∧
        effect (data ∘ Fin.lastCases 0 id) y ∧
        ∀ j, (∀ i, out i ≠ j) → F.L (j.castAdd N) = S.L j ∧ F.R (j.castAdd N) = S.R j := by
  obtain ⟨prep,prepare⟩ := prepareChildOwners_exec (P := Empty) (U := U) (Q := Q)
    Empty.elim live out tmp apart srcTmp dstTmp
  obtain ⟨bank,_,join⟩ := runAdjacentStages (P := Empty) (R := P) (U := U) (q := Q) (A := prime) out src
  let left := Fin.castAdd N (n := T)
  refine ⟨bank,Sum.elim (fun e : Empty => embProg left Sum.inl (Empty.elim e)) (fun p => embProg bank Sum.inr (body p)),(embProg left Sum.inl prep).seq (embProg bank Sum.inr code),?_⟩
  intro data u S rep tl tr empty
  obtain ⟨v,R,t,loaded,paid,user,words,preparedFrame⟩ := prepare _ (embDn left u) S rep controls tl tr empty
  let row : Fin 142081 → Fin 142080 := Fin.lastCases 0 id
  let post := fun (a : U) (F : Stacks N prime) => a = u.user ∧ ∃ y,
    ParentStageWords (fun i => dst (i.castAdd 2)) dst V y F ∧ effect (data ∘ row) y
  obtain ⟨z,F,n,exec,bill,⟨same,y,returned,reads⟩,childFrame⟩ :=
    join Empty.elim body prep code u S seed v _ t price post loaded (by
      intro a D state shared privateTapes
      obtain ⟨b,G,k,y,exec,bill,hb,returned,reads⟩ := run (data ∘ row) a D (by
        constructor
        · intro i; exact (shared _).1.trans (words.left i)
        · intro i; exact (shared _).2.trans (words.right i)
        · intro j l; rw [(shared _).1,(shared _).2]; exact words.controls j l) privateTapes
      exact ⟨b,G,k,exec,bill,hb.trans (state.trans user),y,returned,reads⟩)
  refine ⟨z,F,n,y,exec,bill.trans (Nat.add_le_add_right paid _),same,returned,reads,?_⟩
  intro j outside
  have keep := childFrame j outside
  exact ⟨keep.1,keep.2.trans (preparedFrame j (fun i => outside (i.castAdd 2)))⟩

/-- Reserve the child input words and copy scratch ahead of the live tapes. -/
noncomputable def childOwnerStacks {T : ℕ} (S : Stacks T prime) : Stacks (142082+T) prime :=
  adjacentStageStacks ⟨S.inp,S.out,fun _ => [],fun _ => []⟩ S

/-- Drop the spare owner from a child output bank, retaining its two counters. -/
def childReturnFan {T : ℕ} (dst : Fin (142081+2) ↪ Fin T) : Fin (142080+2) ↪ Fin T :=
  (finSumFinEquiv.symm.toEmbedding.trans
    ((Fin.castSuccEmb.sumMap (Function.Embedding.refl (Fin 2))).trans finSumFinEquiv.toEmbedding)).trans dst

theorem childReturnFan_owner {T : ℕ} (dst : Fin (142081+2) ↪ Fin T) (r : Fin 142080) :
    childReturnFan dst (r.castAdd 2) = dst (r.castSucc.castAdd 2) := by
  change dst (finSumFinEquiv (Sum.map Fin.castSucc id ((@finSumFinEquiv 142080 2).symm (r.castAdd 2)))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem childReturnFan_control {T : ℕ} (dst : Fin (142081+2) ↪ Fin T) (j : Fin 2) :
    childReturnFan dst (j.natAdd 142080) = dst (j.natAdd 142081) := by
  change dst (finSumFinEquiv (Sum.map Fin.castSucc id ((@finSumFinEquiv 142080 2).symm (j.natAdd 142080)))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem ParentStageWords.returnFan {T N V : ℕ} {dst : Fin (142081+2) ↪ Fin N}
    {bank : Fin N ↪ Fin T} {F : Stacks T prime} {y : Fin 142081 → Fin V → ZMod 2}
    (words : ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk bank F)) :
    HelperFan ((childReturnFan dst).trans bank) (fun r => y r.castSucc) F := by
  intro i z
  induction i using Fin.addCases with
  | left r =>
    have encoded : SparseRoleCircuit.encoded (a := prime) (fun r : Fin 142080 => y r.castSucc) r =
        SparseRoleCircuit.encoded y r.castSucc := rfl
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,embStk,
      Function.comp_apply,Function.Embedding.trans_apply,childReturnFan_owner,encoded] using
      words.helperFan (r.castSucc.castAdd 2) z
  | right j =>
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,embStk,
      Function.comp_apply,Function.Embedding.trans_apply,childReturnFan_control] using
      words.helperFan (j.natAdd 142081) z

open Cover.Fallback in
/-- A returned owner supplies the payload field of the unpacker's record.
The other record registers may be reused from the incoming packing pass. -/
theorem HelperFan.unpackRecord {T B w W : ℕ} {fan : Fin (142080+2) ↪ Fin T}
    {saved : Fin 35 ↪ Fin B} {bank : Fin 35 ↪ Fin T} {x : Fin 142080 → Fin ((prime^(w+1))^128*W) → ZMod 2}
    {S : Stacks B prime} {F : Stacks T prime} (returned : HelperFan fan x F) (r : Fin 142080)
    (shared : bank 24 = fan (r.castAdd 2)) {record dest q original}
    (start : RecordReady (b := prime) (w := w) (d := 128) (W := W) saved
      (prime^(w+1)).size W.size record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original S)
    (keep : ∀ i : Fin 35, i ≠ 24 → F.L (bank i) = S.L (saved i) ∧ F.R (bank i) = S.R (saved i)) :
    RecordReady (b := prime) (w := w) (d := 128) (W := W) bank
      (prime^(w+1)).size W.size record SparseRoleCircuit.encode (fun _ => blank) dest 0 q (x r) F := by
  apply start.returnPayload keep
  intro z
  rw [shared]
  simpa only [List.map_ofFn] using (fanPayload returned r z).symm

/-- Recover the input layout of the split child after an enclosing pass has
updated the live tapes. The fresh owner registers and the child's private
seed suffice, and the live projection carries the current input and output stacks. -/
theorem splitChildStacks_eq {T N : ℕ} (D : Stacks (142082+T+N) prime) (seed : Stacks N prime)
    (empty : ∀ i : Fin 142082, let j := (i.castAdd T).castAdd N
      D.L j = [] ∧ D.R j = [])
    (privateTapes : ∀ i : Fin N, let j := i.natAdd (142082+T)
      D.L j = seed.L i ∧ D.R j = seed.R i) :
    let live := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    D = adjacentStageStacks (childOwnerStacks (embStk live D)) seed := by
  intro live
  cases D with
  | mk inp out L R =>
    congr 1
    all_goals
      funext j
      induction j using Fin.addCases with
      | left j =>
        induction j using Fin.addCases with
        | left i =>
          simp only [adjacentStageStacks,childOwnerStacks,Fin.addCases_left]
          first | exact (empty i).1 | exact (empty i).2
        | right i => simp [adjacentStageStacks,childOwnerStacks,embStk,live]
      | right i =>
        simp only [adjacentStageStacks,Fin.addCases_right]
        first | exact (privateTapes i).1 | exact (privateTapes i).2

theorem runSplitOwners {P U : Type} {T N Q V price : ℕ} {body : P → Pr P N Q prime U}
    {code src dst seed} {effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop}
    (run : PackedPieceHandoff V effect body code src dst seed price)
    (live : Fin (142080+2) ↪ Fin T) :
    let H := 142082+T+N
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    ∃ (bank : Fin N ↪ Fin H) (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U)
      (program : Pr (Empty ⊕ P) H Q prime U),
    ∀ (data : Fin 142080 → Fin V → ZMod 2) u S,
      HelperFan (live.trans caller) data S →
      (∀ i : Fin 142082, let j := (i.castAdd T).castAdd N
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin N, let j := i.natAdd (142082+T)
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      ∃ z F n, ∃ y : Fin 142081 → Fin V → ZMod 2, Exec host program (mk u S) n (mk z F) ∧
        n ≤ 142081*(8*V+10)+1+price ∧ z.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk bank F) ∧
        effect (data ∘ Fin.lastCases 0 id) y ∧
        HelperFan ((childReturnFan dst).trans bank) (fun r => y r.castSucc) F ∧
        ∀ j, (∀ i : Fin 2, live (i.natAdd 142080) ≠ j) →
          let t := (j.natAdd 142082).castAdd N
          F.L t = S.L t ∧ F.R t = S.R t := by
  intro H caller
  let raised := live.trans (Fin.natAddEmb 142082)
  let tmp := (Fin.last 142081).castAdd T
  have separate (i : Fin T) (j : Fin 142082) : i.natAdd 142082 ≠ j.castAdd T := by
    intro eq
    have h := congrArg Fin.val eq
    change 142082+i.val = j.val at h
    omega
  obtain ⟨bank,host,program,exec⟩ := prepareRunChild run raised (childInputFan live) tmp
    (fun i j => by rw [childInputFan_owner]; exact separate _ _) (fun _ => separate _ _)
    (fun j => by rw [childInputFan_owner]; exact (Fin.castAddEmb T).injective.ne (Fin.castSucc_ne_last j))
    (childInputFan_control live)
  refine ⟨bank,host,program,?_⟩
  intro data u D rep empty privateTapes
  let S := embStk caller D
  have shape := splitChildStacks_eq D seed empty privateTapes
  have projected : HelperFan live data S := rep
  have placed : HelperFan raised data (childOwnerStacks S) := by
    intro i z
    simpa [raised,embStk,childOwnerStacks,adjacentStageStacks,Function.comp_def] using projected i z
  obtain ⟨z,F,n,y,ran,paid,user,words,reads,keep⟩ := exec data u (childOwnerStacks S)
    placed (by simp [tmp,childOwnerStacks,adjacentStageStacks]) (by simp [tmp,childOwnerStacks,adjacentStageStacks])
    (fun i => by simp [childInputFan_owner,childOwnerStacks,adjacentStageStacks])
  refine ⟨z,F,n,y,?_,paid,user,words,reads,words.returnFan,?_⟩
  · rw [shape]
    exact ran
  intro j outside
  simpa [childOwnerStacks,adjacentStageStacks,S,caller,embStk] using keep _ (childInputFan_outside live j outside)

theorem runSplitChild {P U : Type} {T N Q V w price : ℕ} {body : P → Pr P N Q prime U}
    {code src dst seed} (run : PackedPieceHandoff V (packedChildOutput w V) body code src dst seed price)
    (live : Fin (142080+2) ↪ Fin T) :
    let H := 142082+T+N
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    ∃ (bank : Fin N ↪ Fin H) (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U)
      (program : Pr (Empty ⊕ P) H Q prime U),
    ∀ (lane : Descriptor) (_width : lane.width = 64*w) (size : volume prime lane = V)
      (data : Fin 142080 → Fin (volume prime lane) → ZMod 2) u S,
      let position := packedChildPosition lane size
      HelperFan (live.trans caller) (fun r => data r ∘ position.symm) S →
      (∀ i : Fin 142082, let j := (i.castAdd T).castAdd N
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin N, let j := i.natAdd (142082+T)
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      ∃ z F n, ∃ y : Fin 142081 → Fin V → ZMod 2, Exec host program (mk u S) n (mk z F) ∧
        n ≤ 142081*(8*V+10)+1+price ∧ z.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk bank F) ∧
        HelperFan ((childReturnFan dst).trans bank) (fun r =>
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r) ∘ position.symm) F ∧
        ∀ j, (∀ i : Fin 2, live (i.natAdd 142080) ≠ j) →
          let t := (j.natAdd 142082).castAdd N
          F.L t = S.L t ∧ F.R t = S.R t := by
  intro H caller
  obtain ⟨bank,host,program,exec⟩ := runSplitOwners run live
  refine ⟨bank,host,program,?_⟩
  intro lane width size data u S position rep empty privateTapes
  obtain ⟨z,F,n,y,ran,paid,user,words,reads,owners,keep⟩ :=
    exec _ u S rep empty privateTapes
  refine ⟨z,F,n,y,ran,paid,user,words,?_,keep⟩
  have rows : (fun r : Fin 142080 => y r.castSucc) = fun r =>
      Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r) ∘ position.symm := by
    funext r i
    have read := congrFun (reads r lane width size) (position.symm i)
    simpa [position,Function.comp_def] using read
  exact rows ▸ owners

/-- Supply the live owner rows in inherited order and return their transposes
on the child output tapes. Only the linear owner-copy preparation is charged. -/
theorem runInheritedChild {P U : Type} {T N Q price : ℕ} (lane : Descriptor) {body : P → Pr P N Q prime U}
    {code src dst seed} (run : PackedPieceHandoff (volume prime lane) (fun x y =>
      ∀ r : Fin 142080, y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc))
      body code src dst seed price)
    (live : Fin (142080+2) ↪ Fin T) :
    let H := 142082+T+N
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    ∃ (bank : Fin N ↪ Fin H) (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U)
      (program : Pr (Empty ⊕ P) H Q prime U),
    let V := volume prime lane
    ∀ (data : Fin 142080 → Fin (volume prime lane) → ZMod 2) u S,
      HelperFan (live.trans caller) data S →
      (∀ i : Fin 142082, let j := (i.castAdd T).castAdd N
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin N, let j := i.natAdd (142082+T)
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      ∃ z F n, ∃ y : Fin 142081 → Fin V → ZMod 2, Exec host program (mk u S) n (mk z F) ∧
        n ≤ 142081*(8*V+10)+1+price ∧ z.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk bank F) ∧
        HelperFan ((childReturnFan dst).trans bank) (fun r =>
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)) F ∧
        ∀ j, (∀ i : Fin 2, live (i.natAdd 142080) ≠ j) →
          let t := (j.natAdd 142082).castAdd N
          F.L t = S.L t ∧ F.R t = S.R t := by
  intro H caller
  obtain ⟨bank,host,program,exec⟩ := runSplitOwners run live
  refine ⟨bank,host,program,?_⟩
  intro V data u S rep empty privateTapes
  obtain ⟨z,F,n,y,ran,paid,user,words,reads,owners,keep⟩ :=
    exec data u S rep empty privateTapes
  refine ⟨z,F,n,y,ran,paid,user,words,?_,keep⟩
  have eq : (fun r : Fin 142080 => y r.castSucc) = fun r =>
      Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r) := by
    funext r
    simpa only [Function.comp_apply, Fin.lastCases_castSucc, id_eq] using reads r
  exact eq ▸ owners

/-- Sweeps and idle windows on exact flat words compose to interchange the two
parent fields on every role. The spectator and the two piece-cost sums are preserved. -/
theorem assembledFlatNode {U : Type} :
    ∃ states : ℕ, ∀ {Q w W V : ℕ}, states ≤ Q → (size : (prime^w)^128*W = V) → 0 < V → ∀ place : Fin V ≃ Fin V,
      let address := fun (j : Fin W) s => place ((flatWindowEquiv w W (s,j)).cast size)
      let reads := fun (piece : Piece) (x y : Fin 142081 → Fin V → ZMod 2) =>
        ∀ j, let addr := fun z => address j (windowState w z)
          readRoles addr y = piece.run (readRoles addr x)
      ∀ (sweepCost idleCost : Fin 9 → ℕ),
      (∀ n, ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst seed,
        PackedPieceHandoff V (reads (.stage n)) body code src dst seed (sweepCost n)) →
      (∀ n, ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst seed,
        PackedPieceHandoff V (reads (.remainder n.val)) body code src dst seed (idleCost n)) →
      ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst seed,
        PackedPieceHandoff V (fun x y => packedChildOutput w V (fun r => x r ∘ place) (fun r => y r ∘ place)) body code src dst seed
          ((∑ i, sweepCost i)+(∑ i, idleCost i)+9*(2*(76*17760*V*(142081+7)+6)+1+(142081*(8*V+10)+1))+2) := by
  obtain ⟨states,build⟩ := assembledPackedNode (U := U)
  refine ⟨states,?_⟩
  intro Q w W V fits size pos place address reads sweepCost idleCost sweeps windows
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
  change ∀ k, (y (sweepRoleTape r) ∘ place) _ = _
  apply (flatNodeOutput_iff size child width (packedChildPosition child childSize) (fun _ => rfl) _ _).2
  intro i
  obtain ⟨⟨s,j⟩,rfl⟩ := (flatWindowEquiv w W).surjective i
  have swapped := modularEndpoint r (fun _ => address j) x y
    (nodePieceEffect_read _ (fun n a d h => h j) (fun n a d h => h j) trace) s
  have transposed := flatNodeTranspose (fun k => x (sweepRoleTape r) (place (k.cast size)))
    (s.1 ∘ stageAxis.symm) (s.2 ∘ stageAxis.symm) j
  rw [flatWindowEquiv_fields]
  exact (by simpa only [address,flatWindowEquiv_fields,sweepRoleTape_eq] using swapped :
    y (sweepRoleTape r) _ = x (sweepRoleTape r) _).trans transposed.symm

/-- If each sweep and remainder reads the inherited cells, the assembled node
transposes the physical owner words in place in that address order. -/
theorem assembledInheritedNode {U : Type} :
    ∃ states : ℕ, ∀ {Q w W : ℕ} (child : Descriptor), states ≤ Q → child.width = 64*w →
      (size : (prime^w)^128*W = volume prime child) → 0 < volume prime child →
      let V := volume prime child
      let position := packedChildPosition child rfl
      let address := fun (j : Fin W) s => position.symm ((flatWindowEquiv w W (s,j)).cast size)
      let reads := fun (piece : Piece) (x y : Fin 142081 → Fin V → ZMod 2) =>
        ∀ j, let addr := fun z => address j (windowState w z)
          readRoles addr y = piece.run (readRoles addr x)
      ∀ (sweepCost idleCost : Fin 9 → ℕ),
      (∀ n, ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst seed,
        PackedPieceHandoff V (reads (.stage n)) body code src dst seed (sweepCost n)) →
      (∀ n, ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst seed,
        PackedPieceHandoff V (reads (.remainder n.val)) body code src dst seed (idleCost n)) →
      ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst seed,
        PackedPieceHandoff V (fun x y => ∀ r : Fin 142080, y r.castSucc =
          Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x r.castSucc)) body code src dst seed
          ((∑ i, sweepCost i)+(∑ i, idleCost i)+9*(2*(76*17760*V*(142081+7)+6)+1+(142081*(8*V+10)+1))+2) := by
  obtain ⟨states,assemble⟩ := assembledFlatNode (U := U)
  refine ⟨states,?_⟩
  intro Q w W child fits width size positive V position address reads sweepCost idleCost sweeps windows
  obtain ⟨P,T,body,code,src,dst,seed,run⟩ :=
    assemble fits size positive position.symm sweepCost idleCost sweeps windows
  refine ⟨P,T,body,code,src,dst,seed,?_⟩
  intro x u S words privateTapes
  obtain ⟨z,F,k,y,exec,paid,user,out,changed⟩ := run x u S words privateTapes
  refine ⟨z,F,k,y,exec,paid,user,out,?_⟩
  intro r
  simpa only [position,Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id] using
    changed r child width rfl

end IntegerMultBounds.MathlibTM2.M6.BitNode
