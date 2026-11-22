module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedPhysicalStage
public import IntegerMultBounds.MathlibTM2.M6.BitStagePlacement

/-! Share the previous sweep's destination tapes and its two chart counters
with the next physical stage, leaving all other tapes private. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host SweepFile
open Shared50ModularControl (prime)

/-- Sequence the packed stage with a continuation on its own tape bank.
The continuation sees its original private stacks and all returned parent words. -/
theorem runAfterPackedStage {T N Q V D : ℕ} {P R U : Type}
    (fan : Fin (142081+2) ↪ Fin T) (input : Fin (142081+2) ↪ Fin N) :
    let m := Exit.size 0 T
    ∃ bank : Fin N ↪ Fin (m+N), ∀ (left : P → Pr P m Q prime U) (right : R → Pr R N Q prime U) a b,
    let leftBank := Fin.castAdd N (n := m)
    let body := Sum.elim (fun g => embProg leftBank Sum.inl (left g)) (fun g => embProg bank Sum.inr (right g))
    ∀ u L seed v F t budget (x : Fin 142081 → Fin D → ZMod 2) (post : U → Stacks N prime → Prop),
      Exec left a (mk (embDn leftBank u) L) t (mk v F) →
      ParentStageWords (fun i => Exit.sweep 0 T (owners i)) (fan.trans (Exit.chart 0 T)) V x F →
      (∀ w S, w.user = v.user → ParentStageWords (fun i => input (i.castAdd 2)) input V x S →
        (∀ j, (∀ i, input i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
        ∃ z G k, Exec right b (mk w S) k (mk z G) ∧ k ≤ budget ∧ post z.user G) →
      ∃ z G k, Exec body ((embProg leftBank Sum.inl a).seq (embProg bank Sum.inr b))
        (mk u (adjacentStageStacks L seed)) k (mk z G) ∧ k ≤ t+budget ∧ post z.user (embStk bank G) := by
  intro m
  obtain ⟨bank,_,sequence⟩ := runAdjacentStages (A := prime) (P := P) (R := R) (U := U) (q := Q) (returnedFan fan) input
  refine ⟨bank,?_⟩
  intro left right a b leftBank body u L seed v F t budget x post exec words next
  obtain ⟨z,G,k,ran,paid,done,_⟩ := sequence left right a b u L seed v F t budget post exec (by
    intro w S user shared privateTapes
    apply next w S user _ privateTapes
    constructor
    · intro i
      rw [(shared (i.castAdd 2)).1,returnedFan_owner]; exact words.left i
    · intro i
      rw [(shared (i.castAdd 2)).2,returnedFan_owner]; exact words.right i
    · intro j z
      rw [(shared (j.natAdd 142081)).1,(shared (j.natAdd 142081)).2]
      rw [returnedFan_counter]; exact words.controls j z)
  exact ⟨z,G,k,ran,paid,done⟩

/-- Copy a represented result to fresh owner words, keeping the two live
counters on the chart. The cost includes every owner and the spare. -/
theorem packedResultWords_exec {P U : Type} {T Q : ℕ} (localFan : Fin (142081+2) ↪ Fin T)
    (body : P → Pr P (Exit.size 0 T) Q prime U) :
    let fan := localFan.trans (Exit.chart 0 T)
    let dst := returnedFan localFan
    let tmp := Exit.tmp 0 T
    ∃ code, ∀ {V : ℕ} (x : Fin 142081 → Fin V → ZMod 2) u S,
      HelperFan fan x S → S.L tmp = [] → S.R tmp = [] →
      (∀ i : Fin 142081, S.L (dst (i.castAdd 2)) = [] ∧ S.R (dst (i.castAdd 2)) = []) →
      ∃ z G k, Exec body code (mk u S) k (mk z G) ∧ k ≤ 142081*(8*V+10)+1 ∧
        z.user = u.user ∧ ParentStageWords (fun i => dst (i.castAdd 2)) dst V x G := by
  intro fan dst tmp
  let source := (Fin.castAddEmb 2).trans fan
  let dest := (Fin.castAddEmb 2).trans dst
  let e := Fintype.equivFin (Exit.Register 0 T)
  have apart i j : source i ≠ dest j := by
    change fan (i.castAdd 2) ≠ returnedFan localFan (j.castAdd 2)
    rw [returnedFan_owner]
    exact e.injective.ne (by intro h; cases h)
  have dt i : dest i ≠ tmp := by
    change returnedFan localFan (i.castAdd 2) ≠ tmp
    rw [returnedFan_owner]
    exact e.injective.ne (by intro h; cases h)
  obtain ⟨code,copy⟩ := materializeOwners_exec body source dest tmp apart
    (fun i => e.injective.ne (by intro h; cases h)) dt
  refine ⟨code,?_⟩
  intro V x u S live tl tr empty
  obtain ⟨z,R,k,run,paid,user,words,off⟩ := copy x u S (by
    intro i j
    have h := fanPayload live i j
    rw [encodedOwnerCell,sub_zero] at h
    simpa only [source,Function.Embedding.trans_apply,Fin.castAddEmb_apply,phaseOwners,embStk,
      Function.comp_apply,sub_zero] using h.symm) tl tr (fun i => (empty i).2)
  refine ⟨z,_,k,run,paid,user,fun i => (empty i).1,words,?_⟩
  intro j z
  have keep := off (dst (j.natAdd 142081)) (fun i => dst.injective.ne (by
    intro eq; have h := congrArg Fin.val eq; change i.val = 142081+j.val at h; omega))
  change _ = readAt blank (S.L _) (R _) _
  rw [keep,show dst (j.natAdd 142081) = fan (j.natAdd 142081) from returnedFan_counter localFan j]
  simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,CountedLoopReuseAlphabet.controls,
    ite_self,embStk,Function.comp_apply] using live (j.natAdd 142081) z

theorem ParentStageWords.helperFan {T V : ℕ} {fan : Fin (142081+2) ↪ Fin T}
    {x : Fin 142081 → Fin V → ZMod 2} {S : Stacks T prime}
    (words : ParentStageWords (fun i => fan (i.castAdd 2)) fan V x S) : HelperFan fan x S := by
  intro i
  induction i using Fin.addCases with
  | left i =>
    intro j
    simp only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply]
    change putWord _ 0 (List.ofFn fun l => SparseRoleCircuit.encode (x i l)) j = readAt blank _ _ (j-0)
    rw [words.left i,words.right i,sub_zero,readAt_nil_left,putWord_blank_zero]
  | right j =>
    intro z
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,CountedLoopReuseAlphabet.controls,
      ite_self,embStk,Function.comp_apply] using words.controls j z

/-- Execute a scheduled bridge and materialize the entire output bank. -/
theorem packedBridgeHandoff (d s : ℕ) (scheduled : Piece.bridge d s ∈ nodeProgram) :
    ∃ states : ℕ, ∀ {q V : ℕ} {U : Type}, states ≤ q → 0 < V →
      ∃ (t : ℕ) (code : Pr Empty t q prime U), ∃ src dst prepared,
        PackedPieceHandoff V (fun x y => y = fun j z => bridgeColumn d s (fun l => x l z) j)
          Empty.elim code src dst prepared (2*(76*17760*V*(142081+7)+6)+1 + (142081*(8*V+10)+1)) := by
  obtain ⟨states,bridge⟩ := bridgeColumns_exec d s scheduled
  refine ⟨states,?_⟩
  intro q V U room pos
  let idFan := Function.Embedding.refl (Fin (142081+2))
  let fan := idFan.trans (Exit.chart 0 (142081+2))
  let dst := returnedFan idFan
  let tmp := Exit.tmp 0 (142081+2)
  let body : Empty → Pr Empty (Exit.size 0 (142081+2)) q prime U := Empty.elim
  obtain ⟨code,run⟩ := bridge fan body room
  obtain ⟨copy,materialize⟩ := packedResultWords_exec idFan body
  refine ⟨_,code.seq copy,fan,dst,⟨[],[],fun _ => [],fun _ => []⟩,?_⟩
  intro x u S words fresh
  have live := words.helperFan
  obtain ⟨v,D,k,ran,bill,user,ready,off⟩ := run pos x u S live
  have blank j (outside : ∀ i, fan i ≠ j) : D.L j = [] ∧ D.R j = [] :=
    ⟨(off j outside).1.trans (fresh j outside).1,(off j outside).2.trans (fresh j outside).2⟩
  let e := Fintype.equivFin (Exit.Register 0 (142081+2))
  have scratch := blank tmp (fun i => e.injective.ne (by intro h; cases h))
  obtain ⟨z,G,l,copied,paid,same,result⟩ := materialize _ v D ready scratch.1 scratch.2 (by
    intro i
    rw [returnedFan_owner]
    exact blank _ (fun j => e.injective.ne (by intro h; cases h)))
  exact ⟨z,G,k+l,_,Exec.seq ran copied,Nat.add_le_add bill paid,same.trans user,result,rfl⟩

/-- Chain physical pieces in execution order and sum their individual budgets. -/
theorem packedHandoffList {Job U : Type} {q : ℕ} (V : ℕ)
    (effect : Job → (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop)
    (price : Job → ℕ) (stages : List Job) (last : Job)
    (available : ∀ i ∈ stages++[last], ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PackedPieceHandoff V (effect i) body code src dst prepared (price i)) :
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PackedPieceHandoff V (fun x y => (stages++[last]).foldr
        (fun i cont a => ∃ b, effect i a b ∧ cont b) (fun a => a = y) x)
        body code src dst prepared ((stages++[last]).map price).sum := by
  induction stages with
  | nil =>
    obtain ⟨P,t,body,code,src,dst,D,run⟩ := available last (by simp)
    refine ⟨P,t,body,code,src,dst,D,?_⟩
    intro x u S live frame
    obtain ⟨z,F,steps,y,ran,cost,user,rep,trace⟩ := run x u S live frame
    exact ⟨z,F,steps,_,ran,by simpa using cost,user,rep,y,trace,rfl⟩
  | cons i stages ih =>
    obtain ⟨P,m,left,a,src,mid,L,firstRun⟩ := available i (by simp)
    obtain ⟨R,n,right,b,input,dst,D,nextRun⟩ := ih (fun j hj => available j (List.mem_cons_of_mem _ hj))
    obtain ⟨bank,_,compose⟩ := runAdjacentStages (P := P) (R := R) (U := U) (q := q)
      (A := prime) mid input
    let front := Fin.castAddEmb n (n := m)
    refine ⟨P ⊕ R,m+n,Sum.elim (fun g => embProg front Sum.inl (left g)) (fun g => embProg bank Sum.inr (right g)),
      (embProg front Sum.inl a).seq (embProg bank Sum.inr b),src.trans front,dst.trans bank,adjacentStageStacks L D,?_⟩
    intro x u S live frame
    have priv (j : Fin m) (off : ∀ h, src h ≠ j) := frame (front j)
      (fun h eq => off h (front.injective eq))
    obtain ⟨v,C,t,y,ran,paid,same,ready,trace⟩ :=
      firstRun x (embDn front u) (embStk front S) ⟨live.left,live.right,live.controls⟩ (fun j off => by
        simpa [front,adjacentStageStacks,embStk] using priv j off)
    let post := fun (user : U) (F : Stacks n prime) => user = u.user ∧
      ∃ z, ParentStageWords (fun i => dst (i.castAdd 2)) dst V z F ∧ (stages++[last]).foldr (fun i cont a => ∃ b, effect i a b ∧ cont b) (fun a => a = z) y
    obtain ⟨z,F,steps,done,bill,⟨user,r,rep,rest⟩,_⟩ :=
      compose left right a b u (embStk front S) (embStk (Fin.natAdd m) S) v C t
        ((stages++[last]).map price).sum post ran (by
          intro v' C' user shared frame'
          have live : ParentStageWords (fun i => input (i.castAdd 2)) input V y C' := by
            refine ⟨fun i => (shared _).1.trans (ready.left i),fun i => (shared _).2.trans (ready.right i),?_⟩
            intro j z
            rw [(shared _).1,(shared _).2]
            exact ready.controls j z
          obtain ⟨z,F,s,r,run,cost,preserved,rep,rest⟩ := nextRun y v' C' live (by
            intro j off
            have outside (h) : (src.trans front) h ≠ j.natAdd m := by
              intro eq
              have hv := congrArg Fin.val eq
              change (src h).val = m+j.val at hv
              omega
            have atJ := frame (j.natAdd m) outside
            simp only [adjacentStageStacks,Fin.addCases_right] at atJ
            exact ⟨(frame' j off).1.trans atJ.1,(frame' j off).2.trans atJ.2⟩)
          exact ⟨z,F,s,run,cost,preserved.trans (user.trans same),r,rep,rest⟩)
    have split : adjacentStageStacks (embStk front S) (embStk (Fin.natAdd m) S) = S := splitStacks S
    rw [split] at done
    exact ⟨z,F,steps,r,done,bill.trans (Nat.add_le_add_right paid _),user,⟨rep.left,rep.right,rep.controls⟩,y,trace,rest⟩


/-- Relabel the output ports of a physical owner bank in one host instruction. -/
private theorem permutedPiece {U : Type} {q V : ℕ} (p : Equiv.Perm (Fin 142081)) :
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
      PackedPieceHandoff V (fun x y => y = x ∘ p) body code src dst prepared 1 := by
  let dst := (extendPermutation p 2).toEmbedding
  refine ⟨Empty,142081+2,Empty.elim,.act .done,Function.Embedding.refl _,dst,
    ⟨[],[],fun _ => [],fun _ => []⟩,?_⟩
  intro x u S live _
  refine ⟨u,S,1,x ∘ p,Exec.act .done _,le_rfl,rfl,?_,rfl⟩
  constructor
  · intro i
    exact (congrArg S.L (extendLeft p i)).trans (live.left (p i))
  · intro i
    exact (congrArg S.R (extendLeft p i)).trans (live.right (p i))
  · intro j z
    change _ = readAt blank (S.L (extendPermutation p 2 (j.natAdd 142081))) (S.R (extendPermutation p 2 (j.natAdd 142081))) _
    rw [extendRight]
    exact live.controls j z

/-- Assemble the certified node schedule on full parent words. The final
idle remainder and side exchange each cost one instruction. -/
theorem packedNodeHandoffs {U : Type} {q w B W : ℕ}
    (idle stage : Fin 9 → OwnerArray w B W → OwnerArray w B W → Prop) (price : Piece → ℕ) :
    let V := (prime^w)^16*(B*((prime^w)^112*W))
    let effect := nodePieceEffect w B W idle stage
    let cost := Function.update (Function.update price (.remainder 9) 1) .exchangeSides 1
    (∀ i ∈ nodeProgram, i ≠ .exchangeSides → i ≠ .remainder 9 →
      ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
        PackedPieceHandoff V (effect i) body code src dst prepared (price i)) →
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
      PackedPieceHandoff V (fun x y => nodeProgram.foldr (fun i cont a => ∃ b, effect i a b ∧ cont b)
        (fun a => a = y) x) body code src dst prepared (nodeProgram.map cost).sum := by
  intro V effect cost available
  have schedule : nodeProgram = nodeProgram.dropLast ++ [.exchangeSides] := by decide +kernel
  rw [schedule]
  apply packedHandoffList
  intro i mem
  rw [← schedule] at mem
  by_cases exchange : i = .exchangeSides
  · subst i
    simpa [effect,cost,nodePieceEffect] using permutedPiece (U := U) (q := q) (V := V) exchangeOwner
  by_cases terminal : i = .remainder 9
  · subst i
    simpa [effect,cost,nodePieceEffect] using permutedPiece (U := U) (q := q) (V := V) (Equiv.refl _)
  simpa only [cost,Function.update_of_ne exchange,Function.update_of_ne terminal] using available i mem exchange terminal


private noncomputable def packedBridgeStates : Piece → ℕ
  | .bridge d s => if h : Piece.bridge d s ∈ nodeProgram then (packedBridgeHandoff d s h).choose else 0
  | _ => 0

private def isBridge : Piece → Bool
  | .bridge .. => true
  | _ => false

private theorem sumBridgeCopies (ps : List Piece) (f : Piece → ℕ) (copy : ℕ) :
    (ps.map (fun p => f p + if isBridge p then copy else 0)).sum =
      (ps.map f).sum + ps.countP isBridge * copy := by
  induction ps with
  | nil => simp
  | cons p ps ih => cases h : isBridge p <;> simp [h,ih,Nat.add_mul] <;> omega

private theorem bridgeCount : nodeProgram.countP isBridge = 9 := by decide +kernel

/-- Assemble all nine physical bridges, including their copies, at a capacity
fixed before the word volume and the sweep and remainder budgets. -/
theorem assembledPackedNode {U : Type} :
    ∃ states : ℕ, ∀ {q : ℕ}, states ≤ q → ∀ w B tail : ℕ,
    let V := (prime^w)^16*(B*((prime^w)^112*tail))
    0 < V → ∀ (stage idle : Fin 9 → OwnerArray w B tail → OwnerArray w B tail → Prop)
      (sweepCost idleCost : Fin 9 → ℕ),
    (∀ i, ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PackedPieceHandoff V (stage i) body code src dst prepared (sweepCost i)) →
    (∀ i, ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PackedPieceHandoff V (idle i) body code src dst prepared (idleCost i)) →
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PackedPieceHandoff V (fun x y => nodeProgram.foldr
        (fun i cont a => ∃ b, nodePieceEffect w B tail idle stage i a b ∧ cont b)
        (fun a => a = y) x) body code src dst prepared
        ((∑ i, sweepCost i) + (∑ i, idleCost i) + 9*(2*(76*17760*V*(142081+7)+6)+1+(142081*(8*V+10)+1))+2) := by
  refine ⟨(nodeProgram.map packedBridgeStates).sum,?_⟩
  intro q fits w B tail V pos stage idle sweepCost idleCost sweep remainder
  let price : Piece → ℕ := fun p => nodeHandoffCost V sweepCost idleCost p +
    (if isBridge p then 142081*(8*V+10)+1 else 0)
  let cost := Function.update (Function.update price (.remainder 9) 1) .exchangeSides 1
  have total : (nodeProgram.map cost).sum = (∑ i, sweepCost i) + (∑ i, idleCost i) +
      9*(2*(76*17760*V*(142081+7)+6)+1+(142081*(8*V+10)+1))+2 := by
    have same : cost = price := by
      funext p
      by_cases ex : p = .exchangeSides
      · subst p; rfl
      by_cases term : p = .remainder 9
      · subst p; rfl
      simp only [cost,Function.update_of_ne ex,Function.update_of_ne term]
    rw [same,sumBridgeCopies nodeProgram (nodeHandoffCost V sweepCost idleCost),bridgeCount,nodeHandoffCost_sum]
    ring
  rw [← total]
  apply packedNodeHandoffs idle stage price
  intro p mem exchange terminal
  cases p with
  | stage i => simpa [price,nodeHandoffCost,isBridge,nodePieceEffect] using sweep i
  | remainder i =>
    have ne : i ≠ 9 := fun eq => terminal (eq ▸ rfl)
    have h : i < 9 := by simp [nodeProgram] at mem; omega
    simpa [price,nodeHandoffCost,isBridge,nodePieceEffect,h] using remainder ⟨i,h⟩
  | bridge d s =>
    have cap := (List.le_sum_of_mem (List.mem_map_of_mem (f := packedBridgeStates) mem)).trans fits
    simp only [packedBridgeStates,dite_eq_left mem] at cap
    obtain ⟨t,c,src,dst,D,run⟩ := (packedBridgeHandoff d s mem).choose_spec (U := U) cap pos
    exact ⟨Empty,t,Empty.elim,c,src,dst,D,by simpa [price,nodeHandoffCost,isBridge,nodePieceEffect] using run⟩
  | exchangeSides => exact (exchange rfl).elim


/-- The assembled physical program interchanges the two fields on every
role tape, for all inherited blocks, matrix labels and trailing positions. -/
theorem packedNodeInterchange {U : Type} :
    ∃ states : ℕ, ∀ {q : ℕ}, states ≤ q → ∀ w B K (parent : Fin 64 → ZMod (prime^w))
      (units : ∀ i, IsUnit (parent i)),
    let W := B*prime^(64*(w*64))*K
    let V := (prime^w)^16*(1*((prime^w)^112*W))
    let chart := nodeWindowEquiv w 1 W parent units
    let read := fun j => readRoles (fun z => chart (0,windowState w z,j))
    0 < V → ∀ (sweepCost idleCost : Fin 9 → ℕ),
    (∀ i, ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
      PackedPieceHandoff V (borrowedStageHandoff w B K parent units i) body code src dst prepared (sweepCost i)) →
    (∀ i, ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
      PackedPieceHandoff V (fun a d => ∀ j, read j d = (Piece.remainder i.val).run (read j a))
        body code src dst prepared (idleCost i)) →
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
      PackedPieceHandoff V (fun x y => ∀ (r : Role) i, let (b,s,j) := chart.symm i
        let tape := bankTape r.bank (r.replica,r.port,r.cls)
        y tape i = x tape (chart (b,(s.2,s.1),j))) body code src dst prepared
        ((∑ i, sweepCost i) + (∑ i, idleCost i) + 9*(2*(76*17760*V*(142081+7)+6)+1+(142081*(8*V+10)+1))+2) := by
  obtain ⟨states,assemble⟩ := assembledPackedNode (U := U)
  refine ⟨states,?_⟩
  intro q fits w B K parent units W V chart read pos sweepCost idleCost sweep remainder
  obtain ⟨P,t,body,code,src,dst,prepared,run⟩ := assemble fits w 1 W pos _ _ sweepCost idleCost sweep remainder
  refine ⟨P,t,body,code,src,dst,prepared,?_⟩
  intro x u S words fresh
  obtain ⟨z,G,k,y,exec,paid,user,out,trace⟩ := run x u S words fresh
  exact ⟨z,G,k,y,exec,paid,user,out,fun r => borrowedNodeHandoff_cell parent units r _ x y
    (fun _ _ _ h => h) trace⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
