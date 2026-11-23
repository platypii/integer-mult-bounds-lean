module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedPhysicalStage
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordCleanup
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
  obtain ⟨bank,_,_,sequence⟩ := runAdjacentStages (A := prime) (P := P) (R := R) (U := U) (q := Q) (returnedFan fan) input
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

/-- Cost of clearing both stacks of a tape. -/
def cleanupWeight (l r : List (Fin (prime+4))) : ℕ := 4*l.length+2*r.length+4

/-- Copy a represented result to fresh owner words, keeping the two live
counters on the chart. The cost includes every owner and the spare. -/
theorem packedResultWordsWithCharge {P U : Type} {T Q : ℕ} (localFan : Fin (142081+2) ↪ Fin T)
    (body : P → Pr P (Exit.size 0 T) Q prime U) :
    let fan := localFan.trans (Exit.chart 0 T)
    let dst := returnedFan localFan
    let tmp := Exit.tmp 0 T
    ∃ code, ∀ {V : ℕ} (x : Fin 142081 → Fin V → ZMod 2) u S,
      HelperFan fan x S → S.L tmp = [] → S.R tmp = [] →
      (∀ i : Fin 142081, S.L (dst (i.castAdd 2)) = [] ∧ S.R (dst (i.castAdd 2)) = []) →
      ∃ z G k, Exec body code (mk u S) k (mk z G) ∧ k ≤ 142081*(8*V+10)+1 ∧
        z.user = u.user ∧ ParentStageWords (fun i => dst (i.castAdd 2)) dst V x G ∧
        ∀ js : List (Fin (Exit.size 0 T)), js.Nodup → k+tapeCharge cleanupWeight js G ≤
          tapeCharge cleanupWeight js S+(142081*(10*V+10)+1) := by
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
  refine ⟨z,_,k,run,paid,user,⟨fun i => (empty i).1,words,?_⟩,?_⟩
  · intro j z
    have keep := off (dst (j.natAdd 142081)) (fun i => dst.injective.ne (by
      intro eq; have h := congrArg Fin.val eq; change i.val = 142081+j.val at h; omega))
    change _ = readAt blank (S.L _) (R _) _
    rw [keep,show dst (j.natAdd 142081) = fan (j.natAdd 142081) from returnedFan_counter localFan j]
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,CountedLoopReuseAlphabet.controls,
      ite_self,embStk,Function.comp_apply] using live (j.natAdd 142081) z
  · intro js distinct
    apply placedCleanup_cost_le dest S {S with R := R} cleanupWeight k _ (fun j away => ⟨rfl,off j away⟩) _ js distinct
    intro is unique
    have before (i) : cleanupWeight (S.L (dest i)) (S.R (dest i)) = 4 := by
      rw [show S.L (dest i) = [] from (empty i).1,show S.R (dest i) = [] from (empty i).2]
      rfl
    have after (i) : cleanupWeight (S.L (dest i)) (R (dest i)) = 2*V+4 := by
      change cleanupWeight (S.L (dst (i.castAdd 2))) (R (dest i)) = _
      rw [(empty i).1,words i]
      simp [cleanupWeight]
    change k+(is.map fun i => cleanupWeight (S.L (dest i)) (R (dest i))).sum ≤
      (is.map fun i => cleanupWeight (S.L (dest i)) (S.R (dest i))).sum+_
    simp only [before,after,List.map_const',List.sum_replicate_nat,Nat.mul_add]
    have count : is.length ≤ 142081 := by simpa only [Fintype.card_fin] using unique.length_le_card
    have bound := Nat.mul_le_mul_right (2*V) count
    omega

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
  obtain ⟨code,run⟩ := packedResultWordsWithCharge localFan body
  refine ⟨code,?_⟩
  intro V x u S live tl tr empty
  obtain ⟨z,G,k,ran,paid,user,out,_⟩ := run x u S live tl tr empty
  exact ⟨z,G,k,ran,paid,user,out⟩

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

def PackedPieceHandoffWithCharge {P U : Type} {t q : ℕ} (weight : List (Fin (prime+4)) → List (Fin (prime+4)) → ℕ) (V : ℕ)
    (effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop)
    (body : P → Pr P t q prime U) (code : Pr P t q prime U)
    (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime) (price : ℕ) : Prop :=
  ∀ x u S, ParentStageWords (fun i => src (i.castAdd 2)) src V x S →
    (∀ j, (∀ i, src i ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
    ∃ z F steps y, Exec body code (mk u S) steps (mk z F) ∧ (∀ js : List (Fin t), js.Nodup → steps+tapeCharge weight js F ≤ tapeCharge weight js S+price) ∧ z.user = u.user ∧
      ParentStageWords (fun i => dst (i.castAdd 2)) dst V y F ∧ effect x y

/-- Execute a scheduled bridge and materialize the entire output bank. -/
private theorem packedBridgeProgram (d s : ℕ) (scheduled : Piece.bridge d s ∈ nodeProgram) :
    ∃ states : ℕ, ∀ {q : ℕ} {U : Type}, states ≤ q →
      ∃ (t : ℕ) (code : Pr Empty t q prime U), ∃ src dst prepared, ∀ {V : ℕ}, 0 < V →
        PackedPieceHandoff V (fun x y => y = fun j z => bridgeColumn d s (fun l => x l z) j)
          Empty.elim code src dst prepared (2*(76*17760*V*(142081+7)+6)+1 + (142081*(8*V+10)+1)) := by
  obtain ⟨states,bridge⟩ := bridgeColumns_exec d s scheduled
  refine ⟨states,?_⟩
  intro q U room
  let idFan := Function.Embedding.refl (Fin (142081+2))
  let fan := idFan.trans (Exit.chart 0 (142081+2))
  let dst := returnedFan idFan
  let tmp := Exit.tmp 0 (142081+2)
  let body : Empty → Pr Empty (Exit.size 0 (142081+2)) q prime U := Empty.elim
  obtain ⟨code,run⟩ := bridge fan body room
  obtain ⟨copy,materialize⟩ := packedResultWords_exec idFan body
  refine ⟨_,code.seq copy,fan,dst,⟨[],[],fun _ => [],fun _ => []⟩,?_⟩
  intro V pos x u S words fresh
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

/-- Execute a scheduled bridge and materialize the entire output bank. -/
theorem packedBridgeHandoff (d s : ℕ) (scheduled : Piece.bridge d s ∈ nodeProgram) :
    ∃ states : ℕ, ∀ {q V : ℕ} {U : Type}, states ≤ q → 0 < V →
      ∃ (t : ℕ) (code : Pr Empty t q prime U), ∃ src dst prepared,
        PackedPieceHandoff V (fun x y => y = fun j z => bridgeColumn d s (fun l => x l z) j)
          Empty.elim code src dst prepared (2*(76*17760*V*(142081+7)+6)+1 + (142081*(8*V+10)+1)) := by
  obtain ⟨states,build⟩ := packedBridgeProgram d s scheduled
  refine ⟨states,?_⟩
  intro q V U fits pos
  obtain ⟨t,code,src,dst,seed,run⟩ := build (U := U) fits
  exact ⟨t,code,src,dst,seed,run pos⟩

/-- The bridge program is fixed before the volume. Its tape growth therefore
adds a fixed multiple of its linear running time to the cleanup bill. -/
theorem packedBridgeWithCharge (d s : ℕ) (scheduled : Piece.bridge d s ∈ nodeProgram) :
    ∃ states : ℕ, ∀ {q : ℕ} {U : Type}, states ≤ q →
      ∃ (rate t : ℕ) (code : Pr Empty t q prime U), ∃ src dst seed, ∀ {V : ℕ}, 0 < V →
        PackedPieceHandoffWithCharge cleanupWeight V
          (fun x y => y = fun j z => bridgeColumn d s (fun l => x l z) j)
          Empty.elim code src dst seed (rate*V) := by
  obtain ⟨states,build⟩ := packedBridgeProgram d s scheduled
  refine ⟨states,?_⟩
  intro q U fits
  obtain ⟨t,code,src,dst,seed,run⟩ := build (U := U) fits
  let push := Fast.Main.mnProgPush code
  let rate := 2*(76*17760*(142081+7)+6)+1+(142081*(8+10)+1)
  refine ⟨(1+6*push)*rate,t,code,src,dst,seed,?_⟩
  intro V positive x u S words fresh
  obtain ⟨z,F,n,y,exec,paid,user,out,changed⟩ := run positive x u S words fresh
  refine ⟨z,F,n,y,exec,?_,user,out,changed⟩
  intro js distinct
  have growth := Cover.Fallback.recordCleanup_cost_le js distinct exec (c := push) le_rfl (fun e => nomatch e)
  change tapeCharge cleanupWeight js F+1 ≤ tapeCharge cleanupWeight js S+1+6*(push*n) at growth
  have time : n ≤ rate*V := by dsimp [rate]; omega
  have bound := Nat.mul_le_mul_left (1+6*push) time
  rw [← Nat.mul_assoc] at bound
  simp only [Nat.add_mul,Nat.one_mul,Nat.mul_assoc] at bound ⊢
  omega

/-- Assemble one program for every runtime configuration. Widths, seed words
and budgets may vary while the procedure labels and tape placements stay fixed. -/
theorem packedHandoffFamilyWithCharge {Job U Config : Type} {q : ℕ} (weight : List (Fin (prime+4)) → List (Fin (prime+4)) → ℕ) (volume : Config → ℕ)
    (effect : ∀ c, Job → (Fin 142081 → Fin (volume c) → ZMod 2) → (Fin 142081 → Fin (volume c) → ZMod 2) → Prop)
    (price : Config → Job → ℕ) (stages : List Job) (last : Job)
    (available : ∀ i ∈ stages++[last], ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Config → Stacks t prime), ∀ c,
      PackedPieceHandoffWithCharge weight (volume c) (effect c i) body code src dst (prepared c) (price c i)) :
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Config → Stacks t prime), ∀ c,
      PackedPieceHandoffWithCharge weight (volume c) (fun x y => (stages++[last]).foldr
        (fun i cont a => ∃ b, effect c i a b ∧ cont b) (fun a => a = y) x)
        body code src dst (prepared c) ((stages++[last]).map (price c)).sum := by
  induction stages with
  | nil =>
    obtain ⟨P,t,body,code,src,dst,D,run⟩ := available last (by simp)
    refine ⟨P,t,body,code,src,dst,D,?_⟩
    intro c x u S live frame
    obtain ⟨z,F,steps,y,ran,cost,user,rep,trace⟩ := run c x u S live frame
    exact ⟨z,F,steps,_,ran,by simpa using cost,user,rep,y,trace,rfl⟩
  | cons i stages ih =>
    obtain ⟨P,m,left,a,src,mid,L,firstRun⟩ := available i (by simp)
    obtain ⟨R,n,right,b,input,dst,D,nextRun⟩ := ih (fun j hj => available j (List.mem_cons_of_mem _ hj))
    obtain ⟨bank,_,_,compose⟩ := runAdjacentStagesWithCharge (P := P) (R := R) (U := U) (q := q)
      (A := prime) mid input
    let front := Fin.castAddEmb n (n := m)
    refine ⟨P ⊕ R,m+n,Sum.elim (fun g => embProg front Sum.inl (left g)) (fun g => embProg bank Sum.inr (right g)),
      (embProg front Sum.inl a).seq (embProg bank Sum.inr b),src.trans front,dst.trans bank,(fun c => adjacentStageStacks (L c) (D c)),?_⟩
    intro c x u S live frame
    have priv (j : Fin m) (off : ∀ h, src h ≠ j) := frame (front j)
      (fun h eq => off h (front.injective eq))
    obtain ⟨v,C,t,y,ran,paid,same,ready,trace⟩ :=
      firstRun c x (embDn front u) (embStk front S) ⟨live.left,live.right,live.controls⟩ (fun j off => by
        simpa [front,adjacentStageStacks,embStk] using priv j off)
    let post := fun (user : U) (F : Stacks n prime) => user = u.user ∧
      ∃ z, ParentStageWords (fun i => dst (i.castAdd 2)) dst (volume c) z F ∧ (stages++[last]).foldr (fun i cont a => ∃ b, effect c i a b ∧ cont b) (fun a => a = z) y
    obtain ⟨z,F,steps,done,bill,⟨user,r,rep,rest⟩,_⟩ :=
      compose left right a b u (embStk front S) (embStk (Fin.natAdd m) S) v C t
        (price c i) ((stages++[last]).map (price c)).sum weight post ran paid (by
          intro v' C' user shared frame'
          have live : ParentStageWords (fun i => input (i.castAdd 2)) input (volume c) y C' := by
            refine ⟨fun i => (shared _).1.trans (ready.left i),fun i => (shared _).2.trans (ready.right i),?_⟩
            intro j z
            rw [(shared _).1,(shared _).2]
            exact ready.controls j z
          obtain ⟨z,F,s,r,run,cost,preserved,rep,rest⟩ := nextRun c y v' C' live (by
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
    rw [split] at done bill
    exact ⟨z,F,steps,r,done,bill,user,⟨rep.left,rep.right,rep.controls⟩,y,trace,rest⟩


/-- Chain physical pieces in execution order and sum their individual budgets. -/
theorem packedHandoffListWithCharge {Job U : Type} {q : ℕ} (weight : List (Fin (prime+4)) → List (Fin (prime+4)) → ℕ) (V : ℕ)
    (effect : Job → (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop)
    (price : Job → ℕ) (stages : List Job) (last : Job)
    (available : ∀ i ∈ stages++[last], ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PackedPieceHandoffWithCharge weight V (effect i) body code src dst prepared (price i)) :
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PackedPieceHandoffWithCharge weight V (fun x y => (stages++[last]).foldr
        (fun i cont a => ∃ b, effect i a b ∧ cont b) (fun a => a = y) x)
        body code src dst prepared ((stages++[last]).map price).sum := by
  obtain ⟨P,t,body,code,src,dst,seed,run⟩ := packedHandoffFamilyWithCharge
    weight (fun _ : Unit => V) (fun _ => effect) (fun _ => price) stages last (by
      intro i mem
      obtain ⟨P,t,body,code,src,dst,seed,run⟩ := available i mem
      exact ⟨P,t,body,code,src,dst,fun _ => seed,fun _ => run⟩)
  exact ⟨P,t,body,code,src,dst,seed (),run ()⟩

-- The time-only list specialization can be restored from 30c56adf.

/-- Relabel the output ports of a physical owner bank in one host instruction. -/
private theorem permutedPiece {U : Type} {q : ℕ} (weight : List (Fin (prime+4)) → List (Fin (prime+4)) → ℕ) (p : Equiv.Perm (Fin 142081)) :
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared, ∀ V,
      PackedPieceHandoffWithCharge weight V (fun x y => y = x ∘ p) body code src dst prepared 1 := by
  let dst := (extendPermutation p 2).toEmbedding
  refine ⟨Empty,142081+2,Empty.elim,.act .done,Function.Embedding.refl _,dst,
    ⟨[],[],fun _ => [],fun _ => []⟩,?_⟩
  intro V x u S live _
  refine ⟨u,S,1,x ∘ p,Exec.act .done _,by intro js _; omega,rfl,?_,rfl⟩
  constructor
  · intro i
    exact (congrArg S.L (extendLeft p i)).trans (live.left (p i))
  · intro i
    exact (congrArg S.R (extendLeft p i)).trans (live.right (p i))
  · intro j z
    change _ = readAt blank (S.L (extendPermutation p 2 (j.natAdd 142081))) (S.R (extendPermutation p 2 (j.natAdd 142081))) _
    rw [extendRight]
    exact live.controls j z

/-- In the PR589 node, changing the runtime dimensions changes the seed and
the charges while the finite program and its owner tapes stay fixed. -/
theorem packedNodeFamilyWithCharge {Config U : Type} {q : ℕ}
    (weight : List (Fin (prime+4)) → List (Fin (prime+4)) → ℕ)
    (w B W : Config → ℕ)
    (idle stage : ∀ c, Fin 9 → OwnerArray (w c) (B c) (W c) → OwnerArray (w c) (B c) (W c) → Prop)
    (price : Config → Piece → ℕ) :
    let V := fun c => (prime^(w c))^16*(B c*((prime^(w c))^112*W c))
    let effect := fun c => nodePieceEffect (w c) (B c) (W c) (idle c) (stage c)
    let cost := fun c => Function.update (Function.update (price c) (.remainder 9) 1) .exchangeSides 1
    (∀ i ∈ nodeProgram, i ≠ .exchangeSides → i ≠ .remainder 9 →
      ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst, ∃ seed : Config → Stacks t prime,
        ∀ c, PackedPieceHandoffWithCharge weight (V c) (effect c i) body code src dst (seed c) (price c i)) →
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst, ∃ seed : Config → Stacks t prime,
      ∀ c, PackedPieceHandoffWithCharge weight (V c) (fun x y => nodeProgram.foldr
        (fun i cont a => ∃ b, effect c i a b ∧ cont b) (fun a => a = y) x) body code src dst (seed c)
          (nodeProgram.map (cost c)).sum := by
  intro V effect cost available
  have schedule : nodeProgram = nodeProgram.dropLast ++ [.exchangeSides] := by decide +kernel
  rw [schedule]
  apply packedHandoffFamilyWithCharge
  intro i mem
  rw [← schedule] at mem
  by_cases exchange : i = .exchangeSides
  · subst i
    obtain ⟨P,t,body,code,src,dst,seed,run⟩ := permutedPiece (U := U) (q := q) weight exchangeOwner
    exact ⟨P,t,body,code,src,dst,fun _ => seed,fun c => by simpa [cost,effect,nodePieceEffect] using run (V c)⟩
  by_cases terminal : i = .remainder 9
  · subst i
    obtain ⟨P,t,body,code,src,dst,seed,run⟩ := permutedPiece (U := U) (q := q) weight (Equiv.refl _)
    exact ⟨P,t,body,code,src,dst,fun _ => seed,fun c => by simpa [cost,effect,nodePieceEffect] using run (V c)⟩
  simpa only [cost,Function.update_of_ne exchange,Function.update_of_ne terminal] using available i mem exchange terminal

/-- Assemble the certified node schedule on full parent words. The final
idle remainder and side exchange each cost one instruction. -/
theorem packedNodeHandoffsWithCharge {U : Type} {q w B W : ℕ}
    (weight : List (Fin (prime+4)) → List (Fin (prime+4)) → ℕ)
    (idle stage : Fin 9 → OwnerArray w B W → OwnerArray w B W → Prop) (price : Piece → ℕ) :
    let V := (prime^w)^16*(B*((prime^w)^112*W))
    let effect := nodePieceEffect w B W idle stage
    let cost := Function.update (Function.update price (.remainder 9) 1) .exchangeSides 1
    (∀ i ∈ nodeProgram, i ≠ .exchangeSides → i ≠ .remainder 9 →
      ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
        PackedPieceHandoffWithCharge weight V (effect i) body code src dst prepared (price i)) →
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U), ∃ code src dst prepared,
      PackedPieceHandoffWithCharge weight V (fun x y => nodeProgram.foldr (fun i cont a => ∃ b, effect i a b ∧ cont b)
        (fun a => a = y) x) body code src dst prepared (nodeProgram.map cost).sum := by
  intro V effect cost available
  obtain ⟨P,t,body,code,src,dst,seed,run⟩ := packedNodeFamilyWithCharge weight
    (fun _ : Unit => w) (fun _ => B) (fun _ => W) (fun _ => idle) (fun _ => stage) (fun _ => price) (by
      intro i mem exchange terminal
      obtain ⟨P,t,body,code,src,dst,seed,run⟩ := available i mem exchange terminal
      exact ⟨P,t,body,code,src,dst,fun _ => seed,fun _ => run⟩)
  exact ⟨P,t,body,code,src,dst,seed (),run ()⟩

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
  obtain ⟨P,t,body,code,src,dst,seed,run⟩ :=
    packedNodeHandoffsWithCharge (U := U) (q := q) (fun _ _ => 0) idle stage price (by
      intro i mem exchange terminal
      obtain ⟨P,t,body,code,src,dst,seed,run⟩ := available i mem exchange terminal
      refine ⟨P,t,body,code,src,dst,seed,?_⟩
      intro x u S live frame
      obtain ⟨z,F,n,y,ran,paid,rest⟩ := run x u S live frame
      exact ⟨z,F,n,y,ran,by intro js _; simpa [tapeCharge] using paid,rest⟩)
  refine ⟨P,t,body,code,src,dst,seed,?_⟩
  intro x u S live frame
  obtain ⟨z,F,n,y,ran,paid,rest⟩ := run x u S live frame
  exact ⟨z,F,n,y,ran,by simpa [tapeCharge] using paid [] (by simp),rest⟩

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


/-- Assemble all nine physical bridges, including their copies, at a capacity
fixed before the word volume and the sweep and remainder budgets. -/
theorem assembledPackedNodeWithCharge {U : Type} :
    ∃ states : ℕ, ∀ {q : ℕ}, states ≤ q → ∃ bridgeRate : ℕ, ∀ w B tail : ℕ,
    let V := (prime^w)^16*(B*((prime^w)^112*tail))
    0 < V → ∀ (stage idle : Fin 9 → OwnerArray w B tail → OwnerArray w B tail → Prop)
      (sweepCost idleCost : Fin 9 → ℕ),
    (∀ i, ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PackedPieceHandoffWithCharge cleanupWeight V (stage i) body code src dst prepared (sweepCost i)) →
    (∀ i, ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PackedPieceHandoffWithCharge cleanupWeight V (idle i) body code src dst prepared (idleCost i)) →
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PackedPieceHandoffWithCharge cleanupWeight V (fun x y => nodeProgram.foldr
        (fun i cont a => ∃ b, nodePieceEffect w B tail idle stage i a b ∧ cont b)
        (fun a => a = y) x) body code src dst prepared
        ((∑ i, sweepCost i) + (∑ i, idleCost i) + 9*(2*(76*17760*V*(142081+7)+6)+1+bridgeRate*V)+2) := by
  classical
  let states : Piece → ℕ
    | .bridge d s => if h : Piece.bridge d s ∈ nodeProgram then (packedBridgeWithCharge d s h).choose else 0
    | _ => 0
  refine ⟨(nodeProgram.map states).sum,?_⟩
  intro q fits
  have bridge d s (mem : Piece.bridge d s ∈ nodeProgram) :=
    (packedBridgeWithCharge d s mem).choose_spec (U := U) (q := q) (by
      have h := (List.le_sum_of_mem (List.mem_map_of_mem (f := states) mem)).trans fits
      simpa only [states,dif_pos mem] using h)
  let rate : Piece → ℕ
    | .bridge d s => if h : Piece.bridge d s ∈ nodeProgram then (bridge d s h).choose else 0
    | _ => 0
  let bridgeRate := (nodeProgram.map rate).sum
  refine ⟨bridgeRate,?_⟩
  intro w B tail V pos stage idle sweepCost idleCost sweep remainder
  let price : Piece → ℕ := fun p => nodeHandoffCost V sweepCost idleCost p +
    (if isBridge p then bridgeRate*V else 0)
  let cost := Function.update (Function.update price (.remainder 9) 1) .exchangeSides 1
  have total : (nodeProgram.map cost).sum = (∑ i, sweepCost i) + (∑ i, idleCost i) +
      9*(2*(76*17760*V*(142081+7)+6)+1+bridgeRate*V)+2 := by
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
  apply packedNodeHandoffsWithCharge cleanupWeight idle stage price
  intro p mem exchange terminal
  cases p with
  | stage i => simpa [price,nodeHandoffCost,isBridge,nodePieceEffect] using sweep i
  | remainder i =>
    have ne : i ≠ 9 := fun eq => terminal (eq ▸ rfl)
    have h : i < 9 := by simp [nodeProgram] at mem; omega
    simpa [price,nodeHandoffCost,isBridge,nodePieceEffect,h] using remainder ⟨i,h⟩
  | bridge d s =>
    obtain ⟨t,c,src,dst,D,run⟩ := (bridge d s mem).choose_spec
    have leRate : (bridge d s mem).choose ≤ bridgeRate := by
      simpa only [rate,dif_pos mem] using List.le_sum_of_mem (List.mem_map_of_mem (f := rate) mem)
    refine ⟨Empty,t,Empty.elim,c,src,dst,D,?_⟩
    intro x u S live fresh
    obtain ⟨z,F,n,y,ran,bill,user,out,result⟩ := run pos x u S live fresh
    refine ⟨z,F,n,y,ran,?_,user,out,result⟩
    intro js distinct
    have h := (bill js distinct).trans (Nat.add_le_add_left (Nat.mul_le_mul_right V leRate) _)
    simp only [price,isBridge,ite_true]
    omega
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
