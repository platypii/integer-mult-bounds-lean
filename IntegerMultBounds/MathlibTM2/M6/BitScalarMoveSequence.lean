module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedSweep

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host
open Shared50ModularControl (prime)
open Certificates.PR589

/-- Pair each paid MOVE with the scalar gates since the previous MOVE.
The second component holds the gates after the final paid edge. -/
noncomputable def phaseMoveBlocks : List RawGate → (ℕ → ℕ) →
    List (List RawGate × (ℕ × ℕ)) × List RawGate
  | [], _ => ([], [])
  | g :: gs, current =>
    let moves := ((Frames.edges [g] current).filter positiveMove).map fun edge => ([],edge)
    let (blocks,suffix) := phaseMoveBlocks gs (Frames.run [g] current)
    match blocks with
    | [] => (moves,g :: suffix)
    | (gates,edge) :: rest => (moves ++ (g :: gates,edge) :: rest,suffix)

/-- Projecting the block schedule recovers every original scalar gate
and exactly the positive-rank edge list, both in execution order. -/
theorem phaseMoveBlocks_spec (gs : List RawGate) (current : ℕ → ℕ) :
    let (blocks,suffix) := phaseMoveBlocks gs current
    blocks.map Prod.snd = (Frames.edges gs current).filter positiveMove ∧
      blocks.flatMap Prod.fst ++ suffix = gs := by
  induction gs generalizing current with
  | nil => exact ⟨rfl,rfl⟩
  | cons g gs ih =>
    have edges := Frames.edges_append [g] gs current
    simp only [List.singleton_append] at edges
    have emptyBlocks (es : List (ℕ × ℕ)) :
        (es.map (fun e => (([] : List RawGate),e))).flatMap Prod.fst = [] := by
      induction es with
      | nil => rfl
      | cons _ _ ih => simpa only [List.map_cons,List.flatMap_cons,List.nil_append] using ih
    have tail := ih (Frames.run [g] current)
    cases eq : phaseMoveBlocks gs (Frames.run [g] current) with
    | mk blocks suffix =>
      rw [eq] at tail
      cases blocks with
      | nil =>
        obtain ⟨moveOrder,gateOrder⟩ := tail
        change suffix = gs at gateOrder
        simp [phaseMoveBlocks,eq,edges,List.filter_append,Function.comp_def,← moveOrder,gateOrder,emptyBlocks]
      | cons head rest =>
        obtain ⟨gates,edge⟩ := head
        obtain ⟨moveOrder,gateOrder⟩ := tail
        simp only [List.map_cons,List.flatMap_cons,List.append_assoc] at moveOrder gateOrder
        simp [phaseMoveBlocks,eq,edges,List.filter_append,Function.comp_def,← moveOrder,gateOrder,List.append_assoc,emptyBlocks]

/-- Executing the grouped scalar/MOVE schedule preserves their interleaving.
The state may carry the occurrence index used to select the MOVE register. -/
private theorem phaseMoveBlocks_fold {α : Type*} (gate : α → RawGate → α) (move : α → ℕ × ℕ → α)
    (gs : List RawGate) (current : ℕ → ℕ) (x : α) :
    let schedule := phaseMoveBlocks gs current
    let block := fun x (b : List RawGate × (ℕ × ℕ)) => move (b.1.foldl gate x) b.2
    schedule.2.foldl gate (schedule.1.foldl block x) =
      (gs.foldl (fun (state : α × (ℕ → ℕ)) g =>
        (gate (((Frames.edges [g] state.2).filter positiveMove).foldl move state.1) g,
         Frames.run [g] state.2)) (x,current)).1 := by
  have emptyBlocks (es : List (ℕ × ℕ)) (y : α) :
      (es.map (fun e => (([] : List RawGate),e))).foldl (fun x b => move (b.1.foldl gate x) b.2) y = es.foldl move y := by
    induction es generalizing y with
    | nil => rfl
    | cons e es ih => exact ih (move y e)
  induction gs generalizing current x with
  | nil => rfl
  | cons g gs ih =>
    let es := (Frames.edges [g] current).filter positiveMove
    have tail := ih (Frames.run [g] current) (gate (es.foldl move x) g)
    cases eq : phaseMoveBlocks gs (Frames.run [g] current) with
    | mk blocks suffix =>
      rw [eq] at tail
      cases blocks with
      | nil =>
        simpa only [phaseMoveBlocks,eq,List.foldl_cons,List.foldl_nil,emptyBlocks,es] using tail
      | cons b rest =>
        obtain ⟨gates,e⟩ := b
        simpa only [phaseMoveBlocks,eq,List.foldl_append,List.foldl_cons,emptyBlocks,es] using tail

private theorem foldOccurrences {α β : Type*} (f : α → ℕ → β → α)
    (xs : List β) (x : α) (start : ℕ) :
    xs.foldl (fun (s : α × ℕ) b => (f s.1 s.2 b,s.2+1)) (x,start) =
      ((List.finRange xs.length).foldl (fun y i => f y (start+i.val) xs[i.val]) x,start+xs.length) := by
  induction xs generalizing x start with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons,ih]
    simp only [List.length_cons,List.finRange_succ,List.foldl_cons,List.foldl_map,Fin.val_zero,
      Nat.add_zero,List.getElem_cons_zero,Fin.val_succ,List.getElem_cons_succ,Nat.add_right_comm start 1,
      Nat.add_assoc]

/-- Process the moves attached to a gate in the active frame before applying
the scalar gate. The directory index advances once per paid edge. -/
noncomputable def runIndexedPhase {α : Type*} (gate : α → RawGate → α) (move : α → ℕ → ℕ × ℕ → α)
    (gs : List RawGate) (current : ℕ → ℕ) (x : α) (start : ℕ) : α :=
  ((gs.foldl (fun (state : (α × ℕ) × (ℕ → ℕ)) g =>
    let s := ((Frames.edges [g] state.2).filter positiveMove).foldl
      (fun (s : α × ℕ) e => (move s.1 s.2 e,s.2+1)) state.1
    ((gate s.1 g,s.2),Frames.run [g] state.2)) ((x,start),current)).1).1

/-- The finite-index fold produced by the phase machine agrees with executing
each gate after its positive-rank moves, starting at the phase's directory offset. -/
theorem indexedPhase_fold {α : Type*} (gate : α → RawGate → α) (move : α → ℕ → ℕ × ℕ → α)
    (gs : List RawGate) (current : ℕ → ℕ) (x : α) (start : ℕ) :
    let schedule := phaseMoveBlocks gs current
    let blocks := schedule.1
    schedule.2.foldl gate ((List.finRange blocks.length).foldl
      (fun y i => move (blocks[i.val].1.foldl gate y) (start+i.val) blocks[i.val].2) x) =
      runIndexedPhase gate move gs current x start := by
  intro schedule blocks
  let scalar := fun (s : α × ℕ) g => (gate s.1 g,s.2)
  let paid := fun (s : α × ℕ) e => (move s.1 s.2 e,s.2+1)
  have gates (hs : List RawGate) (s : α × ℕ) : hs.foldl scalar s = (hs.foldl gate s.1,s.2) := by
    induction hs generalizing s with
    | nil => rfl
    | cons g hs ih => exact ih (scalar s g)
  have order := congrArg Prod.fst (phaseMoveBlocks_fold scalar paid gs current (x,start))
  simp only [gates] at order
  dsimp only [paid] at order
  rw [foldOccurrences (fun y j (b : List RawGate × (ℕ × ℕ)) => move (b.1.foldl gate y) j b.2)] at order
  exact order

/-- Every block selected by its MOVE occurrence, and the final suffix,
can be passed directly to the selected-word gate compiler. -/
theorem phaseMoveBlocks_allowed (gs : List RawGate) (current : ℕ → ℕ)
    (allowed : ∀ g ∈ gs, g ∈ program) :
    let schedule := phaseMoveBlocks gs current
    (∀ i : Fin schedule.1.length, ∀ g ∈ schedule.1[i].1, g ∈ program) ∧
      (∀ g ∈ schedule.2, g ∈ program) := by
  have gates := (phaseMoveBlocks_spec gs current).2
  constructor
  · intro i g hg
    apply allowed
    rw [← gates]
    exact List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨_,List.getElem_mem (n := i.val) i.isLt,hg⟩)
  · intro g hg
    apply allowed
    rw [← gates]
    exact List.mem_append_right _ hg

/-- Splitting the scalar word at MOVE boundaries charges every gate once. -/
theorem phaseMoveBlocks_charge (gs : List RawGate) (current : ℕ → ℕ) (charge : RawGate → ℕ) :
    let schedule := phaseMoveBlocks gs current
    (schedule.1.map (fun block => (block.1.map charge).sum)).sum +
      (schedule.2.map charge).sum = (gs.map charge).sum := by
  have sumBlocks (blocks : List (List RawGate × (ℕ × ℕ))) :
      (blocks.map (fun block => (block.1.map charge).sum)).sum =
        ((blocks.flatMap Prod.fst).map charge).sum := by
    induction blocks with
    | nil => rfl
    | cons block rest ih => simp [ih]
  dsimp only
  rw [sumBlocks,← List.sum_append,← List.map_append,(phaseMoveBlocks_spec gs current).2]

private theorem phasePairOrder (gs hs : List RawGate) (cur next : ℕ → ℕ) :
    ((phaseMoveBlocks gs cur).1 ++ (phaseMoveBlocks hs next).1).map Prod.snd =
      (Frames.edges gs cur ++ Frames.edges hs next).filter positiveMove := by
  rw [List.map_append,(phaseMoveBlocks_spec _ _).1,(phaseMoveBlocks_spec _ _).1,List.filter_append]

theorem invocationMoveBlocks_order :
    let before := phaseMoveBlocks (sectionD ++ sectionA) (Frames.snapshot Frames.initialRefs)
    let after := phaseMoveBlocks (sectionB ++ sectionC) (Frames.scatterFinish Frames.beforeScatter)
    (before.1 ++ after.1).map Prod.snd = Geometry.Moves.phaseEdges.filter positiveMove :=
  phasePairOrder _ _ _ _

private theorem appendMoveIndices {α β : Type} (before after : List (α × β)) (edges : List β)
    (order : (before ++ after).map Prod.snd = edges) :
    ∃ (pre : Fin before.length → Fin edges.length) (post : Fin after.length → Fin edges.length),
      (∀ i, (pre i).val = i.val ∧ edges[pre i] = before[i].2) ∧
      (∀ i, (post i).val = before.length+i.val ∧ edges[post i] = after[i].2) := by
  have size := congrArg List.length order
  simp only [List.length_map,List.length_append] at size
  let pre (i : Fin before.length) : Fin edges.length := ⟨i.val,by rw [← size]; omega⟩
  let post (i : Fin after.length) : Fin edges.length := ⟨before.length+i.val,by rw [← size]; omega⟩
  have atIndex (i : Fin edges.length) :
      edges[i] = ((before ++ after)[i.val]'(by rw [List.length_append,size]; exact i.isLt)).2 := by
    change edges[i.val] = _
    exact (List.getElem_of_eq order.symm i.isLt).trans (List.getElem_map Prod.snd)
  refine ⟨pre,post,fun i => ⟨rfl,?_⟩,fun i => ⟨rfl,?_⟩⟩
  · rw [atIndex, List.getElem_append_left i.isLt]
    rfl
  · rw [atIndex, List.getElem_append_right (show before.length ≤ (post i).val by dsimp [post]; omega)]
    simp [post]

/-- Locate each phase-local MOVE in the worker directory. Positions after
COPY start immediately after the last pre-COPY occurrence. -/
theorem invocationMoveIndices :
    let before := (phaseMoveBlocks (sectionD ++ sectionA) (Frames.snapshot Frames.initialRefs)).1
    let after := (phaseMoveBlocks (sectionB ++ sectionC) (Frames.scatterFinish Frames.beforeScatter)).1
    let edges := Geometry.Moves.phaseEdges.filter positiveMove
    ∃ (pre : Fin before.length → MoveIndex) (post : Fin after.length → MoveIndex),
      (∀ i, (pre i).val = i.val ∧ edges[pre i] = before[i].2) ∧
      (∀ i, (post i).val = before.length+i.val ∧ edges[post i] = after[i].2) :=
  appendMoveIndices _ _ _ invocationMoveBlocks_order

/-- Apply one scalar gate on the selected owners at every address. -/
noncomputable def scalarOwnerEffect {k V : ℕ} (owner : Fin 661 ↪ Fin k)
    (x : Fin k → Fin V → ZMod 2) (g : RawGate) (i : Fin k) : Fin V → ZMod 2 := by
  classical
  exact if h : ∃ j, owner j = i then fun a =>
    g.toCircuit.run (Copy.extendStored (fun j => x (owner j) a)) h.choose.val else x i

theorem scalarOwnerEffect_at {k V : ℕ} (owner : Fin 661 ↪ Fin k) (x : Fin k → Fin V → ZMod 2) g j a :
    scalarOwnerEffect owner x g (owner j) a = g.toCircuit.run (Copy.extendStored (fun j => x (owner j) a)) j.val := by
  unfold scalarOwnerEffect
  rw [dite_eq_left (show ∃ l, owner l = owner j from ⟨j,rfl⟩)]
  rw [owner.injective (Exists.choose_spec (show ∃ l, owner l = owner j from ⟨j,rfl⟩))]

/-- Compile a scalar block once for every positive owner volume. -/
theorem scalarOwnerBlock {k : ℕ} (owner : Fin 661 ↪ Fin k) :
    ∃ states, ∀ {Q : ℕ} {U : Type}, states ≤ Q →
    let fan := Function.Embedding.refl (Fin (k+2))
    ∀ gates : List RawGate, (∀ g ∈ gates, g ∈ program) →
      ∃ (code : Pr Empty (k+2) Q prime U) (rate : ℕ), ∀ {V : ℕ}, 0 < V → ∀ (x : Fin k → Fin V → ZMod 2) u S, HelperFan fan x S →
        ∃ z F n, Exec Empty.elim code (mk u S) n (mk z F) ∧
          n ≤ (gates.map (fun g => 76*g.toCircuit.terms.length*V*(k+7)+6)).sum+1 ∧
          (∀ js : List (Fin (k+2)), js.Nodup → n+tapeCharge (fun l r => 4*l.length+2*r.length+4) js F ≤
            tapeCharge (fun l r => 4*l.length+2*r.length+4) js S+rate*((gates.map (fun g => 76*g.toCircuit.terms.length*V*(k+7)+6)).sum+1)) ∧
          z.user = u.user ∧ HelperFan fan (gates.foldl (scalarOwnerEffect owner) x) F := by
  classical
  obtain ⟨states,build⟩ := scheduledGates_host owner
  refine ⟨states,?_⟩
  intro Q U capacity fan gates included
  suffices compiled :
      ∃ code : Pr Empty (k+2) Q prime U, ∀ {V : ℕ}, 0 < V → ∀ (x : Fin k → Fin V → ZMod 2) u S, HelperFan fan x S →
        ∃ z F n, Exec Empty.elim code (mk u S) n (mk z F) ∧
          n ≤ (gates.map (fun g => 76*g.toCircuit.terms.length*V*(k+7)+6)).sum+1 ∧
          z.user = u.user ∧ HelperFan fan (gates.foldl (scalarOwnerEffect owner) x) F by
    obtain ⟨code,run⟩ := compiled
    let push := Fast.Main.mnProgPush code
    refine ⟨code,1+6*push,?_⟩
    intro V pos x u S live
    obtain ⟨z,F,n,exec,time,user,done⟩ := run pos x u S live
    refine ⟨z,F,n,exec,time,?_,user,done⟩
    intro js unique
    have growth := recordCleanup_cost_le js unique exec (c := push) le_rfl (fun e => nomatch e)
    let stock := tapeCharge (fun (l r : List (Fin (prime+4))) => 4*l.length+2*r.length+4) js
    change stock F+1 ≤ stock S+1+6*(push*n) at growth
    change n+stock F ≤ stock S+(1+6*push)*_
    apply le_trans _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ time) _)
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc]
    omega
  induction gates with
  | nil => exact ⟨.act .done,fun {_} _ x u S live => ⟨u,S,1,Exec.act _ _,by simp,rfl,live⟩⟩
  | cons g gs ih =>
    obtain ⟨code,one⟩ := build (P := Empty) (U := U) capacity fan Empty.elim g (included _ (by simp))
    obtain ⟨tail,rest⟩ := ih (fun h hm => included h (List.mem_cons_of_mem _ hm))
    refine ⟨code.seq tail,?_⟩
    intro V pos x u S live
    obtain ⟨v,D,n,y,run,paid,user,ready,keep,update⟩ := one pos (fun _ => True) (by intros; trivial) x u S ⟨live,trivial⟩
    have eq : y = scalarOwnerEffect owner x g := by
      funext i
      by_cases h : ∃ j, owner j = i
      · obtain ⟨j,rfl⟩ := h
        exact funext fun a => (update j a).trans (scalarOwnerEffect_at owner x g j a).symm
      · have off j := fun eq => h (Exists.intro j eq)
        exact by simpa only [scalarOwnerEffect,dite_eq_right h] using keep i off
    obtain ⟨z,F,m,exec,cost,same,out⟩ := rest pos (scalarOwnerEffect owner x g) v D (eq ▸ ready.1)
    exact ⟨z,F,_,Exec.seq run exec,by simp only [List.map_cons,List.sum_cons]; omega,same.trans user,by simpa only [List.foldl_cons] using out⟩

/-- The private tapes of an occurrence still contain its initial stock,
outside the shared owner and cutoff bank. -/
def PrivateTapes {k T : ℕ} (owner : Fin k ↪ Fin T) (seed S : Stacks T prime) : Prop :=
  ∀ j, (∀ i, owner i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j

/-- Run a scalar gate block on the shared owners before a MOVE. The MOVE
sees the gate output and the original private seed. -/
theorem moveAfterOwnerGates {α P U : Type} {T owners Q : ℕ}
    (body : P → Pr P T Q prime U) (owner : Fin owners ↪ Fin T)
    (gates : Pr Empty owners Q prime U) (move : Pr P T Q prime U)
    (rep : α → Stacks owners prime → Prop) (gateEffect moveEffect : α → α)
    (gateBudget moveBudget : ℕ) (seed : Stacks T prime)
    (gateRun : ∀ x u S, rep x S → ∃ z F n, Exec Empty.elim gates (mk u S) n (mk z F) ∧
      CleanupBound S F n (gateBudget) ∧ z.user = u.user ∧ rep (gateEffect x) F)
    (moveRun : ∀ x u S, rep x (embStk owner S) → PrivateTapes owner seed S →
      ∃ z F n, Exec body move (mk u S) n (mk z F) ∧ CleanupBound S F n (moveBudget) ∧
        z.user = u.user ∧ rep (moveEffect x) (embStk owner F)) :
    ∀ x u S, rep x (embStk owner S) → PrivateTapes owner seed S →
      ∃ z F n, Exec body ((embProg owner Empty.elim gates).seq move) (mk u S) n (mk z F) ∧
        CleanupBound S F n (gateBudget+moveBudget) ∧ z.user = u.user ∧ rep (moveEffect (gateEffect x)) (embStk owner F) := by
  intro x u S live stock
  obtain ⟨v,D,n,run,paid,user,next⟩ := gateRun x (embDn owner u) (embStk owner S) live
  obtain ⟨q,G,placed,_,same,view,off⟩ := exec_emb (body' := body) (ι := Empty.elim) owner.injective
    (fun f => nomatch f) run u rfl S rfl
  obtain ⟨z,F,m,exec,cost,final,out⟩ := moveRun (gateEffect x) q G (view ▸ next)
    (fun j outside => ⟨(off j outside).1.trans (stock j outside).1, (off j outside).2.trans (stock j outside).2⟩)
  rw [← view] at paid
  exact ⟨z,F,_,Exec.seq placed exec,(CleanupBound.place owner off paid).seq cost,final.trans (same.trans user),out⟩

/-- Allocate the MOVE occurrences together. Their owner tapes coincide;
all not-yet-run occurrences retain their seed across an embedded call. -/
theorem allocateMoveStock {I : Type} [Fintype I] {owners : ℕ} (tapes : I → ℕ)
    (owner : ∀ i, Fin owners ↪ Fin (tapes i)) :
    ∃ (T : ℕ) (fan : Fin owners ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
      (∀ i j, bank i (owner i j) = fan j) ∧
      ∀ seed : ∀ i, Stacks (tapes i) prime,
      let ready := fun i (S : Stacks T prime) => PrivateTapes (owner i) (seed i) (embStk (bank i) S)
      (∀ shared, ∃ S, embStk fan S = shared ∧ ∀ i, ready i S) ∧
      ∀ {P U : Type} {Q : ℕ} (body : ∀ i, P → Pr P (tapes i) Q prime U) i code u S z F n,
        Exec (body i) code (mk (embDn (bank i) u) (embStk (bank i) S)) n (mk z F) →
        let host := fun f : I × P => embProg (bank f.1) (Prod.mk f.1) (body f.1 f.2)
        ∃ v G, Exec host (embProg (bank i) (Prod.mk i) code) (mk u S) n (mk v G) ∧
          v.user = z.user ∧ embStk (bank i) G = F ∧ (∀ j, (∀ h, bank i h ≠ j) → G.L j = S.L j ∧ G.R j = S.R j) ∧ ∀ j, j ≠ i → ready j S → ready j G := by
  obtain ⟨T,fan,bank,shared,join,apart⟩ := copyWindowBanks tapes owner
  refine ⟨T,fan,bank,shared,?_⟩
  intro seed ready
  constructor
  · intro X
    obtain ⟨S,view,loaded⟩ := join X seed
    exact ⟨S,view,loaded⟩
  · intro P U Q body i code u S z F n run host
    obtain ⟨v,G,exec,_,user,view,off⟩ := exec_emb (body' := host) (ι := Prod.mk i) (bank i).injective
      (fun _ => rfl) run u rfl S rfl
    refine ⟨v,G,exec,user,view,off,?_⟩
    intro j ne stock
    have keep (k : Fin (tapes j)) (outside : ∀ h, owner j h ≠ k) := off (bank j k) ((apart j k outside).2 i ne.symm)
    exact fun k outside => ⟨(keep k outside).1.trans (stock k outside).1, (keep k outside).2.trans (stock k outside).2⟩

/-- Sequence allocated MOVE calls in the supplied order. Only occurrences
remaining in the list need their private seed. The shared owner state follows
the same left fold, and each local execution budget is charged once. -/
theorem moveStockSequence {I P U : Type} [Fintype I] {owners Q : ℕ} (tapes : I → ℕ)
    (owner : ∀ i, Fin owners ↪ Fin (tapes i))
    (body : ∀ i, P → Pr P (tapes i) Q prime U) (code : ∀ i, Pr P (tapes i) Q prime U)
    (gates : I → Pr Empty owners Q prime U) (lastGates : Pr Empty owners Q prime U) (order : List I) (distinct : order.Nodup) :
    ∃ (T : ℕ) (fan : Fin owners ↪ Fin T) (host : I × P → Pr (I × P) T Q prime U)
      (program : Pr (I × P) T Q prime U),
    ∀ {α : Type} (rep : α → Stacks owners prime → Prop) (gateStep step : α → I → α) (lastStep : α → α) (gateBudget budget : I → ℕ) (lastBudget : ℕ)
      (seed : ∀ i, Stacks (tapes i) prime),
    (∀ x u S, rep x S → ∃ z F n, Exec Empty.elim lastGates (mk u S) n (mk z F) ∧
      CleanupBound S F n (lastBudget) ∧ z.user = u.user ∧ rep (lastStep x) F) →
    (∀ i ∈ order, ∀ x u S, rep x S → ∃ z F n, Exec Empty.elim (gates i) (mk u S) n (mk z F) ∧
      CleanupBound S F n (gateBudget i) ∧ z.user = u.user ∧ rep (gateStep x i) F) →
    (∀ i ∈ order, ∀ x u S, rep x (embStk (owner i) S) → PrivateTapes (owner i) (seed i) S →
      ∃ z F n, Exec (body i) (code i) (mk u S) n (mk z F) ∧ CleanupBound S F n (budget i) ∧ z.user = u.user ∧
        rep (step x i) (embStk (owner i) F)) →
    ∀ shared, ∃ S, embStk fan S = shared ∧ ∀ x u, rep x shared →
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧ CleanupBound S F n ((order.map fun i => gateBudget i+budget i).sum+lastBudget) ∧
        z.user = u.user ∧ rep (lastStep (order.foldl (fun x i => step (gateStep x i) i) x)) (embStk fan F) := by
  obtain ⟨T,fan,bank,shared,allocate⟩ := allocateMoveStock tapes owner
  let host := fun f : I × P => embProg (bank f.1) (Prod.mk f.1) (body f.1 f.2)
  let block := fun i => (embProg (owner i) Empty.elim (gates i)).seq (code i)
  let seq := fun (is : List I) => is.foldr (fun i tail => (embProg (bank i) (Prod.mk i) (block i)).seq tail) (embProg fan Empty.elim lastGates)
  refine ⟨T,fan,host,seq order,?_⟩
  intro α rep gateStep step lastStep gateBudget budget lastBudget seed lastRun gateRun localRun X
  obtain ⟨join,place⟩ := allocate seed
  obtain ⟨S,view,stock⟩ := join X
  refine ⟨S,view,?_⟩
  intro x u live
  rw [← view] at live
  have project (i) (D : Stacks T prime) : embStk (owner i) (embStk (bank i) D) = embStk fan D := by
    simp only [embStk,Function.comp_def,shared]
  have ready (i) (_ : i ∈ order) := stock i
  clear stock view
  induction order generalizing u S x with
  | nil =>
    obtain ⟨z,F,n,run,cost,user,out⟩ := lastRun x (embDn fan u) (embStk fan S) live
    obtain ⟨v,G,placed,_,same,view,off⟩ := exec_emb (body' := host) (ι := Empty.elim) fan.injective
      (fun f => nomatch f) run u rfl S rfl
    rw [← view] at cost
    exact ⟨v,G,n,placed,by simpa using CleanupBound.place fan off cost,same.trans user,view ▸ out⟩
  | cons i rest ih =>
    obtain ⟨fresh,nodup⟩ := List.nodup_cons.mp distinct
    obtain ⟨z,F,n,run,cost,user,next⟩ := moveAfterOwnerGates (body i) (owner i) (gates i) (code i) rep (fun x => gateStep x i) (fun x => step x i)
      (gateBudget i) (budget i) (seed i) (gateRun i (by simp)) (localRun i (by simp)) x (embDn (bank i) u) (embStk (bank i) S)
      (by rwa [project]) (ready i (by simp))
    obtain ⟨v,D,placed,same,returned,off,kept⟩ := place body i (block i) u S z F n run
    rw [← returned] at cost
    rw [← returned,project] at next
    obtain ⟨q,G,m,tail,paid,final,out⟩ := ih nodup (fun j hj => gateRun j (List.mem_cons_of_mem _ hj)) (fun j hj => localRun j (List.mem_cons_of_mem _ hj))
      D (step (gateStep x i) i) v next (fun j hj => kept j (fun eq => fresh (eq ▸ hj)) (ready j (List.mem_cons_of_mem _ hj)))
    exact ⟨q,G,_,Exec.seq placed tail,by simpa only [List.map_cons,List.sum_cons,Nat.add_assoc] using (CleanupBound.place (bank i) off cost).seq paid,final.trans (same.trans user),out⟩

private theorem sumScaled {α : Type} (xs : List α) (f g : α → ℕ) (V : ℕ)
    (bound : ∀ i, f i ≤ g i*V) : (xs.map f).sum ≤ (xs.map g).sum*V := by
  induction xs with
  | nil => simp
  | cons i xs ih => simpa only [List.map_cons,List.sum_cons,Nat.add_mul] using Nat.add_le_add (bound i) ih

/-- A fixed phase program with a linear scalar charge and one budget per MOVE. -/
def ScalarPhaseExecution (P U : Type) {k : ℕ} (layout : Fin 661 ↪ Fin k)
    (gs : List RawGate) (current : ℕ → ℕ)
    (tapes : Fin (phaseMoveBlocks gs current).1.length → ℕ) (owner : ∀ i, Fin (k+2+1) ↪ Fin (tapes i)) : Prop :=
    let schedule := phaseMoveBlocks gs current
    let I := Fin schedule.1.length
    let blocks := fun i : I => schedule.1[i].1
    let suffix := schedule.2
    let order := List.finRange schedule.1.length
    ∃ states, ∀ {Q : ℕ}, states ≤ Q →
    ∀ (body : ∀ i, P → Pr P (tapes i) Q prime U) (move : ∀ i, Pr P (tapes i) Q prime U),
    ∃ T fan host code, ∃ overhead : ℕ, ∀ {V : ℕ}, 0 < V →
    let dataBank := Fin.castAddEmb 1 (n := k+2)
    let rep := fun word (x : Fin k → Fin V → ZMod 2) (S : Stacks (k+2+1) prime) =>
      HelperFan dataBank x S ∧ S.R (Fin.last (k+2)) = word
    ∀ word start (step : (Fin k → Fin V → ZMod 2) → ℕ → ℕ × ℕ → Fin k → Fin V → ZMod 2) (budget : I → ℕ) (seed : ∀ i, Stacks (tapes i) prime),
      (∀ i, ∀ x u S, rep word x (embStk (owner i) S) → PrivateTapes (owner i) (seed i) S →
        ∃ z F n, Exec (body i) (move i) (mk u S) n (mk z F) ∧ CleanupBound S F n (budget i) ∧ z.user = u.user ∧ rep word (step x (start+i.val) schedule.1[i.val].2) (embStk (owner i) F)) →
      ∀ shared, ∃ S : Stacks T prime, embStk fan S = shared ∧ ∀ x u, rep word x shared →
        ∃ z F n, Exec (host : I × P → Pr (I × P) T Q prime U) code (mk u S) n (mk z F) ∧
          CleanupBound S F n (overhead*V+(order.map budget).sum) ∧ z.user = u.user ∧
          rep word (runIndexedPhase (scalarOwnerEffect layout) step gs current x start) (embStk fan F)

open Certificates.PR589 in
/-- Execute PR589 scalar blocks interleaved with MOVE occurrences, including
the scalar suffix after the last MOVE. Only the MOVE executions are premises. -/
theorem scalarMoveSequence {P U : Type} {k : ℕ} (layout : Fin 661 ↪ Fin k)
    (gs : List RawGate) (current : ℕ → ℕ) (allowed : ∀ g ∈ gs, g ∈ program)
    (tapes : Fin (phaseMoveBlocks gs current).1.length → ℕ) (owner : ∀ i, Fin (k+2+1) ↪ Fin (tapes i)) :
    ScalarPhaseExecution P U layout gs current tapes owner := by
  classical
  let schedule := phaseMoveBlocks gs current
  unfold ScalarPhaseExecution
  intro _ I blocks suffix order
  obtain ⟨states,build⟩ := scalarOwnerBlock layout
  refine ⟨states,?_⟩
  intro Q capacity
  have compile := build (U := U) capacity
  intro body move
  obtain ⟨blockAllowed,lastAllowed⟩ := phaseMoveBlocks_allowed gs current allowed
  choose gates rate runs using fun i => compile (blocks i) (blockAllowed i)
  obtain ⟨last,lastRate,lastRun⟩ := compile suffix lastAllowed
  let dataBank := Fin.castAddEmb 1 (n := k+2)
  let lift : Pr Empty (k+2) Q prime U → Pr Empty (k+2+1) Q prime U := embProg dataBank (id : Empty → Empty)
  obtain ⟨T,fan,host,code,run⟩ := moveStockSequence tapes owner body move (fun i => lift (gates i)) (lift last) order (List.nodup_finRange _)
  let bill := fun V (gs : List RawGate) => (gs.map fun g => 76*g.toCircuit.terms.length*V*(k+7)+6).sum+1
  let overhead := (order.map fun i => rate i*bill 1 (blocks i)).sum+lastRate*bill 1 suffix
  refine ⟨T,fan,host,code,overhead,?_⟩
  intro V pos _ rep
  have keep {g : Pr Empty (k+2) Q prime U} {x y : Fin k → Fin V → ZMod 2} {cost : ℕ}
      (localRun : ∀ u S, HelperFan (Function.Embedding.refl _) x S →
        ∃ z F n, Exec Empty.elim g (mk u S) n (mk z F) ∧ CleanupBound S F n cost ∧ z.user = u.user ∧
          HelperFan (Function.Embedding.refl _) y F) :
      ∀ word u S, rep word x S → ∃ z F n, Exec Empty.elim (lift g) (mk u S) n (mk z F) ∧
        CleanupBound S F n cost ∧ z.user = u.user ∧ rep word y F := by
    intro word u S live
    obtain ⟨v,D,n,run,paid,user,out⟩ := localRun (embDn dataBank u) (embStk dataBank S) live.1
    obtain ⟨z,F,placed,_,same,view,frame⟩ := exec_emb (body' := Empty.elim) (ι := id) dataBank.injective
      (fun f => nomatch f) run u rfl S rfl
    have away (i : Fin (k+2)) : dataBank i ≠ Fin.last (k+2) := by
      intro eq
      exact by have h := congrArg Fin.val eq; exact i.isLt.ne h
    rw [← view] at paid
    refine ⟨z,F,n,placed,CleanupBound.place dataBank frame paid,same.trans user,?_,(frame _ away).2.trans live.2⟩
    change HelperFan (Function.Embedding.refl _) y (embStk dataBank F)
    exact view ▸ out
  have scale (gs : List RawGate) : bill V gs ≤ bill 1 gs*V := by
    unfold bill
    rw [Nat.add_mul,Nat.one_mul]
    apply Nat.add_le_add _ pos
    apply sumScaled
    intro g
    simp only [Nat.mul_one,Nat.add_mul]
    nlinarith only [pos]
  intro word start step budget seed moves shared
  obtain ⟨S,view,execute⟩ := run (rep word) (fun x i => (blocks i).foldl (scalarOwnerEffect layout) x) (fun x i => step x (start+i.val) schedule.1[i.val].2) (fun x => suffix.foldl (scalarOwnerEffect layout) x)
    (fun i => rate i*bill V (blocks i)) budget (lastRate*bill V suffix) seed (fun x => keep (fun u S h => by
      obtain ⟨z,F,n,exec,_,paid,user,out⟩ := lastRun pos x u S h
      exact ⟨z,F,n,exec,paid,user,out⟩) word) (fun i _ x => keep (fun u S h => by
      obtain ⟨z,F,n,exec,_,paid,user,out⟩ := runs i pos x u S h
      exact ⟨z,F,n,exec,paid,user,out⟩) word) (fun i _ => moves i) shared
  refine ⟨S,view,?_⟩
  intro x u live
  obtain ⟨z,F,n,exec,paid,user,out⟩ := execute x u live
  rw [← indexedPhase_fold]
  refine ⟨z,F,n,exec,?_,user,out⟩
  have scaled (r : ℕ) (gs : List RawGate) : r*bill V gs ≤ (r*bill 1 gs)*V := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left r (scale gs)
  have localBound := sumScaled order _ _ V (fun i => scaled (rate i) (blocks i))
  intro js distinct
  have charge := paid js distinct
  rw [List.sum_map_add] at charge
  dsimp only [overhead]
  rw [Nat.add_mul]
  apply charge.trans
  apply Nat.add_le_add_left
  rw [Nat.add_right_comm _ (order.map budget).sum]
  exact Nat.add_le_add_right (Nat.add_le_add localBound (scaled lastRate suffix)) _

/-- Phase programs indexed by one ordered MOVE directory, split at COPY. -/
def IndexedScalarPhases (P U : Type) {k : ℕ} (layout : Fin 661 ↪ Fin k)
    (gs hs : List RawGate) (cur next : ℕ → ℕ) (edges : List (ℕ × ℕ))
    (tapes : Fin edges.length → ℕ) (owner : ∀ i, Fin (k+2+1) ↪ Fin (tapes i)) : Prop :=
    let before := phaseMoveBlocks gs cur
    let after := phaseMoveBlocks hs next
    ∃ (pre : Fin before.1.length → Fin edges.length) (post : Fin after.1.length → Fin edges.length),
      (∀ i, (pre i).val = i.val ∧ edges[pre i] = before.1[i].2) ∧
      (∀ i, (post i).val = before.1.length+i.val ∧ edges[post i] = after.1[i].2) ∧
      ScalarPhaseExecution P U layout gs cur (tapes ∘ pre) (fun i => owner (pre i)) ∧
      ScalarPhaseExecution P U layout hs next (tapes ∘ post) (fun i => owner (post i))

private theorem scalarPhasePair (P U : Type) {k : ℕ} (layout : Fin 661 ↪ Fin k)
    (gs hs : List RawGate) (cur next : ℕ → ℕ) (edges : List (ℕ × ℕ))
    (ordered : ((phaseMoveBlocks gs cur).1 ++ (phaseMoveBlocks hs next).1).map Prod.snd = edges)
    (leftAllowed : ∀ g ∈ gs, g ∈ program) (rightAllowed : ∀ g ∈ hs, g ∈ program)
    (tapes : Fin edges.length → ℕ) (owner : ∀ i, Fin (k+2+1) ↪ Fin (tapes i)) :
    IndexedScalarPhases P U layout gs hs cur next edges tapes owner := by
  obtain ⟨pre,post,left,right⟩ := appendMoveIndices _ _ edges ordered
  unfold IndexedScalarPhases
  exact ⟨pre,post,left,right,scalarMoveSequence layout gs cur leftAllowed _ _,
    scalarMoveSequence layout hs next rightAllowed _ _⟩

/-- Both sides of the selected COPY use the MOVE banks at their positions in
the same invocation directory. -/
theorem invocationScalarPhases (P U : Type) {k : ℕ} (layout : Fin 661 ↪ Fin k)
    (tapes : MoveIndex → ℕ) (owner : ∀ i, Fin (k+2+1) ↪ Fin (tapes i)) :
    IndexedScalarPhases P U layout
      (sectionD++sectionA) (sectionB++sectionC) (Frames.snapshot Frames.initialRefs)
      (Frames.scatterFinish Frames.beforeScatter)
      (Geometry.Moves.phaseEdges.filter positiveMove) tapes owner := by
  have included {α : Type} (x y z t : List α) :
      (∀ g ∈ x, g ∈ x++y++z++t) ∧ (∀ g ∈ z++t, g ∈ x++y++z++t) := by
    constructor
    · exact fun _ h => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))
    · intro g h
      rcases List.mem_append.mp h with hz | ht
      · exact List.mem_append_left _ (List.mem_append_right _ hz)
      · exact List.mem_append_right _ ht
  have membership := included (sectionD++sectionA) sectionscatter sectionB sectionC
  exact scalarPhasePair P U layout (sectionD++sectionA) (sectionB++sectionC)
    (Frames.snapshot Frames.initialRefs) (Frames.scatterFinish Frames.beforeScatter)
    (Geometry.Moves.phaseEdges.filter positiveMove) invocationMoveBlocks_order membership.1 membership.2 tapes owner

end IntegerMultBounds.MathlibTM2.M6.BitNode
