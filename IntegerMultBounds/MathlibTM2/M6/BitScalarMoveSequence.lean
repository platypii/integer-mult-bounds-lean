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

private theorem foldLastOccurrence {α : Type*} {n : ℕ} (pos : 0 < n) (step : α → Fin n → α)
    (finish : α → α) (x : α) :
    (List.finRange n).foldl (fun y i => if i.val+1 = n then finish (step y i) else step y i) x =
      finish ((List.finRange n).foldl step x) := by
  cases n with
  | zero => omega
  | succ n =>
    have earlier (i : Fin n) : i.val ≠ n := i.isLt.ne
    simp [List.finRange_succ_last,List.foldl_map,earlier]

/-- When a phase has a MOVE, its last worker can execute the scalar suffix
before returning, with exactly the effect of the literal phase. -/
theorem indexedPhase_lastSuffix {α : Type*} (gate : α → RawGate → α) (move : α → ℕ → ℕ × ℕ → α)
    (gs : List RawGate) (current : ℕ → ℕ) (x : α) (start : ℕ) :
    let schedule := phaseMoveBlocks gs current
    let blocks := schedule.1
    0 < blocks.length →
    (List.finRange blocks.length).foldl (fun y i =>
      let z := move (blocks[i.val].1.foldl gate y) (start+i.val) blocks[i.val].2
      (if i.val+1 = blocks.length then schedule.2 else []).foldl gate z) x =
      runIndexedPhase gate move gs current x start := by
  intro schedule blocks pos
  rw [← indexedPhase_fold]
  convert foldLastOccurrence pos (fun y (i : Fin blocks.length) =>
    move (blocks[i.val].1.foldl gate y) (start+i.val) blocks[i.val].2) (schedule.2.foldl gate ·) x using 1
  congr 1
  funext y i
  split <;> simp_all

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

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- A paid MOVE acts on one register and carries its spectator index unchanged. -/
noncomputable def moveOwnerEffect {k w W : ℕ} (owner : Fin 661 ↪ Fin k)
    (x : Fin k → Fin ((prime^w)^16*W) → ZMod 2) (i : ℕ) (p : ℕ × ℕ) :=
  let r := owner (paidRegister i)
  Function.update x r (fun a => let (s,j) := copyAddress a
    x r (copyAddress.symm (AffineFieldProgram.run (selectedWord w p) s,j)))

/-- The coordinate relation returned by the MOVE machine determines its entire
output word, including when two occurrences use the same register. -/
theorem moveOwnerEffect_of_exec {k w W : ℕ} (owner : Fin 661 ↪ Fin k)
    (x : Fin k → Fin ((prime^w)^16*W) → ZMod 2) (i : ℕ) (p : ℕ × ℕ)
    (checked : Geometry.Moves.CheckedPair p) (y : Fin ((prime^w)^16*W) → ZMod 2)
    (reads : ∀ s j, y (copyAddress.symm (AffineFieldProgram.run (selectedWord w p) s,j)) =
      x (owner (paidRegister i)) (copyAddress.symm (s,j))) :
    Function.update x (owner (paidRegister i)) y = moveOwnerEffect owner x i p := by
  unfold moveOwnerEffect
  congr 1
  funext a
  obtain ⟨⟨s,j⟩,rfl⟩ := copyAddress.symm.surjective a
  simp only [Equiv.apply_symm_apply]
  simpa only [(modular_scatter w).choose_spec.2.1 p checked s] using
    reads (AffineFieldProgram.run (selectedWord w p) s) j

theorem phaseRead_moveOwnerEffect {k w W : ℕ} (owner : Fin 661 ↪ Fin k)
    (x : Fin k → Fin ((prime^w)^16*W) → ZMod 2) (i : ℕ) (p : ℕ × ℕ) (j : Fin W) :
    phaseRead owner (moveOwnerEffect owner x i p) j =
      Function.update (phaseRead owner x j) (paidRegister i).val
        (fun s => phaseRead owner x j (paidRegister i).val (AffineFieldProgram.run (selectedWord w p) s)) := by
  apply phaseRead_edge owner (paidRegister i) p x _ (fun r h => Function.update_of_ne h ..) _ j
  intro s l
  simp only [moveOwnerEffect,Function.update_self,← copyAddress_index,Equiv.apply_symm_apply]

/-- Reading one spectator commutes with the complete physical phase. -/
theorem phaseRead_indexedPhase {k w W : ℕ} (owner : Fin 661 ↪ Fin k)
    (gs : List RawGate) (current : ℕ → ℕ) (allowed : ∀ g ∈ gs, g ∈ program)
    (x : Fin k → Fin ((prime^w)^16*W) → ZMod 2) (start : ℕ) (j : Fin W) :
    phaseRead owner (runIndexedPhase (scalarOwnerEffect owner) (moveOwnerEffect owner) gs current x start) j =
      runIndexedPhase (fun bank g => FramedCircuit.moduleGate g.toCircuit bank)
        (fun (bank : ℕ → AddressStream (ZMod (prime^w))) i p => Function.update bank (paidRegister i).val
          (fun s => bank (paidRegister i).val (AffineFieldProgram.run (selectedWord w p) s)))
        gs current (phaseRead owner x j) start := by
  rw [← indexedPhase_fold,← indexedPhase_fold]
  let read := fun data => phaseRead (w := w) owner data j
  have gates (hs : List RawGate) (ok : ∀ g ∈ hs, g ∈ program) (data) :
      read (hs.foldl (scalarOwnerEffect owner) data) =
        hs.foldl (fun bank g => FramedCircuit.moduleGate g.toCircuit bank) (read data) := by
    induction hs generalizing data with
    | nil => rfl
    | cons g hs ih =>
      rw [List.foldl_cons,List.foldl_cons,ih (fun h mem => ok h (List.mem_cons_of_mem _ mem))]
      exact congrArg (fun b => hs.foldl (fun bank (h : RawGate) => FramedCircuit.moduleGate h.toCircuit bank) b) (phaseRead_gate owner g (ok g List.mem_cons_self) data _ (scalarOwnerEffect_at owner data g) j)
  obtain ⟨blocks,suffix⟩ := phaseMoveBlocks_allowed gs current allowed
  change read _ = _
  rw [gates _ suffix]
  apply congrArg (fun b => (phaseMoveBlocks gs current).2.foldl (fun bank g => FramedCircuit.moduleGate g.toCircuit bank) b)
  symm
  apply List.foldl_hom read
  intro data i
  dsimp only [read]
  rw [phaseRead_moveOwnerEffect]
  exact congrArg (fun (bank : ℕ → AddressStream (ZMod (prime^w))) =>
    Function.update bank (paidRegister (start+i.val)).val (fun s => bank (paidRegister (start+i.val)).val
      (AffineFieldProgram.run (selectedWord w (phaseMoveBlocks gs current).1[i.val].2) s))) (gates _ (blocks i) data).symm

/-- All other invocations' owner words survive the phase. -/
theorem indexedPhase_off_owner {k w W : ℕ} (owner : Fin 661 ↪ Fin k)
    (gs : List RawGate) (current : ℕ → ℕ) (x : Fin k → Fin ((prime^w)^16*W) → ZMod 2)
    (start : ℕ) (r : Fin k) (outside : ∀ i, owner i ≠ r) :
    runIndexedPhase (scalarOwnerEffect owner) (moveOwnerEffect owner) gs current x start r = x r := by
  have fixed {α β : Type} (read : α → β) {γ : Type} (step : α → γ → α)
      (same : ∀ x g, read (step x g) = read x) (gs : List γ) (x : α) :
      read (gs.foldl step x) = read x := by
    induction gs generalizing x with
    | nil => rfl
    | cons g gs ih => exact (ih (step x g)).trans (same x g)
  let read := fun (data : Fin k → Fin ((prime^w)^16*W) → ZMod 2) => data r
  have gates := fixed read (scalarOwnerEffect owner) (fun data g => by
    simp only [read,scalarOwnerEffect,dite_eq_right (show ¬ ∃ i, owner i = r from fun ⟨i,h⟩ => outside i h)])
  rw [← indexedPhase_fold]
  change read _ = read x
  rw [gates]
  apply fixed
  intro data i
  exact (Function.update_of_ne (outside (paidRegister (start+i.val))).symm ..).trans (gates _ data)

private def phaseAligned (start : ℕ) (edges : List (ℕ × ℕ)) (registers : List ℕ) : Prop :=
  ∀ pre p post, edges = pre ++ p :: post → positiveMove p = true →
    registers[pre.length]? = some (paidRegister (start+(pre.filter positiveMove).length)).val

private noncomputable def readMove (w : ℕ) (bank : ℕ → AddressStream (ZMod (prime^w)))
    (i : ℕ) (p : ℕ × ℕ) :=
  Function.update bank (paidRegister i).val
    (fun x => bank (paidRegister i).val (AffineFieldProgram.run (selectedWord w p) x))

private def nextMove {α : Type*} (move : α → ℕ → ℕ × ℕ → α) (s : α × ℕ) (p : ℕ × ℕ) :=
  (move s.1 s.2 p,s.2+1)

/-- Align all incidences in order. A repeated wire uses the frame left by its
previous incidence, including when that edge has zero rank. -/
private theorem alignFrameReads (w : ℕ) (updates : List (ℕ × ℕ)) (current : ℕ → ℕ)
    (x : ℕ → AddressStream (ZMod (prime^w))) (start : ℕ) :
    let edges := RankTrace.edges current updates
    (∀ p ∈ edges, Geometry.Moves.CheckedPair p) → phaseAligned start edges (updates.map Prod.fst) →
    (edges.filter positiveMove).foldl (nextMove (readMove w))
      (FramedCircuit.encode (fun i => selectedFrame w (current i)) x,start) =
      (FramedCircuit.encode (fun i => selectedFrame w (RankTrace.finish current updates i)) x,
       start+(edges.filter positiveMove).length) := by
  induction updates generalizing current start with
  | nil => intro _ _ _; rfl
  | cons u us ih =>
    obtain ⟨r,next⟩ := u
    intro edges checked aligned
    let p := (current r,next)
    let cur := Function.update current r next
    let tail := RankTrace.edges cur us
    change ∀ q ∈ p :: tail, _ at checked
    change phaseAligned start (p :: tail) (r :: us.map Prod.fst) at aligned
    have valid := checked p List.mem_cons_self
    have after : Function.update (FramedCircuit.encode (fun i => selectedFrame w (current i)) x) r
          (fun s => selectedFrame w (current r) (x r) (AffineFieldProgram.run (selectedWord w p) s)) =
        FramedCircuit.encode (fun i => selectedFrame w (cur i)) x := by
      rw [(modular_scatter w).choose_spec.1 p valid]
      funext i
      by_cases h : i = r
      · subst i
        simp [p,cur,FramedCircuit.encode,selectedFrame]
      · simp [FramedCircuit.encode,cur,Function.update_of_ne h]
    have rest (n : ℕ) (eq : n = start+(if positiveMove p then 1 else 0)) :
        (tail.filter positiveMove).foldl (nextMove (readMove w))
          (FramedCircuit.encode (fun i => selectedFrame w (cur i)) x,n) = _ :=
      ih cur n (fun q h => checked q (List.mem_cons_of_mem _ h)) (fun pre q post split paid => by
        have h := aligned (p :: pre) q post (congrArg (p :: ·) split) paid
        cases keep : positiveMove p <;> simpa [eq,keep,Nat.add_assoc,Nat.add_comm 1] using h)
    change ((p :: tail).filter positiveMove).foldl _ _ = (_,start+((p :: tail).filter positiveMove).length)
    rw [RankTrace.finish]
    cases keep : positiveMove p with
    | false =>
      have zero : Geometry.moveRank p.1 p.2 = 0 := by simpa [positiveMove] using keep
      have idMove := (modular_scatter w).choose_spec.2.2.1.zero p valid zero
      simp only [idMove] at after
      have same : FramedCircuit.encode (fun i => selectedFrame w (current i)) x =
          FramedCircuit.encode (fun i => selectedFrame w (cur i)) x := by
        convert after using 1
        exact (Function.update_eq_self ..).symm
      simpa only [List.filter_cons_of_neg (by simp [keep] : ¬ positiveMove p = true),same] using
        rest start (by simp [keep])
    | true =>
      have reg := aligned [] p tail rfl keep
      simp only [List.length_nil,List.getElem?_cons_zero,List.filter_nil,Nat.add_zero,Option.some.injEq] at reg
      simp only [List.filter_cons_of_pos keep,List.foldl_cons,List.length_cons,nextMove,readMove,← reg]
      change Function.update (FramedCircuit.encode (fun i => selectedFrame w (current i)) x) r (fun s => FramedCircuit.encode (fun i => selectedFrame w (current i)) x r
        (AffineFieldProgram.run (selectedWord w p) s)) = _ at after
      rw [after]
      simpa only [Nat.add_assoc,Nat.add_comm 1] using rest (start+1) (by simp [keep])

private theorem phaseAligned_append {start : ℕ} {a b : List (ℕ × ℕ)} {rs ss : List ℕ}
    (len : a.length = rs.length) (aligned : phaseAligned start (a++b) (rs++ss)) :
    phaseAligned start a rs ∧ phaseAligned (start+(a.filter positiveMove).length) b ss := by
  constructor
  · intro pre p post split paid
    have h := aligned pre p (post++b) (by simp [split,List.append_assoc]) paid
    rw [List.getElem?_append_left (by rw [← len,split]; simp)] at h
    exact h
  · intro pre p post split paid
    have h := aligned (a++pre) p post (by simp [split,List.append_assoc]) paid
    simp only [List.length_append,List.filter_append] at h
    rw [List.getElem?_append_right (by omega)] at h
    simpa only [len,Nat.add_sub_cancel_left,Nat.add_assoc] using h

private theorem runIndexedPhase_cons {α : Type*} (gate : α → RawGate → α) (move : α → ℕ → ℕ × ℕ → α)
    (g : RawGate) (gs : List RawGate) (current : ℕ → ℕ) (x : α) (start : ℕ) :
    let s := ((Frames.edges [g] current).filter positiveMove).foldl
      (fun (s : α × ℕ) p => (move s.1 s.2 p,s.2+1)) (x,start)
    runIndexedPhase gate move (g::gs) current x start =
      runIndexedPhase gate move gs (Frames.step g current) (gate s.1 g) s.2 := rfl

private theorem phaseRegisterCount (gs : List RawGate) (cur : ℕ → ℕ) :
    (Frames.edges gs cur).length = (gs.flatMap Frames.touched).length := by
  have count (us : List (ℕ × ℕ)) (c : ℕ → ℕ) : (RankTrace.edges c us).length = us.length := by
    induction us generalizing c with
    | nil => rfl
    | cons u us ih => obtain ⟨r,n⟩ := u; simp [RankTrace.edges,ih]
  rw [Frames.edges,count]
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simpa only [Frames.updates,List.flatMap_cons,List.length_append,List.length_map] using
      congrArg ((Frames.touched g).length + ·) ih

private theorem indexedPhase_encode (w : ℕ) (gs : List RawGate) (current : ℕ → ℕ)
    (x : ℕ → AddressStream (ZMod (prime^w))) (start : ℕ)
    (checked : ∀ p ∈ Frames.edges gs current, Geometry.Moves.CheckedPair p)
    (aligned : phaseAligned start (Frames.edges gs current) (gs.flatMap Frames.touched)) :
    runIndexedPhase (fun bank g => FramedCircuit.moduleGate g.toCircuit bank)
      (readMove w)
      gs current (FramedCircuit.encode (fun i => selectedFrame w (current i)) x) start =
      FramedCircuit.encode (fun i => selectedFrame w (Frames.run gs current i))
        (FramedCircuit.moduleRun (gs.map RawGate.toCircuit) x) := by
  induction gs generalizing current x start with
  | nil => rfl
  | cons g gs ih =>
    let es := Frames.edges [g] current
    let cur := Frames.step g current
    have trace : Frames.edges (g :: gs) current = es ++ Frames.edges gs cur := Frames.edges_append [g] gs current
    rw [trace] at checked aligned
    rw [List.flatMap_cons] at aligned
    have size : es.length = (Frames.touched g).length := by
      simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil] using phaseRegisterCount [g] current
    obtain ⟨head,tail⟩ := phaseAligned_append size aligned
    let updates := (Frames.touched g).map fun i => (i,g.frame)
    have eq : es = RankTrace.edges current updates := by simp [es,Frames.edges,Frames.updates,updates]
    have first := alignFrameReads w updates current x start (fun p h => checked p (List.mem_append_left _ (eq.symm ▸ h)))
      (by simpa [updates,List.map_map,Function.comp_def,← eq] using head)
    rw [← eq,← Frames.step_eq_finish] at first
    have gate := FramedCircuit.gate_invariant g.toCircuit (fun i => selectedFrame w (cur i)) (selectedFrame w g.frame)
      (fun i h => by rw [Frames.touched_toCircuit] at h; simp [cur,Frames.step,h]) x
    rw [runIndexedPhase_cons]
    unfold nextMove at first
    simp only [← show es = Frames.edges [g] current from rfl,first]
    dsimp only [cur] at gate
    rw [gate]
    exact ih cur _ _ (fun p h => checked p (List.mem_append_right _ h)) tail

private theorem invocationPhase_allowed (b : Bool) :
    ∀ g ∈ (if b then sectionB++sectionC else sectionD++sectionA), g ∈ program := by
  intro g h
  cases b
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))
  · rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left _ (List.mem_append_right _ h)
    · exact List.mem_append_right _ h

private theorem invocationPhase_aligned (b : Bool) :
    let gs := if b then sectionB++sectionC else sectionD++sectionA
    let cur := if b then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
    let first := Frames.edges (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)
    phaseAligned (if b then (first.filter positiveMove).length else 0) (Frames.edges gs cur)
      (gs.flatMap Frames.touched) := by
  intro gs cur first pre p post split paid
  have hi : pre.length < (gs.flatMap Frames.touched).length := by
    rw [← phaseRegisterCount gs cur,split]; simp
  let r := (gs.flatMap Frames.touched)[pre.length]
  have mem : r ∈ gs.flatMap Frames.touched := List.getElem_mem hi
  obtain ⟨g,hg,hr⟩ := List.mem_flatMap.mp mem
  let j : Fin 661 := ⟨r,Frames.bounded_touched program program_bounded g (invocationPhase_allowed b g hg) r hr⟩
  have lookup : (gs.flatMap Frames.touched)[pre.length]? = some j.val := List.getElem?_eq_getElem hi
  rw [lookup]
  cases b
  · have bound : pre.length < first.length := by change pre.length < (Frames.edges gs cur).length; rw [split]; simp
    simp only [gs,cur,Bool.false_eq_true,ite_false] at split lookup
    have full := congrArg (· ++ Frames.edges (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter)) split
    have eq := paidRegister_at pre p _ (by simpa only [Geometry.Moves.phaseEdges,List.append_assoc,List.cons_append] using full)
      paid j (by unfold invocationRegister; rw [ite_eq_left bound]; exact lookup)
    simp only [Bool.false_eq_true,ite_false,Nat.zero_add,eq]
  · simp only [gs,cur,ite_true] at split lookup
    have full := congrArg (first ++ ·) split
    have eq := paidRegister_at (first++pre) p post (by simpa only [first,Geometry.Moves.phaseEdges,List.append_assoc] using full)
      paid j (by
        unfold invocationRegister
        rw [List.length_append]
        change (if first.length+pre.length < first.length then _ else
          ((sectionB++sectionC).flatMap Frames.touched)[first.length+pre.length-first.length]?) = _
        rw [ite_eq_right (by omega),Nat.add_sub_cancel_left]
        exact lookup)
    simpa only [ite_true,List.filter_append,List.length_append] using congrArg (fun j : Fin 661 => some j.val) eq.symm

/-- A complete physical phase, read at any spectator, realizes the selected
frame semantics from the manuscript. The second phase resumes after COPY at
the first phase's paid-edge count. -/
theorem invocationIndexedPhase_read {k w W : ℕ} (owner : Fin 661 ↪ Fin k) (b : Bool)
    (x : Fin k → Fin ((prime^w)^16*W) → ZMod 2) (j : Fin W) :
    let gs := if b then sectionB++sectionC else sectionD++sectionA
    let cur := if b then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
    let start := if b then ((Frames.edges (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)).filter positiveMove).length else 0
    phaseRead owner (runIndexedPhase (scalarOwnerEffect owner) (moveOwnerEffect owner) gs cur x start) j =
      labelPhase w gs cur (phaseRead owner x j) := by
  intro gs cur start
  rw [phaseRead_indexedPhase owner gs cur (invocationPhase_allowed b)]
  have eq := indexedPhase_encode w gs cur (FramedCircuit.decode (fun i => selectedFrame w (cur i)) (phaseRead owner x j))
    start (invocationPhase_valid w b).1 (invocationPhase_aligned b)
  rw [FramedCircuit.encode_decode] at eq
  unfold readMove at eq
  exact eq

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

/-- A fixed tape address reads a shared owner, a private occurrence, or an unused blank. -/
noncomputable def moveStockSeed {I : Type} {k T : ℕ} {tapes : I → ℕ}
    (source : Fin T → Option (Fin k ⊕ Sigma (fun i => Fin (tapes i))))
    (shared : Stacks k prime) (seed : ∀ i, Stacks (tapes i) prime) : Stacks T prime :=
  let read (x : Fin k → List (Fin (prime+4))) (y : ∀ i, Fin (tapes i) → List (Fin (prime+4))) j :=
    match source j with
    | some (.inl i) => x i
    | some (.inr ⟨i,l⟩) => y i l
    | none => []
  ⟨shared.inp,shared.out,read shared.L (fun i => (seed i).L),read shared.R (fun i => (seed i).R)⟩

private theorem moveStockSources {I : Type} {k T : ℕ} {tapes : I → ℕ}
    (owner : ∀ i, Fin k ↪ Fin (tapes i)) (fan : Fin k ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T)
    (apart : ∀ i l, (∀ j, owner i j ≠ l) →
      (∀ j, fan j ≠ bank i l) ∧ ∀ m, m ≠ i → ∀ j, bank m j ≠ bank i l) :
    ∃ source : Fin T → Option (Fin k ⊕ Sigma (fun i => Fin (tapes i))),
      (∀ j, source (fan j) = some (.inl j)) ∧
      ∀ i l, (∀ j, owner i j ≠ l) → source (bank i l) = some (.inr ⟨i,l⟩) := by
  classical
  let privateAt (j : Fin T) (p : Sigma (fun i => Fin (tapes i))) :=
    bank p.1 p.2 = j ∧ ∀ h, owner p.1 h ≠ p.2
  let source (j : Fin T) : Option (Fin k ⊕ Sigma (fun i => Fin (tapes i))) :=
    if h : ∃ i, fan i = j then some (.inl h.choose) else
    if h : ∃ p, privateAt j p then some (.inr h.choose) else none
  refine ⟨source,?_,?_⟩
  · intro j
    have h : ∃ i, fan i = fan j := ⟨j,rfl⟩
    simp only [source,dif_pos h,fan.injective h.choose_spec]
  · intro i l off
    have free := apart i l off
    have h : ∃ p, privateAt (bank i l) p := ⟨⟨i,l⟩,rfl,off⟩
    have unique (p : Sigma (fun i => Fin (tapes i))) (atSlot : privateAt (bank i l) p) : p = ⟨i,l⟩ := by
      obtain ⟨m,j⟩ := p
      have eq := atSlot.1
      by_cases same : m = i
      · subst m
        exact congrArg (Sigma.mk i) ((bank i).injective eq)
      · exact (free.2 m same j eq).elim
    simp only [source,dif_neg (show ¬ ∃ j, fan j = bank i l from fun ⟨j,eq⟩ => free.1 j eq),dif_pos h,unique _ h.choose_spec]

/-- Allocate the MOVE occurrences together. Their owner tapes coincide;
all not-yet-run occurrences retain their seed across an embedded call. -/
theorem allocateMoveStock {I : Type} [Fintype I] {owners : ℕ} (tapes : I → ℕ)
    (owner : ∀ i, Fin owners ↪ Fin (tapes i)) :
    ∃ (T : ℕ) (fan : Fin owners ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T)
      (source : Fin T → Option (Fin owners ⊕ Sigma (fun i => Fin (tapes i)))),
      (∀ i j, bank i (owner i j) = fan j) ∧ (∀ j, source (fan j) = some (.inl j)) ∧
      ∀ seed : ∀ i, Stacks (tapes i) prime,
      let ready := fun i (S : Stacks T prime) => PrivateTapes (owner i) (seed i) (embStk (bank i) S)
      (∀ shared, let initial := moveStockSeed source shared seed; embStk fan initial = shared ∧ ∀ S, PrivateTapes fan initial S → ∀ i, ready i S) ∧
      ∀ {P R U : Type} {Q : ℕ} (i : I) (body : P → Pr P (tapes i) Q prime U)
        (host : R → Pr R T Q prime U) (label : P → R),
        (∀ f, host (label f) = embProg (bank i) label (body f)) →
        ∀ code u S z F n, Exec body code (mk (embDn (bank i) u) (embStk (bank i) S)) n (mk z F) →
        ∃ v G, Exec host (embProg (bank i) label code) (mk u S) n (mk v G) ∧
          v.user = z.user ∧ embStk (bank i) G = F ∧ (∀ j, (∀ h, bank i h ≠ j) → G.L j = S.L j ∧ G.R j = S.R j) ∧ ∀ j, j ≠ i → ready j S → ready j G := by
  obtain ⟨T,fan,bank,shared,_,_,apart⟩ := copyWindowBanks tapes owner
  obtain ⟨source,owners,privateAt⟩ := moveStockSources owner fan bank apart
  refine ⟨T,fan,bank,source,shared,owners,?_⟩
  intro seed ready
  constructor
  · intro X
    constructor
    · cases X
      simp [moveStockSeed,embStk,Function.comp_def,owners]
    · intro D fresh i k outside
      have h := fresh (bank i k) (apart i k outside).1
      simpa [moveStockSeed,embStk,privateAt i k outside] using h
  · intro P R U Q i body host label installed code u S z F n run
    obtain ⟨v,G,exec,_,user,view,off⟩ := exec_emb (body' := host) (ι := label) (bank i).injective
      installed run u rfl S rfl
    refine ⟨v,G,exec,user,view,off,?_⟩
    intro j ne stock
    have keep (k : Fin (tapes j)) (outside : ∀ h, owner j h ≠ k) := off (bank j k) ((apart j k outside).2 i ne.symm)
    exact fun k outside => ⟨(keep k outside).1.trans (stock k outside).1, (keep k outside).2.trans (stock k outside).2⟩

/-- Place the pre-COPY phase, COPY, and post-COPY phase on one owner and cutoff
bank. Each program has its own procedure labels and private initialization. -/
theorem placeInvocationPrograms {owners : ℕ} (tapes : Fin 3 → ℕ)
    (ports : ∀ i, Fin owners ↪ Fin (tapes i)) :
    ∃ (T : ℕ) (fan : Fin owners ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T)
      (source : Fin T → Option (Fin owners ⊕ Sigma (fun i => Fin (tapes i)))),
    (∀ j, source (fan j) = some (.inl j)) ∧
    ∀ {P : Fin 3 → Type} {Q : ℕ} {U : Type} (body : ∀ i, P i → Pr (P i) (tapes i) Q prime U)
      (code : ∀ i, Pr (P i) (tapes i) Q prime U),
    let host := fun f : Sigma P => embProg (bank f.1) (Sigma.mk f.1) (body f.1 f.2)
    let placed := fun i => embProg (bank i) (Sigma.mk i) (code i)
    ∀ {α : Type} (rep : α → Stacks owners prime → Prop) (effect : Fin 3 → α → α → Prop)
      (budget : Fin 3 → ℕ) (seed : ∀ i, Stacks (tapes i) prime),
    (∀ i x u S, PrivateTapes (ports i) (seed i) S → rep x (embStk (ports i) S) →
      ∃ z F n y, Exec (body i) (code i) (mk u S) n (mk z F) ∧ CleanupBound S F n (budget i) ∧
        z.user = u.user ∧ rep y (embStk (ports i) F) ∧ effect i x y) →
    ∀ shared, let initial := moveStockSeed source shared seed; embStk fan initial = shared ∧ ∀ x u S, PrivateTapes fan initial S →
      rep x (embStk fan S) → ∃ z F n a b y,
        Exec host ((placed 0).seq ((placed 1).seq (placed 2))) (mk u S) n (mk z F) ∧
        CleanupBound S F n (budget 0+(budget 1+budget 2)) ∧ z.user = u.user ∧ rep y (embStk fan F) ∧
        effect 0 x a ∧ effect 1 a b ∧ effect 2 b y := by
  obtain ⟨T,fan,bank,source,sharedAt,ownersAt,allocate⟩ := allocateMoveStock tapes ports
  refine ⟨T,fan,bank,source,ownersAt,?_⟩
  intro P Q U body code host placed α rep effect budget seed run shared
  obtain ⟨join,place⟩ := allocate seed
  obtain ⟨view,initialized⟩ := join shared
  refine ⟨view,?_⟩
  intro x u S fresh live
  let ready := fun i D => PrivateTapes (ports i) (seed i) (embStk (bank i) D)
  have stock := initialized S fresh
  have project i (D : Stacks T prime) : embStk (ports i) (embStk (bank i) D) = embStk fan D := by
    simp only [embStk,Function.comp_def,sharedAt]
  have step (i) data (v : HS T Q prime U) D (init : ready i D) (live : rep data (embStk fan D)) :
      ∃ z F n y, Exec host (placed i) (mk v D) n (mk z F) ∧ CleanupBound D F n (budget i) ∧
        z.user = v.user ∧ rep y (embStk fan F) ∧ effect i data y ∧ ∀ j, j ≠ i → ready j D → ready j F := by
    obtain ⟨q,G,n,y,exec,cost,user,out,act⟩ := run i data (embDn (bank i) v) _ init (by rwa [project])
    obtain ⟨z,F,h,same,returned,off,keep⟩ := place i (body i) host (Sigma.mk i) (fun _ => rfl) _ v D q G n exec
    rw [← returned] at cost out
    exact ⟨z,F,n,y,h,CleanupBound.place (bank i) off cost,same.trans user,project i F ▸ out,act,keep⟩
  obtain ⟨v,D,l,a,left,lp,vu,ra,ha,keepA⟩ := step 0 x u S (stock _) live
  obtain ⟨z,F,m,b,middle,mp,zv,rb,hb,keepB⟩ := step 1 a v D (keepA 1 (by decide) (stock _)) ra
  obtain ⟨q,G,r,y,right,rp,qz,ry,hy,_⟩ := step 2 b z F (keepB 2 (by decide) (keepA 2 (by decide) (stock _))) rb
  exact ⟨q,G,_,a,b,y,Exec.seq left (Exec.seq middle right),lp.seq (mp.seq rp),qz.trans (zv.trans vu),ry,ha,hb,hy⟩

noncomputable def invocationPhaseOutput {w W : ℕ} (n : Fin 9) (p : Fin 32 × Fin 5) (afterCopy : Bool)
    (x : Fin 142081 → Fin ((prime^w)^16*W) → ZMod 2) :=
  let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n p.1 p.2,ownerTape_injective ..⟩
  let gs := if afterCopy then sectionB++sectionC else sectionD++sectionA
  let cur := if afterCopy then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
  let start := if afterCopy then ((Frames.edges (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)).filter positiveMove).length else 0
  runIndexedPhase (scalarOwnerEffect owner) (moveOwnerEffect owner) gs cur x start

private theorem invocationPhaseOutput_off {w W : ℕ} (n : Fin 9) (p : Fin 32 × Fin 5) (b : Bool)
    (x : Fin 142081 → Fin ((prime^w)^16*W) → ZMod 2) (k : Fin 142081)
    (outside : ∀ i, ownerTape n p.1 p.2 i ≠ k) : invocationPhaseOutput n p b x k = x k :=
  indexedPhase_off_owner _ _ _ x _ k outside

/-- The middle component performs all nine COPY windows. The outer components
return the owner words produced by the corresponding indexed phase. -/
def InvocationComponentEffect (n : Fin 9) (p : Fin 32 × Fin 5) (w B K : ℕ) (i : Fin 3)
    (x y : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2) : Prop :=
  let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n p.1 p.2,ownerTape_injective ..⟩
  if i = 1 then (∀ g (cell : Cover.LabelEntry.Cell (copyLabelLayout w B K) B),
      phaseRead owner y (labelSpectator g cell) = Copy.run (selectedFrame w) Copy.lifecycles
        (phaseRead owner x (labelSpectator g cell))) ∧
      ∀ k, k ≠ Fin.last 142080 → (∀ j, owner j ≠ k) → y k = x k
  else y = invocationPhaseOutput n p (i == 2) x

/-- The two selected phase outputs and middle COPY effect give one borrowed invocation. -/
theorem invocationComponentEffects {w B K : ℕ} (n : Fin 9) (p : Fin 32 × Fin 5)
    (x a b y : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2)
    (left : InvocationComponentEffect n p w B K 0 x a) (copy : InvocationComponentEffect n p w B K 1 a b)
    (right : InvocationComponentEffect n p w B K 2 b y) : BorrowedStep n w B K p x y := by
  change a = invocationPhaseOutput n p false x at left
  change y = invocationPhaseOutput n p true b at right
  subst a
  subst y
  simp only [InvocationComponentEffect,ite_true] at copy
  constructor
  · intro g cell
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n p.1 p.2,ownerTape_injective ..⟩
    let j := labelSpectator g cell
    have middle : phaseRead owner b j = borrowedScatter w (phaseRead owner (invocationPhaseOutput n p false x) j) := by
      funext i
      by_cases hi : i < 661
      · exact (congrFun (copy.1 g cell) i).trans (commonScatter_eq_borrowedScatter _ _ _ ⟨i,hi⟩)
      · simp [phaseRead,borrowedScatter,Copy.extendStored,hi]
    change phaseRead _ (invocationPhaseOutput n p true b) (labelSpectator g cell) = _
    rw [show phaseRead _ (invocationPhaseOutput n p true b) _ = _ from invocationIndexedPhase_read _ true b _,middle]
    rw [show phaseRead _ (invocationPhaseOutput n p false x) _ = _ from invocationIndexedPhase_read _ false x _]
    simp only [j,Bool.false_eq_true,ite_false,ite_true]
  · intro k live outside
    apply (invocationPhaseOutput_off n p true b k outside).trans
    apply Eq.trans _ (invocationPhaseOutput_off n p false x k outside)
    exact copy.2 k live outside

/-- A charged invocation on shared owner tapes and one shared cutoff tape.
Its code is fixed before the volume, cutoff word, component budgets and seeds. -/
theorem chargedInvocation_host (n : Fin 9) (p : Fin 32 × Fin 5) (tapes : Fin 3 → ℕ)
    (ports : ∀ i, Fin (142081+2+1) ↪ Fin (tapes i)) :
    ∃ (T : ℕ) (fan : Fin (142081+2+1) ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T)
      (source : Fin T → Option (Fin (142081+2+1) ⊕ Sigma (fun i => Fin (tapes i)))),
    (∀ j, source (fan j) = some (.inl j)) ∧
    ∀ {P : Fin 3 → Type} {Q : ℕ} {U : Type} (body : ∀ i, P i → Pr (P i) (tapes i) Q prime U)
      (code : ∀ i, Pr (P i) (tapes i) Q prime U),
    let host := fun f : Sigma P => embProg (bank f.1) (Sigma.mk f.1) (body f.1 f.2)
    ∃ program, ∀ (w B K : ℕ) word,
    let V := (prime^w)^16*(B*prime^(64*(w*64))*K)
    let rep := fun (x : Fin 142081 → Fin V → ZMod 2) (S : Stacks (142081+2+1) prime) =>
      HelperFan (Fin.castAddEmb 1) x S ∧ S.R (Fin.last (142081+2)) = word
    ∀ (budget : Fin 3 → ℕ) (seed : ∀ i, Stacks (tapes i) prime),
    (∀ i x u S, PrivateTapes (ports i) (seed i) S → rep x (embStk (ports i) S) →
      ∃ z F m y, Exec (body i) (code i) (mk u S) m (mk z F) ∧ CleanupBound S F m (budget i) ∧
        z.user = u.user ∧ rep y (embStk (ports i) F) ∧ InvocationComponentEffect n p w B K i x y) →
    ∀ shared, let initial := moveStockSeed source shared seed; embStk fan initial = shared ∧ ∀ x u S, PrivateTapes fan initial S →
      rep x (embStk fan S) → ∃ z F m y, Exec host program (mk u S) m (mk z F) ∧
        CleanupBound S F m (budget 0+(budget 1+budget 2)) ∧ z.user = u.user ∧ rep y (embStk fan F) ∧
        BorrowedStep n w B K p x y := by
  obtain ⟨T,fan,bank,source,ownersAt,place⟩ := placeInvocationPrograms tapes ports
  refine ⟨T,fan,bank,source,ownersAt,?_⟩
  intro P Q U body code host
  let placed := fun i => embProg (bank i) (Sigma.mk i) (code i)
  refine ⟨(placed 0).seq ((placed 1).seq (placed 2)),?_⟩
  intro w B K word V rep budget seed runs shared
  obtain ⟨view,run⟩ := place body code rep _ budget seed runs shared
  refine ⟨view,?_⟩
  intro x u S fresh ready
  obtain ⟨z,F,m,a,b,y,exec,paid,user,out,left,copy,right⟩ := run x u S fresh ready
  exact ⟨z,F,m,y,exec,paid,user,out,invocationComponentEffects n p x a b y left copy right⟩

/-- Extend the shared bank by a cutoff tape outside the worker's tape range. -/
def withCutoffPort {k T : ℕ} (fan : Fin k ↪ Fin T) : Fin (k+1) ↪ Fin (T+1) :=
  (finSumFinEquiv.symm.toEmbedding.trans (fan.sumMap (Function.Embedding.refl (Fin 1)))).trans finSumFinEquiv.toEmbedding

private theorem withCutoffPort_data {k T : ℕ} (fan : Fin k ↪ Fin T) (i : Fin k) :
    withCutoffPort fan (i.castAdd 1) = (fan i).castAdd 1 := by
  simp [withCutoffPort,Function.Embedding.sumMap]

theorem withCutoffPort_cut {k T : ℕ} (fan : Fin k ↪ Fin T) :
    withCutoffPort fan (Fin.last k) = Fin.last T := by
  change withCutoffPort fan ((0 : Fin 1).natAdd k) = (0 : Fin 1).natAdd T
  simp [withCutoffPort,Function.Embedding.sumMap]

open RecursiveInterchangeLayout in
/-- Worker records lie outside the cutoff, and archive tape 34 is private. -/
theorem withCutoffPort_records {k T m : ℕ} (fan : Fin k ↪ Fin T) (ports : Fin (m+35) ↪ Fin T)
    (apart : ∀ j : Fin (m+35), j.val ≠ 24 → ∀ h, fan h ≠ ports j) :
    let record := (scheduledRecordPorts ports).trans (Fin.castAddEmb 1)
    (∀ j, record j ≠ withCutoffPort fan (Fin.last k)) ∧ (∀ j : Fin 35, j.val ≠ 24 → ∀ h, withCutoffPort fan h ≠ record j) := by
  intro record
  have off j : record j ≠ withCutoffPort fan (Fin.last k) := by
    rw [withCutoffPort_cut]
    exact fun eq => ((scheduledRecordPorts ports j).isLt).ne (congrArg Fin.val eq)
  refine ⟨off,?_⟩
  intro j ne h
  induction h using Fin.addCases with
  | left h =>
    rw [withCutoffPort_data]
    exact (Fin.castAddEmb 1).injective.ne (apart _ ne h)
  | right h =>
    have eq : h = 0 := Subsingleton.elim ..
    subst h
    exact (off j).symm

private theorem withCutoffPort_view {k T : ℕ} (fan : Fin k ↪ Fin T) (S : Stacks (T+1) prime) :
    embStk (Fin.castAddEmb 1 (n := k)) (embStk (withCutoffPort fan) S) =
      embStk fan (embStk (Fin.castAddEmb 1) S) := by
  simp only [embStk,Function.comp_def,Fin.coe_castAddEmb,withCutoffPort_data]

def cutoffWorkerSeed {T : ℕ} (seed : Stacks T prime) : Stacks (T+1) prime :=
  ⟨seed.inp,seed.out,Fin.append seed.L (fun _ => []),Fin.append seed.R (fun _ => [])⟩

theorem withCutoffPort_private_cast {k T : ℕ} (fan : Fin k ↪ Fin T) (j : Fin T) :
    (∀ i, withCutoffPort fan i ≠ j.castAdd 1) ↔ ∀ i, fan i ≠ j := by
  constructor
  · exact fun outside i eq => outside (i.castAdd 1)
      ((withCutoffPort_data fan i).trans (congrArg (Fin.castAdd 1) eq))
  · intro outside i
    induction i using Fin.lastCases with
    | last =>
      rw [withCutoffPort_cut]
      exact fun eq => j.isLt.ne (congrArg Fin.val eq.symm)
    | cast i =>
      change withCutoffPort fan (i.castAdd 1) ≠ j.castAdd 1
      rw [withCutoffPort_data]
      exact (Fin.castAddEmb 1).injective.ne (outside i)

/-- The cutoff port is shared, so lifting a worker preserves its private stock. -/
theorem privateTapes_withCutoff {k T : ℕ} (fan : Fin k ↪ Fin T) (seed : Stacks T prime)
    (S : Stacks (T+1) prime) :
    PrivateTapes (withCutoffPort fan) (cutoffWorkerSeed seed) S ↔
      PrivateTapes fan seed (embStk (Fin.castAddEmb 1) S) := by
  constructor
  · intro fresh j outside
    simpa only [embStk,Function.comp_apply,Fin.coe_castAddEmb,cutoffWorkerSeed,Fin.append_left]
      using fresh (j.castAdd 1) ((withCutoffPort_private_cast fan j).mpr outside)
  · intro stock j
    induction j using Fin.lastCases with
    | last => exact fun outside => False.elim (outside (Fin.last k) (withCutoffPort_cut fan))
    | cast j =>
      intro outside
      change S.L (j.castAdd 1) = (cutoffWorkerSeed seed).L (j.castAdd 1) ∧
        S.R (j.castAdd 1) = (cutoffWorkerSeed seed).R (j.castAdd 1)
      simpa only [embStk,Function.comp_apply,Fin.coe_castAddEmb,cutoffWorkerSeed,Fin.append_left]
        using stock j ((withCutoffPort_private_cast fan j).mp outside)

/-- Lift a seeded worker without changing its countdown word, step count, or
cleanup budget. Only tapes outside the extended owner bank need initialization. -/
private theorem runWithCutoff {α P U : Type} {k T Q : ℕ} (fan : Fin k ↪ Fin T)
    (body : P → Pr P T Q prime U) (code : Pr P T Q prime U) (seed : Stacks T prime) :
    let bank := Fin.castAddEmb 1 (n := T)
    let host := fun f => embProg bank id (body f)
    let ports := withCutoffPort fan
    let initial := cutoffWorkerSeed seed
    (∀ j, initial.R (bank j) = seed.R j) ∧ ∀ (rep : α → Stacks k prime → Prop) (effect : α → α → Prop)
      (budget : ℕ) (word : List (Fin (prime+4))),
    (∀ x u S, PrivateTapes fan seed S → rep x (embStk fan S) → ∃ z F t y,
      Exec body code (mk u S) t (mk z F) ∧ CleanupBound S F t budget ∧ z.user = u.user ∧
        rep y (embStk fan F) ∧ effect x y) →
    ∀ x u S, PrivateTapes ports initial S → rep x (embStk fan (embStk bank S)) →
      S.R (ports (Fin.last k)) = word → ∃ z F t y, Exec host (embProg bank id code) (mk u S) t (mk z F) ∧
        CleanupBound S F t budget ∧ z.user = u.user ∧ rep y (embStk fan (embStk bank F)) ∧
        F.R (ports (Fin.last k)) = word ∧ effect x y := by
  intro bank host ports
  intro initial
  refine ⟨fun j => by simp only [initial,cutoffWorkerSeed,bank,Fin.coe_castAddEmb,Fin.append_left],?_⟩
  intro rep effect budget word run x u S fresh live header
  have cut (j : Fin T) : bank j ≠ ports (Fin.last k) := by
    rw [withCutoffPort_cut]
    exact fun h => j.isLt.ne (congrArg Fin.val h)
  have stock := (privateTapes_withCutoff fan seed S).mp fresh
  obtain ⟨z,F,t,y,exec,paid,user,out,acts⟩ := run x (embDn bank u) _ stock live
  obtain ⟨v,G,h,_,same,view,off⟩ := exec_emb (body' := host) (ι := id) bank.injective (fun _ => rfl) exec u rfl S rfl
  rw [← view] at paid out
  exact ⟨v,G,t,y,h,CleanupBound.place bank off paid,same.trans user,out,(off _ cut).2.trans header,acts⟩

open RecursiveInterchangeLayout in
/-- One selected worker, with a fixed layout and a local charge additive in the child budget. -/
def SelectedOccurrenceWorker [M8.Machine.Net] (child : Fin nodeChildren5.length)
    (coords : ∀ (desc : Descriptor) (w W : ℕ), (Fin (volume prime desc) ≃ Fin ((prime^w)^16*W)) → Prop)
    (effect : ∀ w B K : ℕ, let X := Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2
      X → X → Prop) : Prop :=
    ∃ (T states : ℕ) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (fan : Fin (142081+2) ↪ Fin T),
    ∃ basis : WorkerBasisLayout ports, basis.OwnerTapes fan ∧
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (body : P → Pr P T Q prime U) (f : P),
    let bank := Fin.castAddEmb 1 (n := T)
    let host := fun f => embProg bank id (body f)
    let owners := withCutoffPort fan
    ∃ (base swaps fixed : ℕ) (code : Pr P (T+1) Q prime U), ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let blocks := M^112*B
    let W := blocks*prime^(64*((w+1)*64))*K
    let V := M^16*W
    let desc := scheduledChild prime node child
    0 < W → ∃ position : Fin (volume prime desc) ≃ Fin V,
      coords desc (w+1) W position ∧
      ∀ record,
      let prepared := cutoffWorkerSeed (basis.seed w W record)
      WorkerEntryWords (fun j => (scheduledRecordPorts ports j).castAdd 1) record prepared ∧ ∀ budget word,
      ScheduledChildExec node desc w W ports record position body f budget true →
      let rep := fun x (D : Stacks (T+1) prime) => HelperFan (Fin.castAddEmb 1) x (embStk owners D) ∧
        D.R (owners (Fin.last (142081+2))) = word
      ∀ data u S, PrivateTapes owners prepared S → rep data S →
        ∃ z F t out, Exec host code (mk u S) t (mk z F) ∧
          CleanupBound S F t ((base+swaps*swapVolumeRate w)*V+fixed+budget) ∧ z.user = u.user ∧ rep out F ∧
          effect (w+1) blocks K data out

open RecursiveInterchangeLayout in
/-- Execute one selected COPY window with its private seed and shared cutoff. -/
theorem invocationCopyWindow [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) (j : Fin Copy.lifecycles.length) :
    SelectedOccurrenceWorker (copyChildPosition (n,p,j)) CopyIntervalPositions
      (CopyFanoutEffect n p.1 p.2 Copy.lifecycles[j.val] (List.getElem_mem ..)) := by
  unfold SelectedOccurrenceWorker
  obtain ⟨T,states,ports,fan,basis,owned,build⟩ := borrowedWindow_layout true n p j
  refine ⟨T,states,ports,fan,basis,owned,?_⟩
  intro P U Q cap body f bank host owners
  obtain ⟨base,code,run⟩ := build cap body f
  refine ⟨13*base,0,156,embProg bank id code,?_⟩
  intro node w B rows width split label M K blocks W V desc pos
  obtain ⟨position,coords,prepare⟩ := run node w B rows width split label pos
  refine ⟨position,coords,?_⟩
  intro record
  let seed := basis.seed w W record
  obtain ⟨archive,window⟩ := prepare record
  let Data := Fin 142081 → Fin V → ZMod 2
  let stored := fun (x : Data) (D : Stacks (142081+2) prime) => HelperFan (Function.Embedding.refl _) x D
  let initial := cutoffWorkerSeed seed
  obtain ⟨original,lift⟩ := runWithCutoff (α := Data) fan body code seed
  refine ⟨⟨(original _).trans archive.1,(original _).trans archive.2.1,(original _).trans archive.2.2⟩,?_⟩
  intro budget word child rep data u S fresh live
  have execute := lift stored _ _ word (fun x v D stock ready => window budget child x v D ready stock)
  obtain ⟨z,F,t,y,exec,paid,user,out,cut,act⟩ := execute data u S fresh (by
    have h := live.1
    change stored data (embStk (Fin.castAddEmb 1) (embStk owners S)) at h
    rwa [withCutoffPort_view] at h) live.2
  have price : nativePrice true (base*V+12)+budget = (13*base+0*swapVolumeRate w)*V+156+budget := by unfold nativePrice; simp; ring
  exact ⟨z,F,t,y,exec,price ▸ paid,user,⟨show stored y (embStk (Fin.castAddEmb 1) (embStk owners F)) from
    withCutoffPort_view fan F ▸ out,cut⟩,act⟩

open RecursiveInterchangeLayout in
/-- The fixed nine-window program supplies the middle invocation component on
the shared owner and cutoff bank, with one budget for each child. -/
theorem invocationCopyComponent [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) :
    let J := Fin Copy.lifecycles.length
    ∃ (tapes : J → ℕ) (regs : ∀ j, Fin (rowSwapBlock.tapes+35) ↪ Fin (tapes j))
      (T states : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ j, Fin (tapes j) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (localBody : ∀ j, P → Pr P (tapes j) Q prime U) (proc : J → P),
    let localHost := fun f : J × P => embProg (bank f.1) (fun g => (f.1,g)) (localBody f.1 f.2)
    let bankCopy := Fin.castAddEmb 1 (n := T)
    let host := fun f => embProg bankCopy id (localHost f)
    let ports := withCutoffPort fan
    ∃ (base : J → ℕ) (program : Pr (J × P) (T+1) Q prime U), ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let blocks := M^112*B
    let W := blocks*prime^(64*((w+1)*64))*K
    let V := M^16*W
    let desc := fun j : J => scheduledChild prime node (copyChildPosition (n,p,j))
    0 < W → ∃ position : ∀ j, Fin (volume prime (desc j)) ≃ Fin V,
      (∀ j, CopyIntervalPositions (desc j) (w+1) W (position j)) ∧
      ∀ record : J → List (Fin (prime+4)), ∃ initial : Stacks (T+1) prime, ∀ (budget : J → ℕ) word,
      (∀ j, ScheduledChildExec node (desc j) w W (regs j) (record j) (position j) (localBody j) (proc j) (budget j) true) →
      let work := fun j => nativePrice true (base j*V+12)
      let rep := fun data (S : Stacks (T+1) prime) => HelperFan (Fin.castAddEmb 1) data (embStk ports S) ∧
        S.R (ports (Fin.last (142081+2))) = word
      ∀ (data : Fin 142081 → Fin V → ZMod 2) u S, PrivateTapes ports initial S → rep data S →
        ∃ z F t out, Exec host program (mk u S) t (mk z F) ∧
          CleanupBound S F t ((List.ofFn work).sum+(List.ofFn budget).sum+1) ∧ z.user = u.user ∧
          rep out F ∧ InvocationComponentEffect n p (w+1) blocks K 1 data out := by
  intro J
  obtain ⟨ts,regs,T,states,fan,bank,build⟩ := borrowedWindows_host true n p
  refine ⟨ts,regs,T,states,fan,bank,?_⟩
  intro P U Q cap localBody proc localHost bankCopy host ports
  obtain ⟨base,code,run⟩ := build cap localBody proc
  refine ⟨base,embProg bankCopy id code,?_⟩
  intro node w B rows width split label M K blocks W V desc pos
  obtain ⟨position,coords,prepare⟩ := run node w B rows width split label pos
  refine ⟨position,coords,?_⟩
  intro record
  let blankStack : Stacks (142081+2) prime := ⟨[],[],fun _ => [],fun _ => []⟩
  obtain ⟨seed,_,windows⟩ := prepare record blankStack
  let Data := Fin 142081 → Fin V → ZMod 2
  let initial := cutoffWorkerSeed seed
  obtain ⟨_,lift⟩ := runWithCutoff (α := Data) fan localHost code seed
  refine ⟨initial,?_⟩
  intro budget word children work rep data u S fresh live
  let stored := fun (x : Data) (D : Stacks (142081+2) prime) => HelperFan (Function.Embedding.refl _) x D
  have useCopy := lift stored (InvocationComponentEffect n p (w+1) blocks K 1) _ word (fun x v D stock ready => by
    obtain ⟨z,F,t,y,exec,paid,user,out,act,off⟩ := windows budget children x v D ready stock
    exact ⟨z,F,t,y,exec,paid,user,out,act,off⟩)
  obtain ⟨z,F,t,y,exec,paid,user,out,header,act⟩ := useCopy data u S fresh (by
    have h := live.1
    change stored data (embStk (Fin.castAddEmb 1) (embStk ports S)) at h
    rwa [withCutoffPort_view] at h) live.2
  refine ⟨z,F,t,y,exec,paid,user,?_,act⟩
  exact ⟨show stored y (embStk (Fin.castAddEmb 1) (embStk ports F)) from withCutoffPort_view fan F ▸ out,header⟩

open RecursiveInterchangeLayout in
def SelectedMoveWindow [M8.Machine.Net] {k : ℕ} (layout : Fin 661 ↪ Fin k)
    (n : Fin 9) (p : Fin 32 × Fin 5) (i : MoveIndex) (T states : ℕ)
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (fan : Fin (k+2) ↪ Fin T)
    (basis : WorkerBasisLayout ports) : Prop :=
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (body : P → Pr P T Q prime U) (f : P),
    let host := fun label => embProg (Fin.castAddEmb 1) id (body label)
    ∃ (base swaps : ℕ) (code : Pr P (T+1) Q prime U), ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let W := (M^112*B)*prime^(64*((w+1)*64))*K
    let V := M^16*W
    let desc := scheduledChild prime node (phaseChildPositions.choose (n,p,i))
    0 < W → ∃ position : Fin (volume prime desc) ≃ Fin V,
    (∀ h, (position h).val = (CopyChildLayout.packActive desc h).val) ∧
    ∀ record,
    let initial := cutoffWorkerSeed (basis.seed w W record)
    WorkerEntryWords (fun j => (scheduledRecordPorts ports j).castAdd 1) record initial ∧ ∀ budget word,
    ScheduledChildExec node desc w W ports record position body f budget true →
    let owners := withCutoffPort fan
    let rep := fun x (S : Stacks (T+1) prime) => HelperFan (Fin.castAddEmb 1) x (embStk owners S) ∧
      S.R (owners (Fin.last (k+2))) = word
    ∀ (x : Fin k → Fin V → ZMod 2) u S, PrivateTapes owners initial S → rep x S →
      ∃ z F t, Exec host code (mk u S) t (mk z F) ∧
        CleanupBound S F t (budget+nativePrice true ((base+swaps*swapVolumeRate w)*V)) ∧ z.user = u.user ∧
        rep (moveOwnerEffect layout x i.val ((Geometry.Moves.phaseEdges.filter positiveMove)[i.val]'i.isLt)) F

open RecursiveInterchangeLayout in
/-- Execute a paid MOVE from the invocation directory on its selected owner
and retain the shared cutoff. The recursive budget enters the total once. -/
theorem invocationMoveLayout [M8.Machine.Net] {k : ℕ} (layout : Fin 661 ↪ Fin k)
    (n : Fin 9) (p : Fin 32 × Fin 5) (i : MoveIndex) :
    ∃ (T states : ℕ) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (fan : Fin (k+2) ↪ Fin T)
      (basis : WorkerBasisLayout ports), basis.OwnerTapes fan ∧ SelectedMoveWindow layout n p i T states ports fan basis := by
  let edge := (Geometry.Moves.phaseEdges.filter positiveMove)[i.val]'i.isLt
  let child := phaseChildPositions.choose (n,p,i)
  have mem := List.mem_filter.mp (List.getElem_mem (l := Geometry.Moves.phaseEdges.filter positiveMove) i.isLt)
  have checked := Geometry.Moves.phase_checked edge mem.1
  have paid : 0 < Geometry.moveRank edge.1 edge.2 := Nat.pos_of_ne_zero (bne_iff_ne.mp mem.2)
  obtain ⟨A,B',T,states,ports,fan,a,b,basis,owners,basisEq,apart,_,_,_,build⟩ :=
    allocatedPhaseMove_host true (layout (paidRegister i.val)) edge checked paid
  refine ⟨T,states,ports,fan,basis,owners,?_⟩
  intro P U Q cap body f host
  obtain ⟨base,swaps,code,run⟩ := build cap body f
  refine ⟨base,swaps,embProg (Fin.castAddEmb 1) id code,?_⟩
  intro node w B rows width split label M K W V desc pos
  have aligned : B*prime^(64*((w+1)*64))*(M^112*K) = W := by dsimp only [W]; ring
  have go := run node child w B rows (phaseChildPositions.choose_spec n p i).1 width split label
  dsimp only at go
  rw [aligned] at go
  -- The child record is private, so initialize it after the record word is fixed.
  have calls := fun record => go pos record (fun _ => blank) 0
  obtain ⟨position,coords,_⟩ := calls []
  refine ⟨position,coords,?_⟩
  intro record
  obtain ⟨actual,coords',prepare,exec⟩ := calls record
  have same : actual = position := Equiv.ext (fun h => Fin.ext ((coords' h).trans (coords h).symm))
  subst actual
  let seed := recordBasisStacks ports ((Fin.natAddEmb 1).trans a) ((Fin.natAddEmb 1).trans b)
    (moveRecordSeed w W record [] []) (basisHeaderStacks A (w+1) W) (basisHeaderStacks B' (w+1) W)
  have ready := prepare [] [] (fun z => by simp [readAt_nil_left,wordTape_nil]; rfl)
  let Data := Fin k → Fin V → ZMod 2
  let initial := cutoffWorkerSeed seed
  obtain ⟨original,lift⟩ := runWithCutoff (α := Data) fan body code seed
  rw [basisEq w W record]
  refine ⟨?_,?_⟩
  · obtain ⟨D,⟨old,_,_,stored,_⟩,kept⟩ := ready
    have atPort (j : Fin 35) (ne : j.val ≠ 24) :
        initial.R ((scheduledRecordPorts ports j).castAdd 1) = D.R (scheduledRecordPorts ports j) := by
      apply (original _).trans
      apply (kept _ _).2
      refine ⟨ports.injective.ne (fun eq => ne (congrArg Fin.val eq)),?_⟩
      exact fun off => off.2.1 _ rfl
    exact ⟨(atPort 34 (by decide)).trans stored.archive,
      (atPort 0 (by decide)).trans (stored.scratch 0 (by decide)).2,
      (atPort 1 (by decide)).trans (stored.scratch 1 (by decide)).2⟩
  intro budget word recurse owners rep x u S fresh live
  let stored := fun (x : Data) (D : Stacks (k+2) prime) => HelperFan (Function.Embedding.refl _) x D
  have move := lift stored (fun x y => y = moveOwnerEffect layout x i.val edge) _ word (fun data v D stock h => by
    obtain ⟨old,init,kept⟩ := ready
    obtain ⟨z,F,t,y,run,paid,user,out,_,acts⟩ := exec budget recurse data v D h ⟨old,init,fun j hj =>
      ⟨(stock j (apart j hj)).1.trans (kept j hj).1,(stock j (apart j hj)).2.trans (kept j hj).2⟩⟩
    exact ⟨z,F,t,_,run,paid,user,out,moveOwnerEffect_of_exec layout data i.val edge checked y acts⟩)
  obtain ⟨z,F,t,y,run,paid,user,out,header,rfl⟩ := move x u S fresh (by
    have h := live.1
    change stored x (embStk (Fin.castAddEmb 1) (embStk owners S)) at h
    rwa [withCutoffPort_view] at h) live.2
  exact ⟨z,F,t,run,paid,user,show stored _ (embStk (Fin.castAddEmb 1) (embStk owners F)) from
    withCutoffPort_view fan F ▸ out,header⟩

open RecursiveInterchangeLayout in
theorem invocationMoveComponent [M8.Machine.Net] {k : ℕ} (layout : Fin 661 ↪ Fin k)
    (n : Fin 9) (p : Fin 32 × Fin 5) (i : MoveIndex) :
    let edge := (Geometry.Moves.phaseEdges.filter positiveMove)[i.val]'i.isLt
    let child := phaseChildPositions.choose (n,p,i)
    ∃ (T states : ℕ) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (fan : Fin (k+2) ↪ Fin T),
    (∀ j : Fin (rowSwapBlock.tapes+35), j.val ≠ 24 → ∀ h, fan h ≠ ports j) ∧
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (body : P → Pr P T Q prime U) (f : P),
    let host := fun label => embProg (Fin.castAddEmb 1) id (body label)
    ∃ (base swaps : ℕ) (code : Pr P (T+1) Q prime U), ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let W := (M^112*B)*prime^(64*((w+1)*64))*K
    let V := M^16*W
    let desc := scheduledChild prime node child
    0 < W → ∃ position : Fin (volume prime desc) ≃ Fin V,
    (∀ h, (position h).val = (CopyChildLayout.packActive desc h).val) ∧
    ∀ record, ∃ initial : Stacks (T+1) prime, WorkerEntryWords (fun j => (scheduledRecordPorts ports j).castAdd 1) record initial ∧ ∀ budget word,
    ScheduledChildExec node desc w W ports record position body f budget true →
    let owners := withCutoffPort fan
    let rep := fun x (S : Stacks (T+1) prime) => HelperFan (Fin.castAddEmb 1) x (embStk owners S) ∧
      S.R (owners (Fin.last (k+2))) = word
    ∀ (x : Fin k → Fin V → ZMod 2) u S, PrivateTapes owners initial S → rep x S →
      ∃ z F t, Exec host code (mk u S) t (mk z F) ∧
        CleanupBound S F t (budget+nativePrice true ((base+swaps*swapVolumeRate w)*V)) ∧ z.user = u.user ∧
        rep (moveOwnerEffect layout x i.val edge) F := by
  intro edge child
  obtain ⟨T,states,ports,fan,basis,owned,build⟩ := invocationMoveLayout layout n p i
  refine ⟨T,states,ports,fan,owned.recordPrivate,?_⟩
  intro P U Q cap body f host
  obtain ⟨base,swaps,code,run⟩ := build cap body f
  refine ⟨base,swaps,code,?_⟩
  intro node w B rows width split label M K W V desc pos
  obtain ⟨position,coords,prepare⟩ := run node w B rows width split label pos
  exact ⟨position,coords,fun record => ⟨cutoffWorkerSeed (basis.seed w W record),prepare record⟩⟩

/-- Sequence allocated MOVE calls in the supplied order. Only occurrences
remaining in the list need their private seed. The shared owner state follows
the same left fold, and each local execution budget is charged once. -/
theorem moveStockSequence {I P U : Type} [Fintype I] {owners Q : ℕ} (tapes : I → ℕ)
    (owner : ∀ i, Fin owners ↪ Fin (tapes i))
    (body : ∀ i, P → Pr P (tapes i) Q prime U) (code : ∀ i, Pr P (tapes i) Q prime U)
    (gates : I → Pr Empty owners Q prime U) (lastGates : Pr Empty owners Q prime U) (order : List I) (distinct : order.Nodup) :
    ∃ (T : ℕ) (fan : Fin owners ↪ Fin T) (host : I × P → Pr (I × P) T Q prime U)
      (program : Pr (I × P) T Q prime U)
      (source : Fin T → Option (Fin owners ⊕ Sigma (fun i => Fin (tapes i)))),
    ∀ {α : Type} (rep : α → Stacks owners prime → Prop) (gateStep step : α → I → α) (lastStep : α → α) (gateBudget budget : I → ℕ) (lastBudget : ℕ)
      (seed : ∀ i, Stacks (tapes i) prime),
    (∀ x u S, rep x S → ∃ z F n, Exec Empty.elim lastGates (mk u S) n (mk z F) ∧
      CleanupBound S F n (lastBudget) ∧ z.user = u.user ∧ rep (lastStep x) F) →
    (∀ i ∈ order, ∀ x u S, rep x S → ∃ z F n, Exec Empty.elim (gates i) (mk u S) n (mk z F) ∧
      CleanupBound S F n (gateBudget i) ∧ z.user = u.user ∧ rep (gateStep x i) F) →
    (∀ i ∈ order, ∀ x u S, rep x (embStk (owner i) S) → PrivateTapes (owner i) (seed i) S →
      ∃ z F n, Exec (body i) (code i) (mk u S) n (mk z F) ∧ CleanupBound S F n (budget i) ∧ z.user = u.user ∧
        rep (step x i) (embStk (owner i) F)) →
    ∀ shared, let initial := moveStockSeed source shared seed; embStk fan initial = shared ∧ ∀ x u S, PrivateTapes fan initial S → rep x (embStk fan S) →
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧ CleanupBound S F n ((order.map fun i => gateBudget i+budget i).sum+lastBudget) ∧
        z.user = u.user ∧ rep (lastStep (order.foldl (fun x i => step (gateStep x i) i) x)) (embStk fan F) := by
  obtain ⟨T,fan,bank,source,shared,_,allocate⟩ := allocateMoveStock tapes owner
  let host := fun f : I × P => embProg (bank f.1) (Prod.mk f.1) (body f.1 f.2)
  let block := fun i => (embProg (owner i) Empty.elim (gates i)).seq (code i)
  let seq := fun (is : List I) => is.foldr (fun i tail => (embProg (bank i) (Prod.mk i) (block i)).seq tail) (embProg fan Empty.elim lastGates)
  refine ⟨T,fan,host,seq order,source,?_⟩
  intro α rep gateStep step lastStep gateBudget budget lastBudget seed lastRun gateRun localRun X
  obtain ⟨join,place⟩ := allocate seed
  obtain ⟨view,initialized⟩ := join X
  refine ⟨view,?_⟩
  intro x u S fresh live
  have stock := initialized S fresh
  have project (i) (D : Stacks T prime) : embStk (owner i) (embStk (bank i) D) = embStk fan D := by
    simp only [embStk,Function.comp_def,shared]
  have ready (i) (_ : i ∈ order) := stock i
  clear stock view initialized fresh
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
    obtain ⟨v,D,placed,same,returned,off,kept⟩ := place i (body i) host (Prod.mk i) (fun _ => rfl) (block i) u S z F n run
    rw [← returned] at cost
    rw [← returned,project] at next
    obtain ⟨q,G,m,tail,paid,final,out⟩ := ih nodup (fun j hj => gateRun j (List.mem_cons_of_mem _ hj)) (fun j hj => localRun j (List.mem_cons_of_mem _ hj))
      (step (gateStep x i) i) v D next (fun j hj => kept j (fun eq => fresh (eq ▸ hj)) (ready j (List.mem_cons_of_mem _ hj)))
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
    ∃ (T : ℕ) (fan : Fin (k+2+1) ↪ Fin T), ∃ host code, ∃ (overhead : ℕ) (source : Fin T → Option (Fin (k+2+1) ⊕ Sigma (fun i => Fin (tapes i)))), ∀ {V : ℕ}, 0 < V →
    let dataBank := Fin.castAddEmb 1 (n := k+2)
    let rep := fun word (x : Fin k → Fin V → ZMod 2) (S : Stacks (k+2+1) prime) =>
      HelperFan dataBank x S ∧ S.R (Fin.last (k+2)) = word
    ∀ word start (step : (Fin k → Fin V → ZMod 2) → ℕ → ℕ × ℕ → Fin k → Fin V → ZMod 2) (budget : I → ℕ) (seed : ∀ i, Stacks (tapes i) prime),
      (∀ i, ∀ x u S, rep word x (embStk (owner i) S) → PrivateTapes (owner i) (seed i) S →
        ∃ z F n, Exec (body i) (move i) (mk u S) n (mk z F) ∧ CleanupBound S F n (budget i) ∧ z.user = u.user ∧ rep word (step x (start+i.val) schedule.1[i.val].2) (embStk (owner i) F)) →
      ∀ shared, let initial := moveStockSeed source shared seed; embStk fan initial = shared ∧
        ∀ x u S, PrivateTapes fan initial S → rep word x (embStk fan S) →
        ∃ z F n, Exec (host : I × P → Pr (I × P) T Q prime U) code (mk u S) n (mk z F) ∧
          CleanupBound S F n (overhead*V+(order.map budget).sum) ∧ z.user = u.user ∧
          rep word (runIndexedPhase (scalarOwnerEffect layout) step gs current x start) (embStk fan F)

/-- A scalar program on the data bank preserves the adjacent cutoff word at its original cost. -/
theorem scalarWithCutoff {k Q V cost : ℕ} {U : Type} {g : Pr Empty (k+2) Q prime U}
    {x y : Fin k → Fin V → ZMod 2}
    (localRun : ∀ u S, HelperFan (Function.Embedding.refl _) x S →
      ∃ z F n, Exec Empty.elim g (mk u S) n (mk z F) ∧ CleanupBound S F n cost ∧
        z.user = u.user ∧ HelperFan (Function.Embedding.refl _) y F) :
    let dataBank := Fin.castAddEmb 1 (n := k+2)
    ∀ (word : List (Fin (prime+4))) u S, HelperFan dataBank x S ∧ S.R (Fin.last (k+2)) = word →
      ∃ z F n, Exec Empty.elim (embProg dataBank (id : Empty → Empty) g) (mk u S) n (mk z F) ∧
        CleanupBound S F n cost ∧ z.user = u.user ∧ HelperFan dataBank y F ∧ F.R (Fin.last (k+2)) = word := by
  intro dataBank
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

open Certificates.PR589 in
/-- Compile a selected scalar block on the shared bank with a volume-linear charge. -/
theorem scalarCutoffBlock {k : ℕ} (layout : Fin 661 ↪ Fin k) :
    ∃ states, ∀ {Q : ℕ} {U : Type}, states ≤ Q →
    ∀ gs : List RawGate, (∀ g ∈ gs, g ∈ program) →
    ∃ (code : Pr Empty (k+2+1) Q prime U) (rate : ℕ), ∀ {V : ℕ}, 0 < V →
    ∀ (x : Fin k → Fin V → ZMod 2) (word : List (Fin (prime+4))) u S,
      HelperFan (Fin.castAddEmb 1) x S ∧ S.R (Fin.last (k+2)) = word →
      ∃ z F n, Exec Empty.elim code (mk u S) n (mk z F) ∧ CleanupBound S F n (rate*V) ∧
        z.user = u.user ∧ HelperFan (Fin.castAddEmb 1) (gs.foldl (scalarOwnerEffect layout) x) F ∧
        F.R (Fin.last (k+2)) = word := by
  obtain ⟨states,compile⟩ := scalarOwnerBlock layout
  refine ⟨states,?_⟩
  intro Q U capacity gs allowed
  obtain ⟨g,rate,run⟩ := compile (U := U) capacity gs allowed
  let bill := fun V (gs : List RawGate) => (gs.map fun g => 76*g.toCircuit.terms.length*V*(k+7)+6).sum+1
  refine ⟨embProg (Fin.castAddEmb 1) (id : Empty → Empty) g,rate*bill 1 gs,?_⟩
  intro V pos x
  have scale (gs : List RawGate) : bill V gs ≤ bill 1 gs*V := by
    unfold bill
    rw [Nat.add_mul,Nat.one_mul]
    apply Nat.add_le_add _ pos
    apply sumScaled
    intro g
    simp only [Nat.mul_one,Nat.add_mul]
    nlinarith only [pos]
  apply scalarWithCutoff
  intro u S live
  obtain ⟨z,F,n,exec,_,paid,user,out⟩ := run pos x u S live
  refine ⟨z,F,n,exec,?_,user,out⟩
  intro js distinct
  apply (paid js distinct).trans
  apply Nat.add_le_add_left
  change rate*bill V gs ≤ rate*bill 1 gs*V
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left rate (scale gs)

open Certificates.PR589 in
/-- Execute PR589 scalar blocks before and after a worker on its owner tapes. Its private archive is
available at worker entry, and only the bare worker execution is a premise. -/
theorem scalarWorkerBlocks {k : ℕ} (layout : Fin 661 ↪ Fin k) :
    ∃ states, ∀ {Q T : ℕ} {P U : Type}, states ≤ Q →
    ∀ (gs : List RawGate), (∀ g ∈ gs, g ∈ program) →
    ∀ (suffix : List RawGate), (∀ g ∈ suffix, g ∈ program) →
    ∀ (owner : Fin (k+2+1) ↪ Fin T) (body : P → Pr P T Q prime U) (worker : Pr P T Q prime U),
    ∃ (code : Pr P T Q prime U) (rate : ℕ), ∀ {V : ℕ}, 0 < V → ∀ word,
    let rep := fun (x : Fin k → Fin V → ZMod 2) (S : Stacks (k+2+1) prime) =>
      HelperFan (Fin.castAddEmb 1) x S ∧ S.R (Fin.last (k+2)) = word
    ∀ (effect : (Fin k → Fin V → ZMod 2) → Fin k → Fin V → ZMod 2) budget seed, (∀ x u S, rep x (embStk owner S) → PrivateTapes owner seed S →
      ∃ z F n, Exec body worker (mk u S) n (mk z F) ∧ CleanupBound S F n budget ∧
        z.user = u.user ∧ rep (effect x) (embStk owner F)) →
    ∀ x u S, rep x (embStk owner S) → PrivateTapes owner seed S →
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ CleanupBound S F n (rate*V+budget) ∧
        z.user = u.user ∧ rep (suffix.foldl (scalarOwnerEffect layout) (effect (gs.foldl (scalarOwnerEffect layout) x))) (embStk owner F) := by
  obtain ⟨states,compile⟩ := scalarCutoffBlock layout
  refine ⟨states,?_⟩
  intro Q T P U capacity gs allowed suffix suffixAllowed owner body worker
  obtain ⟨gates,rate,run⟩ := compile (U := U) capacity gs allowed
  obtain ⟨last,lastRate,finish⟩ := compile (U := U) capacity suffix suffixAllowed
  refine ⟨((embProg owner Empty.elim gates).seq worker).seq (embProg owner Empty.elim last),rate+lastRate,?_⟩
  intro V pos word rep effect budget seed execute
  intro x u S live stock
  obtain ⟨v,D,n,step,paid,user,out⟩ := moveAfterOwnerGates body owner gates worker rep _ effect _ budget seed
    (fun x => run pos x word) execute x u S live stock
  obtain ⟨q,G,m,tail,cost,same,result⟩ := finish pos _ word (embDn owner v) (embStk owner D) out
  obtain ⟨z,F,placed,_,kept,view,frame⟩ := exec_emb (body' := body) (ι := Empty.elim) owner.injective
    (fun f => nomatch f) tail v rfl D rfl
  rw [← view] at cost
  refine ⟨z,F,_,Exec.seq step placed,?_,kept.trans (same.trans user),view ▸ result⟩
  simpa only [Nat.add_mul,Nat.add_right_comm _ budget] using paid.seq (CleanupBound.place owner frame cost)

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
  obtain ⟨states,build⟩ := scalarCutoffBlock layout
  refine ⟨states,?_⟩
  intro Q capacity
  have compile := build (U := U) capacity
  intro body move
  obtain ⟨blockAllowed,lastAllowed⟩ := phaseMoveBlocks_allowed gs current allowed
  choose gates rate runs using fun i => compile (blocks i) (blockAllowed i)
  obtain ⟨last,lastRate,lastRun⟩ := compile suffix lastAllowed
  obtain ⟨T,fan,host,code,source,run⟩ := moveStockSequence tapes owner body move gates last order (List.nodup_finRange _)
  let overhead := (order.map rate).sum+lastRate
  refine ⟨T,fan,host,code,overhead,source,?_⟩
  intro V pos _ rep
  intro word start step budget seed moves shared
  obtain ⟨view,execute⟩ := run (rep word) (fun x i => (blocks i).foldl (scalarOwnerEffect layout) x) (fun x i => step x (start+i.val) schedule.1[i.val].2) (fun x => suffix.foldl (scalarOwnerEffect layout) x)
    (fun i => rate i*V) budget (lastRate*V) seed (fun x => lastRun pos x word)
    (fun i _ x => runs i pos x word) (fun i _ => moves i) shared
  refine ⟨view,?_⟩
  intro x u D fresh live
  obtain ⟨z,F,n,exec,paid,user,out⟩ := execute x u D fresh live
  rw [← indexedPhase_fold]
  refine ⟨z,F,n,exec,?_,user,out⟩
  have localBound := sumScaled order (fun i => rate i*V) rate V (fun _ => le_rfl)
  intro js distinct
  have charge := paid js distinct
  rw [List.sum_map_add] at charge
  dsimp only [overhead]
  rw [Nat.add_mul]
  apply charge.trans
  apply Nat.add_le_add_left
  rw [Nat.add_right_comm _ (order.map budget).sum]
  exact Nat.add_le_add_right (Nat.add_le_add_right localBound (lastRate*V)) _

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
  exact scalarPhasePair P U layout (sectionD++sectionA) (sectionB++sectionC)
    (Frames.snapshot Frames.initialRefs) (Frames.scatterFinish Frames.beforeScatter)
    (Geometry.Moves.phaseEdges.filter positiveMove) invocationMoveBlocks_order (invocationPhase_allowed false) (invocationPhase_allowed true) tapes owner

open Geometry.Moves in
/-- Both sides of the selected COPY boundary have a final paid MOVE. -/
theorem selectedPhase_hasMove (afterCopy : Bool) :
    let gs := if afterCopy then sectionB++sectionC else sectionD++sectionA
    let cur := if afterCopy then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
    0 < (phaseMoveBlocks gs cur).1.length := by
  intro gs cur
  have size := congrArg List.length (phaseMoveBlocks_spec gs cur).1
  rw [List.length_map] at size
  rw [size]
  have paid {es : List (ℕ × ℕ)} {vs : List ℕ} (profile : es.map value = vs)
      (checked : ∀ e ∈ es, CheckedPair e) (one : 1 ∈ vs) :
      ∃ e ∈ es, positiveMove e = true := by
    rw [← profile,List.mem_map] at one
    obtain ⟨e,mem,h⟩ := one
    exact ⟨e,mem,by simp [positiveMove,rank e (checked e mem),h]⟩
  cases afterCopy with
  | false =>
    obtain ⟨e,mem,h⟩ := paid valuesA_eq checkedA (by decide +kernel)
    apply List.length_pos_of_mem (a := e)
    apply List.mem_filter.mpr
    refine ⟨?_,h⟩
    change e ∈ Frames.edges (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)
    rw [Frames.edges_append,Frames.initial_link,Frames.checkedD]
    exact List.mem_append_right _ mem
  | true =>
    obtain ⟨e,mem,h⟩ := paid valuesB_eq checkedB (by decide +kernel)
    apply List.length_pos_of_mem (a := e)
    apply List.mem_filter.mpr
    refine ⟨?_,h⟩
    change e ∈ Frames.edges (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter)
    rw [Frames.edges_append,Frames.scatter_link]
    exact List.mem_append_left _ mem

/-- Scalar blocks and positive MOVE edges in one selected phase. -/
@[irreducible] noncomputable def selectedPhaseSchedule (afterCopy : Bool) :=
  phaseMoveBlocks (if afterCopy then sectionB++sectionC else sectionD++sectionA)
    (if afterCopy then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs)

/-- The data returned by one selected MOVE with its surrounding scalar gates. -/
noncomputable def selectedMoveOutput {w W : ℕ} (n : Fin 9) (p : Fin 32 × Fin 5) (afterCopy : Bool)
    (i : Fin (selectedPhaseSchedule afterCopy).1.length) (x : Fin 142081 → Fin ((prime^w)^16*W) → ZMod 2) :=
  let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n p.1 p.2,ownerTape_injective ..⟩
  let start := if afterCopy then ((Frames.edges (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)).filter positiveMove).length else 0
  let schedule := selectedPhaseSchedule afterCopy
  let block := schedule.1[i.val]
  let z := moveOwnerEffect owner (block.1.foldl (scalarOwnerEffect owner) x) (start+i.val) block.2
  (if i.val+1 = schedule.1.length then schedule.2 else []).foldl (scalarOwnerEffect owner) z

/-- The ordered worker effects for the phase on one side of COPY. -/
@[irreducible] def InvocationPhaseTrace {w W : ℕ} (n : Fin 9) (p : Fin 32 × Fin 5) (afterCopy : Bool)
    (x : Fin 142081 → Fin ((prime^w)^16*W) → ZMod 2) (next : (Fin 142081 → Fin ((prime^w)^16*W) → ZMod 2) → Prop) : Prop :=
  (List.finRange (selectedPhaseSchedule afterCopy).1.length).foldr
    (fun i tail a => ∃ b, b = selectedMoveOutput n p afterCopy i a ∧ tail b) next x

theorem invocationPhaseOutput_fold {w W : ℕ} (n : Fin 9) (p : Fin 32 × Fin 5) (afterCopy : Bool)
    (x : Fin 142081 → Fin ((prime^w)^16*W) → ZMod 2) (next : (Fin 142081 → Fin ((prime^w)^16*W) → ZMod 2) → Prop) :
    InvocationPhaseTrace n p afterCopy x next ↔ next (invocationPhaseOutput n p afterCopy x) := by
  have fold {α ι : Type} (ls : List ι) (step : α → ι → α) (a : α) (done : α → Prop) :
      ls.foldr (fun i tail v => ∃ b, b = step v i ∧ tail b) done a ↔ done (ls.foldl step a) := by
    induction ls generalizing a with
    | nil => rfl
    | cons i ls ih =>
      constructor
      · rintro ⟨_,rfl,h⟩
        exact (ih _).mp h
      · exact fun h => ⟨_,rfl,(ih _).mpr h⟩
  unfold InvocationPhaseTrace invocationPhaseOutput selectedMoveOutput selectedPhaseSchedule
  dsimp only
  rw [fold]
  apply Iff.of_eq
  apply congrArg next
  exact indexedPhase_lastSuffix _ _ _ _ x _ (selectedPhase_hasMove afterCopy)

/-- The ordered MOVE, COPY, MOVE effects on the shared data realize a borrowed invocation. -/
theorem invocationWindowEffects {w B K : ℕ} (n : Fin 9) (p : Fin 32 × Fin 5)
    (x a b y : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2)
    (left : InvocationPhaseTrace n p false x (fun v => a = v))
    (windows : (List.finRange Copy.lifecycles.length).foldr (fun i tail v => ∃ z,
      CopyFanoutEffect n p.1 p.2 _ (List.getElem_mem (l := Copy.lifecycles) i.isLt) w B K v z ∧ tail z)
      (fun v => v = b) a)
    (right : InvocationPhaseTrace n p true b (fun v => y = v)) : BorrowedStep n w B K p x y := by
  rw [invocationPhaseOutput_fold] at left right
  exact invocationComponentEffects n p x a b y left (copyWindowTrace n p.1 p.2 a b windows) right

theorem phaseDirectory (afterCopy : Bool) :
    let gs := if afterCopy then sectionB++sectionC else sectionD++sectionA
    let cur := if afterCopy then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
    let blocks := (phaseMoveBlocks gs cur).1
    let start := if afterCopy then ((Frames.edges (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)).filter positiveMove).length else 0
    ∃ select : Fin blocks.length → MoveIndex, ∀ i, (select i).val = start+i.val ∧
      (Geometry.Moves.phaseEdges.filter positiveMove)[(select i).val] = blocks[i.val].2 := by
  have count (gs : List RawGate) (cur : ℕ → ℕ) :
      (phaseMoveBlocks gs cur).1.length = ((Frames.edges gs cur).filter positiveMove).length := by
    simpa only [List.length_map] using congrArg List.length (phaseMoveBlocks_spec gs cur).1
  obtain ⟨pre,post,left,right⟩ := invocationMoveIndices
  cases afterCopy
  · exact ⟨pre,fun i => ⟨(left i).1.trans (Nat.zero_add _).symm,(left i).2⟩⟩
  · exact ⟨post,fun i => ⟨(right i).1.trans (congrArg (·+i.val) (count _ _)),(right i).2⟩⟩

/-- The global MOVE occurrence for a local position before or after COPY. -/
noncomputable def selectedPhaseIndex (afterCopy : Bool) :
    Fin (selectedPhaseSchedule afterCopy).1.length → MoveIndex := by
  unfold selectedPhaseSchedule
  exact (phaseDirectory afterCopy).choose

open RecursiveInterchangeLayout Certificates.PR589 in
/-- Compile each MOVE in either literal PR589 phase on its occurrence bank.
The directory selects the recursive child and the final worker also runs the suffix. -/
theorem invocationScalarMove [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) (afterCopy : Bool) :
    let start := if afterCopy then ((Frames.edges (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)).filter positiveMove).length else 0
    let schedule := selectedPhaseSchedule afterCopy
    let blocks := schedule.1
    ∃ select : Fin blocks.length → MoveIndex, ∀ j,
    (select j).val = start+j.val ∧ (Geometry.Moves.phaseEdges.filter positiveMove)[(select j).val] = blocks[j.val].2 ∧
    let i := select j
    let edge := (Geometry.Moves.phaseEdges.filter positiveMove)[i.val]'i.isLt
    let child := phaseChildPositions.choose (n,p,i)
    SelectedOccurrenceWorker child (fun desc _ _ pos => ∀ h, (pos h).val = (CopyChildLayout.packActive desc h).val)
      (fun w B K x y => y = selectedMoveOutput (w := w) (W := B*prime^(64*(w*64))*K) n p afterCopy
        j x) := by
  unfold selectedPhaseSchedule
  intro start schedule blocks
  let layout : Fin 661 ↪ Fin 142081 := ⟨ownerTape n p.1 p.2,ownerTape_injective ..⟩
  let phase := if afterCopy then sectionB++sectionC else sectionD++sectionA
  let cur := if afterCopy then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
  let select := (phaseDirectory afterCopy).choose
  have atIndex := (phaseDirectory afterCopy).choose_spec
  refine ⟨select,fun j => ⟨(atIndex j).1,(atIndex j).2,?_⟩⟩
  intro i edge child
  unfold SelectedOccurrenceWorker
  let gs := blocks[j.val].1
  let suffix := if j.val+1 = blocks.length then schedule.2 else []
  obtain ⟨prefixAllowed,lastAllowed⟩ := phaseMoveBlocks_allowed phase cur (invocationPhase_allowed afterCopy)
  have allowed := prefixAllowed j
  have suffixAllowed : ∀ g ∈ suffix, g ∈ program := by
    dsimp only [suffix]
    split
    · exact lastAllowed
    · simp
  obtain ⟨T,states,ports,fan,basis,owned,build⟩ := invocationMoveLayout layout n p i
  obtain ⟨scalar,compile⟩ := scalarWorkerBlocks layout
  refine ⟨T,max states scalar,ports,fan,basis,owned,?_⟩
  intro P U Q capacity body f bank host owners
  obtain ⟨base,swaps,worker,run⟩ := build ((Nat.le_max_left ..).trans capacity) body f
  obtain ⟨code,rate,execute⟩ := compile ((Nat.le_max_right ..).trans capacity) gs allowed suffix suffixAllowed
    (withCutoffPort fan) host worker
  refine ⟨rate+13*base,13*swaps,0,code,?_⟩
  intro node w B rows width split label M K blocksCount W V desc pos
  obtain ⟨position,coords,prepare⟩ := run node w B rows width split label pos
  refine ⟨position,coords,?_⟩
  intro record
  let initial := cutoffWorkerSeed (basis.seed w W record)
  obtain ⟨archive,step⟩ := prepare record
  refine ⟨archive,?_⟩
  intro budget word call rep x u S privateSeed live
  have positive : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) pos
  obtain ⟨z,F,t,h,cost,user,out⟩ := execute positive word _ _ initial (fun y v D h stock => step budget word call y v D stock h)
    x u S live privateSeed
  have price : rate*V+(budget+nativePrice true ((base+swaps*swapVolumeRate w)*V)) =
      ((rate+13*base)+(13*swaps)*swapVolumeRate w)*V+0+budget := by unfold nativePrice; simp; ring
  refine ⟨z,F,t,_,h,price ▸ cost,user,out,?_⟩
  unfold selectedMoveOutput selectedPhaseSchedule
  change _ = suffix.foldl (scalarOwnerEffect layout)
    (moveOwnerEffect layout (gs.foldl (scalarOwnerEffect layout) x) (start+j.val) blocks[j.val].2)
  rw [← (atIndex j).1,← (atIndex j).2]

open RecursiveInterchangeLayout in
def ChargedPhaseComponent [M8.Machine.Net] (P U : Type) (n : Fin 9) (p : Fin 32 × Fin 5)
    (layout : Fin 661 ↪ Fin 142081) (gs : List RawGate) (cur : ℕ → ℕ) (start : ℕ)
    (select : Fin (phaseMoveBlocks gs cur).1.length → MoveIndex) : Prop :=
    let blocks := (phaseMoveBlocks gs cur).1
    let I := Fin blocks.length
    ∃ (tapes : I → ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (tapes i))
      (states : ℕ),
    ∀ {Q : ℕ}, states ≤ Q → ∀ (body : ∀ i, P → Pr P (tapes i) Q prime U) (f : I → P),
    ∃ (T : ℕ) (fan : Fin (142081+2+1) ↪ Fin T) (host : I × P → Pr (I × P) T Q prime U)
      (code : Pr (I × P) T Q prime U) (overhead : ℕ) (base swaps : I → ℕ),
    ∀ (node : Descriptor) (w B rows : ℕ), node.width = 64*(w+1) → node.rows = 142080*rows →
    node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let W := (M^112*B)*prime^(64*((w+1)*64))*K
    let V := M^16*W
    let desc := fun i => scheduledChild prime node (phaseChildPositions.choose (n,p,select i))
    0 < W → ∃ position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V,
    (∀ i h, ((position i) h).val = (CopyChildLayout.packActive (desc i) h).val) ∧
    ∀ record : I → List (Fin (prime+4)), ∃ initial : Stacks T prime, ∀ (budget : I → ℕ) word,
    (∀ i, ScheduledChildExec node (desc i) w W (ports i) (record i) (position i) (body i) (f i) (budget i) true) →
    let bill := fun i => budget i+nativePrice true ((base i+swaps i*swapVolumeRate w)*V)
    let rep := fun x (S : Stacks T prime) => HelperFan (Fin.castAddEmb 1) x (embStk fan S) ∧ S.R (fan (Fin.last (142081+2))) = word
    ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, PrivateTapes fan initial S → rep x S →
      ∃ z F t, Exec host code (mk u S) t (mk z F) ∧ CleanupBound S F t (overhead*V+((List.finRange blocks.length).map bill).sum) ∧
        z.user = u.user ∧ rep (runIndexedPhase (scalarOwnerEffect layout) (moveOwnerEffect layout) gs cur x start) F

private theorem assemblePhaseComponent [M8.Machine.Net] (P U : Type) (n : Fin 9) (p : Fin 32 × Fin 5)
    (layout : Fin 661 ↪ Fin 142081) (gs : List RawGate) (cur : ℕ → ℕ) (start : ℕ)
    (select : Fin (phaseMoveBlocks gs cur).1.length → MoveIndex) (allowed : ∀ g ∈ gs, g ∈ program)
    (atIndex : ∀ i, (select i).val = start+i.val ∧ (Geometry.Moves.phaseEdges.filter positiveMove)[(select i).val] =
      (phaseMoveBlocks gs cur).1[i.val].2) : ChargedPhaseComponent P U n p layout gs cur start select := by
  classical
  unfold ChargedPhaseComponent
  intro blocks I
  choose tapes qs regs owners _ workers using fun i : I => invocationMoveComponent layout n p (select i)
  obtain ⟨states,compile⟩ := scalarMoveSequence (P := P) (U := U) layout gs cur allowed
    (fun i => tapes i+1) (fun i => withCutoffPort (owners i))
  refine ⟨tapes,regs,max states (Finset.univ.sup qs),?_⟩
  intro Q cap body f
  choose base swaps move run using fun i => workers i ((Finset.le_sup (Finset.mem_univ i)).trans ((le_max_right ..).trans cap)) (body i) (f i)
  obtain ⟨T,fan,host,code,overhead,source,phase⟩ := compile ((le_max_left ..).trans cap)
    (fun i label => embProg (Fin.castAddEmb 1) id (body i label)) move
  refine ⟨T,fan,host,code,overhead,base,swaps,?_⟩
  intro node w B rows width split label M K W V desc pos
  choose position coords prepare using fun i => run i node w B rows width split label pos
  refine ⟨position,coords,?_⟩
  intro record
  choose seed _ execute using fun i => prepare i (record i)
  let blankOwners : Stacks (142081+2+1) prime := ⟨[],[],fun _ => [],fun _ => []⟩
  have size : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) pos
  refine ⟨moveStockSeed source blankOwners seed,?_⟩
  intro budget word children bill rep
  obtain ⟨_,exec⟩ := phase size word start (moveOwnerEffect layout) bill seed (fun i x u S live fresh => by
    obtain ⟨z,F,t,h,cost,user,out⟩ := execute i (budget i) word (children i) x u S fresh live
    refine ⟨z,F,t,h,cost,user,?_⟩
    have index := (atIndex i).1
    have edge := (atIndex i).2
    rw [← index,← edge]
    exact out) blankOwners
  exact exec

/-- Compile either literal phase with its selected physical MOVE workers. -/
theorem invocationPhaseComponent [M8.Machine.Net] (P U : Type) (n : Fin 9) (p : Fin 32 × Fin 5)
    (afterCopy : Bool) :
    let gs := if afterCopy then sectionB++sectionC else sectionD++sectionA
    let cur := if afterCopy then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
    let start := if afterCopy then ((Frames.edges (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)).filter positiveMove).length else 0
    let layout : Fin 661 ↪ Fin 142081 := ⟨ownerTape n p.1 p.2,ownerTape_injective ..⟩
    ∃ select, (∀ i, (select i : MoveIndex).val = start+i.val) ∧ ChargedPhaseComponent P U n p layout gs cur start select := by
  intro gs cur start layout
  let select := (phaseDirectory afterCopy).choose
  have atIndex := (phaseDirectory afterCopy).choose_spec
  exact ⟨select,fun i => (atIndex i).1,assemblePhaseComponent P U n p layout gs cur start select (invocationPhase_allowed afterCopy) atIndex⟩

private theorem directorySum {l : ℕ} (start : ℕ) (child : Fin l → ℕ) (cost : ℕ → ℕ)
    (atIndex : ∀ i, child i = start+i.val) :
    ((List.finRange l).map (fun i => cost (child i))).sum = ((List.range' start l).map cost).sum := by
  induction l generalizing start with
  | zero => rfl
  | succ l ih =>
    rw [List.finRange_succ,List.range'_succ]
    simp only [List.map_cons,List.map_map,List.sum_cons]
    rw [atIndex 0]
    simp only [Fin.val_zero,Nat.add_zero,Nat.add_right_inj]
    exact ih (start+1) (fun i => child i.succ) (fun i => by rw [atIndex]; simp [Nat.add_assoc,Nat.add_comm 1])

/-- The two compiled phase budgets and the nine COPY budgets use precisely
the invocation's contiguous child directory, in pre-COPY, COPY, post-COPY execution order. -/
theorem invocationComponentChildSum (n : Fin 9) (p : Fin 32 × Fin 5) (cost : ℕ → ℕ)
    {left right : ℕ} (pre : Fin left → MoveIndex) (post : Fin right → MoveIndex)
    (first : ∀ i, (pre i).val = i.val) (last : ∀ i, (post i).val = left+i.val)
    (count : left+right = (Geometry.Moves.phaseEdges.filter positiveMove).length) :
    let child := fun j : MoveIndex => (phaseChildPositions.choose (n,p,j)).val
    ((List.finRange left).map (fun i => cost (child (pre i)))).sum +
      ((List.ofFn (fun j : CopyIndex => cost (copyChildPosition (n,p,j)).val)).sum +
       ((List.finRange right).map (fun i => cost (child (post i)))).sum) =
      ((List.range' (stageChildStart n+runChildStart p) Geometry.Moves.localPaid.length).map cost).sum := by
  intro child
  let start := stageChildStart n+runChildStart p
  have offset j : child j = start+j.val := by
    simpa only [child,start,Nat.add_assoc] using (phaseChildPositions.choose_spec n p j).2
  rw [directorySum start _ _ (fun i => (offset (pre i)).trans (congrArg (start+·) (first i))),
      directorySum (start+left) _ _ (fun i => by rw [offset,last]; simp only [start,Nat.add_assoc])]
  have bill (es : List (ℕ × ℕ)) (a : ℕ) :
      indexedBill (fun j _ => cost j) a es = ((List.range' a es.length).map cost).sum := by
    induction es generalizing a with
    | nil => rfl
    | cons e es ih => simp [indexedBill,List.range'_succ,ih]
  have total := invocationChildBill n p (fun _ => 0) cost
  simp only [bill,List.map_const',List.sum_replicate,nsmul_zero,Nat.zero_add] at total
  have join : ((List.range' start left).map cost).sum + ((List.range' (start+left) right).map cost).sum =
      ((List.range' start (Geometry.Moves.phaseEdges.filter positiveMove).length).map cost).sum := by
    rw [← List.sum_append,← List.map_append,List.range'_append_1,count]
  rw [Nat.add_comm ((List.ofFn _).sum),← Nat.add_assoc,join]
  exact total

/-- Split the three actual execution bills into the local work and the child
sum required by the recursive node. The COPY sequence pays one final step. -/
theorem invocationComponentBudget (n : Fin 9) (p : Fin 32 × Fin 5) (cost : ℕ → ℕ)
    {left right : ℕ} (pre : Fin left → MoveIndex) (post : Fin right → MoveIndex)
    (first : ∀ i, (pre i).val = i.val) (last : ∀ i, (post i).val = left+i.val)
    (count : left+right = (Geometry.Moves.phaseEdges.filter positiveMove).length)
    (leftScalar rightScalar : ℕ) (leftMove : Fin left → ℕ) (rightMove : Fin right → ℕ) (copy : CopyIndex → ℕ) :
    let child := fun j : MoveIndex => cost (phaseChildPositions.choose (n,p,j)).val
    let leftBill := leftScalar+((List.finRange left).map (fun i => child (pre i)+leftMove i)).sum
    let rightBill := rightScalar+((List.finRange right).map (fun i => child (post i)+rightMove i)).sum
    let copyBill := (List.ofFn copy).sum+(List.ofFn (fun j : CopyIndex => cost (copyChildPosition (n,p,j)).val)).sum+1
    leftBill+(copyBill+rightBill) =
      leftScalar+rightScalar+((List.finRange left).map leftMove).sum+((List.finRange right).map rightMove).sum+
        (List.ofFn copy).sum+1+((List.range' (stageChildStart n+runChildStart p) Geometry.Moves.localPaid.length).map cost).sum := by
  dsimp only
  rw [List.sum_map_add,List.sum_map_add,← invocationComponentChildSum n p cost pre post first last count]
  dsimp only
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
