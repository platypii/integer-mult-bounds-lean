module

public import IntegerMultBounds.MathlibTM2.M6.BitIdleParentArchive
public import IntegerMultBounds.MathlibTM2.M6.BitScheduledSeededRows

/-! Prepare the parent role directory once and retain it across scheduled MOVE calls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

def moveRoleFields {T : ℕ} (bank : Fin (80+273) ↪ Fin T) : Fin 6 ↪ Fin T :=
  (((Fin.natAddEmb 38 (m := 6)).trans (Fin.castAddEmb 36)).trans (Fin.castAddEmb 273)).trans bank

def moveMasterInputs : Fin 3 ↪ Fin 12 := ⟨![9,7,5],by decide⟩

def moveHeaderBank {T : ℕ} (master : Fin 12 ↪ Fin T) (scratch : Fin 35 ↪ Fin T)
    (apart : ∀ i j, master i ≠ scratch j) : Fin 38 ↪ Fin T :=
  Fin.Embedding.append (Set.disjoint_range_iff.mpr (fun i j => apart (moveMasterInputs i) j) :
    Disjoint (Set.range (moveMasterInputs.trans master)) (Set.range scratch))

/-- Read-only inputs shared by the parent's scheduled MOVE invocations. -/
structure ParentMoveDirectory {T : ℕ} (p : CutoffNodeInput) (master : Fin 12 ↪ Fin T)
    (fields : Fin 6 ↪ Fin T) (S : Stacks T prime) : Prop where
  words : ∀ i, S.R (master i) = nodeSeedWords p i
  roleWords : ∀ i, S.R (fields i) = (Routines.hdr (role p.node 142080) i).map bitSymbol

theorem prepareMoveDirectory {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin (80+273) ↪ Fin T) (master : Fin 12 ↪ Fin T) (apart : ∀ i j, bank i ≠ master j)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q) :
    ∃ code rate, ∀ (p : CutoffNodeInput) u (S : Stacks T prime),
      (∀ i, S.R (master i) = nodeSeedWords p i) → (∀ i, S.L (bank i) = [] ∧ S.R (bank i) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (rate*p.cells) ∧ ParentMoveDirectory p master (moveRoleFields bank) F ∧
        ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨a,compile⟩ := loadNodeArchive
  obtain ⟨load,install⟩ := compile body bank master apart
  obtain ⟨divide,b,run⟩ := idleParentRoleHeaders body bank capacity
  refine ⟨load.seq divide,a+b,?_⟩
  intro p u S words empty
  obtain ⟨v,D,n,exec,user,paid,stored,off⟩ := install p u S words empty
  have ready : ParentArchiveInput p.node p.w (embStk bank D) := by
    have left : (embStk bank D).L = (parentArchiveSeed p.node p.w).L := funext (fun i => (stored i).1)
    have right : (embStk bank D).R = (parentArchiveSeed p.node p.w).R := funext (fun i => (stored i).2)
    have transfer {A B : Stacks (80+273) prime} (hl : A.L = B.L) (hr : A.R = B.R)
        (spec : ParentArchiveInput p.node p.w B) : ParentArchiveInput p.node p.w A := by
      simpa only [ParentArchiveInput,embStk,hl,hr] using spec
    exact transfer left right (parentArchiveSeed_ready p.node p.w)
  obtain ⟨z,F,m,finish,same,bill,fields,frame⟩ := run p v D ready
  have keep j (h : ∀ i, bank i ≠ j) := And.intro ((frame j h).1.trans (off j h).1) ((frame j h).2.trans (off j h).2)
  refine ⟨z,F,n+m,exec.seq finish,same.trans user,?_,⟨fun i => (keep _ (fun j => apart j i)).2.trans (words i),fields⟩,keep⟩
  simpa only [Nat.add_mul] using paid.seq bill

/-- Read the clock, radix, middle field and cutoff on the original master tapes.
The directory survives the call for the next occurrence. -/
theorem parentDirectoryMove {P R U : Type} {T H Q scratchCount : ℕ}
    (body : P → Pr P T Q prime U) (entry : P) (src dst : Fin (142081+2) ↪ Fin T)
    (ret : Fin 3 ↪ Fin T) (tmp buf : Fin T) (place : Fin T ↪ Fin H) (host : R → Pr R H Q prime U)
    (payload count saved aux : Fin H) (seed : CutoffNodeInput → Stacks T prime)
    (master : Fin 12 ↪ Fin H) (scratch : Fin 35 ↪ Fin H) (distinct : ∀ i j, master i ≠ scratch j)
    (fields : Fin 6 ↪ Fin H) (temp : Fin H) (counter : Fin 9 ↪ Fin H)
    (apart : [payload,temp,counter 0].Nodup)
    (payloadMaster : ∀ j, master j ≠ payload) (payloadFields : ∀ j, fields j ≠ payload)
    (i : Fin nodeChildren5.length) :
    let r := moveHeaderBank master scratch distinct
    let cut := master 0
    (∀ i j, fields i ≠ r j) → (∀ j, counter 2 ≠ r j) →
    (∀ i, fields i ≠ counter 2) → cut ≠ counter 2 →
    ( SeededSuspendedRows body entry src dst ret tmp buf place host payload count saved aux
      nodeSeedWords CutoffNodeInput.cells seed (moveSeedHeaders r fields cut) scratchCount) →
    let slots := frameSlots place
    let cleanup := counter 2 :: moveSeedOutputs r
    let Label := (Fin T × Bool) ⊕ R
    payload ∉ cleanup → count ∉ cleanup → saved ∉ cleanup → aux ∉ cleanup →
    (∀ j, place j ∉ cleanup) →
    ∃ (table : Label → Pr Label H Q prime U) (code : Pr Label H Q prime U) (rate : ℕ),
      (∀ f, table (.inr f) = stateMapProg id id Sum.inr (host f)) ∧
      ∀ (p c : CutoffNodeInput) price, c.node = scheduledChild prime p.node i →
      PackedPieceHandoffWithCharge cleanupWeight c.cells (packedChildOutput (c.w+1) c.cells)
        body (body entry) src dst (seed c) price →
      (seed c).L tmp = [] → (seed c).R tmp = [] → (seed c).R buf = [] →
      (∀ j, (seed c).L (ret j) = [] ∧ (seed c).R (ret j) = []) →
      let wide := packedDescriptor c.node.width (CopyChildLayout.spectators c.node)
      ∀ u (S : Stacks H prime) (x : Fin (volume prime wide) → ZMod 2),
      RecordPayload payload (fun _ => blank) 0 x S → S.L temp = [] → S.R temp = [] →
      (∀ j, S.R (counter j) = []) →
      ParentMoveDirectory p master fields S →
      (∀ j, S.R (scratch j) = []) →
      p.root.width.size = c.root.width.size → p.cutoff = c.cutoff →
      (∀ j ∈ cleanup, S.L j = [] ∧ S.R j = []) →
      S.R count = [] → S.R saved = [] → S.L aux = [] → S.R aux = [] →
      ∃ z F t, Exec table code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (price+(1000512056*p.cells)+(nodeHeaderSetupRate+25+rate)*c.cells+
          4*(scratchCount+slots.length)+112+(prime+8)*(slots.map (fun j => (S.L j).length+(S.R j).length+2)).sum) ∧
        RecordPayload payload (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (v := wide) (one_dvd wide.rows) x) F ∧
        ParentMoveDirectory p master fields F ∧
        ∀ j, j ≠ payload → F.L j = S.L j ∧ F.R j = S.R j := by
  intro r cut fieldOff rowOff inheritedOff cutRow rows slots cleanup Label payloadOff countOff savedOff auxOff bankOff
  have cutOff (j) : cut ≠ r j := by
    induction j using Fin.addCases (m := 3) (n := 35) with
    | left j =>
      have ne : (0 : Fin 12) ≠ moveMasterInputs j := (by decide : ∀ i, 0 ≠ moveMasterInputs i) j
      simpa [r,cut,moveHeaderBank,Fin.Embedding.append] using master.injective.ne ne
    | right j => simpa [r,cut,moveHeaderBank,Fin.Embedding.append] using distinct 0 j
  obtain ⟨table,code,rate,labels,run⟩ := scheduledSeededRows body entry src dst ret tmp buf place host payload
    count saved aux seed r fields cut temp counter apart fieldOff cutOff rowOff inheritedOff cutRow i rows
    payloadOff countOff savedOff auxOff bankOff
  refine ⟨table,code,rate,labels,?_⟩
  intro p c price child handoff tl tr br vacant wide u S x input left right empty directory free root threshold fresh hc hs al ar
  have clock : (S.R (r 0)).length = p.w := by
    change (S.R (master 9)).length = p.w
    rw [directory.words]
    exact List.length_replicate
  have radix : S.R (r 1) = binSyms (prime^(p.w+1)).size (prime^(p.w+1)) := directory.words 7
  have middle : S.R (r 2) = (Routines.hdr p.node 4).map bitSymbol := directory.words 5
  have unused (j : Fin 38) (hj : 3 ≤ j.val) : S.R (r j) = [] := by
    induction j using Fin.addCases (m := 3) (n := 35) with
    | left j => exact False.elim (Nat.not_le_of_lt j.isLt hj)
    | right j => simpa [r,moveHeaderBank,Fin.Embedding.append] using free j
  have cutoff : S.R cut = binSyms c.root.width.size c.cutoff := by
    change S.R (master 0) = _
    rw [← root,← threshold]
    exact directory.words 0
  obtain ⟨z,F,t,exec,user,paid,out,frame⟩ := run p c price child handoff tl tr br vacant u S x input
    left right empty clock radix middle unused (fun j _ _ => directory.roleWords j) cutoff fresh hc hs al ar
  exact ⟨z,F,t,exec,user,paid,out,⟨fun j => (frame _ (payloadMaster j)).2.trans (directory.words j),
    fun j => (frame _ (payloadFields j)).2.trans (directory.roleWords j)⟩,frame⟩

/-- Scope the role directory around a whole sequence of calls. The setup and
retirement costs occur once, regardless of how many occurrences share it. -/
theorem withMoveDirectory {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin (80+273) ↪ Fin T) (master : Fin 12 ↪ Fin T) (apart : ∀ i j, bank i ≠ master j)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q) :
    ∃ (setup : Pr P T Q prime U) (rate : ℕ), ∀ (worker : Pr P T Q prime U) (p : CutoffNodeInput) (price : ℕ)
      (payload : Fin T) (external : ∀ i, bank i ≠ payload) {N : ℕ} (y : Fin N → ZMod 2) u (S : Stacks T prime),
      (∀ i, S.R (master i) = nodeSeedWords p i) → (∀ i, S.L (bank i) = [] ∧ S.R (bank i) = []) →
      (∀ a D, ParentMoveDirectory p master (moveRoleFields bank) D →
        (∀ j, (∀ i, bank i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
        ∃ b G m, Exec body worker (mk a D) m (mk b G) ∧ b.user = a.user ∧
          CleanupBound D G m price ∧ RecordPayload payload (fun _ => blank) 0 y G ∧
          ∀ j, j ≠ payload → (∀ i, bank i ≠ j) → G.L j = D.L j ∧ G.R j = D.R j) →
      ∃ z F t, Exec body ((setup.seq worker).seq (clearWorkTapes (frameSlots bank))) (mk u S) t (mk z F) ∧
        z.user = u.user ∧ CleanupBound S F t (rate*p.cells+price+4*(80+273)+1) ∧
        RecordPayload payload (fun _ => blank) 0 y F ∧
        ∀ j, j ≠ payload → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨setup,rate,install⟩ := prepareMoveDirectory body bank master apart capacity
  refine ⟨setup,rate,?_⟩
  intro worker p price payload external N y u S words fresh invoke
  obtain ⟨a,D,n,start,user,paid,ready,frame⟩ := install p u S words fresh
  obtain ⟨b,G,m,run,same,cost,out,keep⟩ := invoke a D ready frame
  let slots := frameSlots bank
  have nd : slots.Nodup := by simpa [slots,frameSlots] using (List.nodup_finRange _).map bank.injective
  obtain ⟨z,zu,erase⟩ := clearWorkTapes_exec body slots nd b G
  let F := clearSlots slots G
  have clean j (h : j ∈ slots) : F.L j = [] ∧ F.R j = [] := by simp [F,clearSlots,replaceBank,h]
  have empty j (h : j ∈ slots) : S.L j = [] ∧ S.R j = [] := by
    obtain ⟨i,rfl⟩ := (mem_frameSlots _ _).1 h
    exact fresh i
  have bill := cleanupBound_clearBank slots nd (paid.seq cost) (Nat.le_refl (tapeCharge cleanupWeight slots G+1))
    (F := F) clean (fun j => by by_cases h : j ∈ slots <;> simp [F,clearSlots,replaceBank,h])
  have init : tapeCharge cleanupWeight slots S = 4*(80+273) := by
    unfold tapeCharge
    rw [List.map_congr_left (g := fun _ => 4) (fun j h => congrArg₂ cleanupWeight (empty j h).1 (empty j h).2)]
    simp only [List.map_const',List.sum_replicate,smul_eq_mul,slots,frameSlots,List.length_reverse,
      List.length_map,List.length_finRange]
  have off : payload ∉ slots := fun h => by
    obtain ⟨i,e⟩ := (mem_frameSlots _ _).1 h
    exact external i e
  refine ⟨z,F,_,(start.seq run).seq erase,zu.trans (same.trans user),init ▸ bill,?_,?_⟩
  · intro j
    simpa only [F,clearSlots,replaceBank,ite_eq_right off] using out j
  · intro j ne
    by_cases h : j ∈ slots
    · simp [F,clearSlots,replaceBank,h,(empty j h).1,(empty j h).2]
    · have outside (i) : bank i ≠ j := fun e => h ((mem_frameSlots _ _).2 ⟨i,e⟩)
      have g := keep j ne outside
      have d := frame j outside
      simpa [F,clearSlots,replaceBank,h] using And.intro (g.1.trans d.1) (g.2.trans d.2)

end IntegerMultBounds.MathlibTM2.M6.BitNode
