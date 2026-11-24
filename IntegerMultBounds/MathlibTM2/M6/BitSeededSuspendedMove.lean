module

public import IntegerMultBounds.MathlibTM2.M6.BitSuspendedMove

/-! Load the packed child's private seed inside the saved physical bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback RecursiveInterchangeLayout
open Shared50ModularControl (prime)

private theorem frameDistinct {k H : ℕ} (ports : Fin k ↪ Fin H) : (frameSlots ports).Nodup := by
  simpa [frameSlots] using (List.nodup_finRange _).map ports.injective

private theorem frameLength {k H : ℕ} (ports : Fin k ↪ Fin H) : (frameSlots ports).length = k := by
  simp [frameSlots]

private theorem mem_moveScratch {T H k r : ℕ} (src : Fin k ↪ Fin T) (ret : Fin r ↪ Fin T)
    (apart : ∀ i j, ret i ≠ src j) (place : Fin T ↪ Fin H) (j : Fin H) :
    j ∈ frameSlots (moveFramePorts src ret apart place) ↔
      (∃ i, place (ret i) = j) ∨ ∃ i, place (src i) = j := by
  rw [mem_frameSlots]
  constructor
  · rintro ⟨i,rfl⟩
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i,by simp [moveFramePorts,Fin.Embedding.append]⟩
    | right i => exact Or.inr ⟨i,by simp [moveFramePorts,Fin.Embedding.append]⟩
  · rintro (⟨i,rfl⟩|⟨i,rfl⟩)
    · exact ⟨i.castAdd _,by simp [moveFramePorts,Fin.Embedding.append]⟩
    · exact ⟨i.natAdd _,by simp [moveFramePorts,Fin.Embedding.append]⟩

/-- A suspended packed child receives its private seed from the header tapes. -/
def SeededSuspendedRowsWithReserve {P R U Config : Type} {T H Q h : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (src dst : Fin (142081+2) ↪ Fin T) (ret : Fin 3 ↪ Fin T) (tmp buf : Fin T)
    (place : Fin T ↪ Fin H) (host : R → Pr R H Q prime U) (payload count saved aux : Fin H)
    (words : Config → Fin h → List (Fin (prime+4))) (cells : Config → ℕ) (seed : Config → Stacks T prime)
    (headers : Fin h → Fin H) (scratchCount : ℕ)
    (reserve : (Fin 2 → List (Fin (prime+4))) → (Fin 2 → List (Fin (prime+4))) → ℕ) : Prop :=
    let slots := frameSlots place
    let Label := (Fin T × Bool) ⊕ R
    ∃ (table : Label → Pr Label H Q prime U) (code : Pr Label H Q prime U) (rate : ℕ),
      (∀ f, table (.inr f) = stateMapProg id id Sum.inr (host f)) ∧
      ∀ c (child : Descriptor) (atom price : ℕ), child.width = 64*atom → 142080 ∣ child.rows →
      let m := volume prime (packedDescriptor (64*atom) (CopyChildLayout.spectators child/142080))
      let wide := packedDescriptor child.width (CopyChildLayout.spectators child)
      PackedPieceHandoffWithReserve cleanupWeight reserve m (packedChildOutput atom m) body (body entry) src dst (seed c) price →
      0 < m → (seed c).L tmp = [] → (seed c).R tmp = [] → (seed c).R buf = [] →
      (∀ i, (seed c).L (ret i) = [] ∧ (seed c).R (ret i) = []) →
      ∀ (x : Fin (volume prime wide) → ZMod 2) u (S : Stacks H prime),
      RecordPayload payload (fun _ => blank) 0 x S → (∀ i, S.R (headers i) = words c i) →
      S.R count = [] → S.R saved = [] → S.L aux = [] → S.R aux = [] →
      ∃ z F n, Exec table code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (rate*cells c+4*scratchCount+1+(price+1000000034*volume prime wide+49)+
          4*slots.length+1+(prime+8)*(slots.map (fun j => (S.L j).length+(S.R j).length+2)).sum) ∧
        RecordPayload payload (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (v := wide) (one_dvd wide.rows) x) F ∧
        ∀ j, j ≠ payload → F.L j = S.L j ∧ F.R j = S.R j

def SeededSuspendedRows {P R U Config : Type} {T H Q h : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (src dst : Fin (142081+2) ↪ Fin T) (ret : Fin 3 ↪ Fin T) (tmp buf : Fin T)
    (place : Fin T ↪ Fin H) (host : R → Pr R H Q prime U) (payload count saved aux : Fin H)
    (words : Config → Fin h → List (Fin (prime+4))) (cells : Config → ℕ) (seed : Config → Stacks T prime)
    (headers : Fin h → Fin H) (scratchCount : ℕ) : Prop :=
  SeededSuspendedRowsWithReserve body entry src dst ret tmp buf place host payload count saved aux
    words cells seed headers scratchCount (fun _ _ => 0)

private theorem seededRowsWithScratch {P R U Config : Type} {T H Q h : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (src dst : Fin (142081+2) ↪ Fin T) (ret : Fin 3 ↪ Fin T)
    (srcOff : ∀ i j, ret i ≠ src j) (dstOff : ∀ i j, ret i ≠ childReturnFan dst j)
    (tmp buf : Fin T) (srcTmp : ∀ i, src i ≠ tmp) (srcBuf : ∀ i, src i ≠ buf)
    (retTmp : ∀ i, ret i ≠ tmp) (retBuf : ∀ i, ret i ≠ buf) (distinct : tmp ≠ buf)
    (place : Fin T ↪ Fin H) (label : P → R) (host : R → Pr R H Q prime U)
    (installed : ∀ f, host (label f) = embProg place label (body f))
    (payload count saved aux : Fin H)
    (outside : ∀ i, place i ≠ payload ∧ place i ≠ count ∧ place i ≠ saved ∧ place i ≠ aux)
    (separate : [count,place (ret 0),payload,saved,aux].Nodup)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (words : Config → Fin h → List (Fin (prime+4))) (cells : Config → ℕ) (seed : Config → Stacks T prime)
    (loader : LoadsPackedSeed words cells seed) (headers : Fin h → Fin H)
    (away : ∀ i j, place i ≠ headers j) {k : ℕ} (fan : Fin k ↪ Fin H)
    (belongs : ∀ j, j ∈ frameSlots fan ↔ (∃ i, place (ret i) = j) ∨ ∃ i, place (src i) = j)
    (reserve : (Fin 2 → List (Fin (prime+4))) → (Fin 2 → List (Fin (prime+4))) → ℕ)
    (bounded : ∀ l r, reserve l r ≤ ∑ i, cleanupWeight (l i) (r i)) :
    SeededSuspendedRowsWithReserve body entry src dst ret tmp buf place host payload count saved aux words cells seed headers k reserve := by
  unfold SeededSuspendedRowsWithReserve
  intro slots Label
  obtain ⟨rate,compile⟩ := loader
  obtain ⟨loadSeed,load⟩ := compile host place headers away
  obtain ⟨move,execute⟩ := packedRowsOnChildBankWithReserve body entry src dst ret srcOff dstOff tmp buf
    srcTmp srcBuf retTmp retBuf distinct place label host installed payload count saved aux outside separate capacity
  let scratch := frameSlots fan
  let worker := (loadSeed.seq (clearWorkTapes scratch)).seq move
  obtain ⟨table,code,labels,wrap⟩ := installedSuspendedMove place host worker
  refine ⟨table,code,rate,labels,?_⟩
  intro c child atom price aligned groups m wide handoff pos tl tr br vacant x u S input atHeaders hc hs al ar
  have off (j) (a : ∀ i, place i ≠ j) : j ∉ slots := fun mem => by
    obtain ⟨i,e⟩ := (mem_frameSlots _ _).1 mem
    exact a i e
  have on (i : Fin T) : place i ∈ slots := (mem_frameSlots _ _).2 ⟨i,rfl⟩
  have payloadOff := off payload (fun i => (outside i).1)
  have call := wrap payload payloadOff u S (Shared50RecursiveNodeRows.transpose (v := wide) (one_dvd wide.rows) x)
    (rate*cells c+4*k+1+(price+1000000034*volume prime wide+49))
    (fun j => j ≠ payload ∧ ∀ i, place i ≠ j)
  obtain ⟨z,F,n,exec,user,paid,out,frame⟩ := call (by
    intro v
    let D := clearSlots slots S
    have blank (i) : D.L (place i) = [] ∧ D.R (place i) = [] := by simp [D,clearSlots,replaceBank,on]
    obtain ⟨a,B,t,init,user,paid,loaded,frame⟩ := load c v D
      (fun j => by simpa [D,clearSlots,replaceBank,off _ (fun i => away i j)] using atHeaders j) blank
    have nd : scratch.Nodup := frameDistinct fan
    obtain ⟨b,same,erase⟩ := clearWorkTapes_exec host scratch nd a B
    let G := clearSlots scratch B
    have cleared j (h : j ∈ scratch) : G.L j = [] ∧ G.R j = [] := by simp [G,clearSlots,replaceBank,h]
    have kept j (apart : ∀ i, place i ≠ j) : G.L j = S.L j ∧ G.R j = S.R j := by
      have h : j ∉ scratch := fun e => ((belongs _).1 e).elim (fun ⟨i,eq⟩ => apart _ eq) (fun ⟨i,eq⟩ => apart _ eq)
      simpa [G,D,clearSlots,replaceBank,h,off _ apart] using frame j apart
    have privateAt j (a : ∀ i, src i ≠ j) (b : ∀ i, ret i ≠ j) :
        G.L (place j) = (seed c).L j ∧ G.R (place j) = (seed c).R j := by
      have h : place j ∉ scratch := fun e => ((belongs _).1 e).elim
        (fun ⟨i,eq⟩ => b i (place.injective eq)) (fun ⟨i,eq⟩ => a i (place.injective eq))
      simpa [G,clearSlots,replaceBank,h] using loaded j
    have pay := cleanupBound_clearBank scratch nd paid (Nat.le_refl (tapeCharge cleanupWeight scratch B+1))
      (F := G) cleared (fun j => by by_cases h : j ∈ scratch <;> simp [G,clearSlots,replaceBank,h])
    have charge : tapeCharge cleanupWeight scratch D = 4*k := by
      unfold tapeCharge
      rw [List.map_congr_left (g := fun _ => 4) (fun j mem => by
        rcases (belongs _).1 mem with ⟨i,rfl⟩ | ⟨i,rfl⟩ <;>
          exact congrArg₂ cleanupWeight (blank _).1 (blank _).2)]
      simp only [List.map_const',List.sum_replicate,smul_eq_mul,frameLength,Nat.mul_comm,scratch]
    rw [charge] at pay
    have p := kept payload (fun i => (outside i).1)
    obtain ⟨z,F,n,run,zu,cost,out,endFrame⟩ := execute child atom price (seed c) reserve aligned groups bounded handoff pos x b G
      (fun j => by simpa only [p.1,p.2] using input j) ((kept _ (fun i => (outside i).2.1)).2.trans hc)
      ((kept _ (fun i => (outside i).2.2.1)).2.trans hs) ((kept _ (fun i => (outside i).2.2.2)).1.trans al)
      ((kept _ (fun i => (outside i).2.2.2)).2.trans ar)
      (fun i => cleared _ ((belongs _).2 (Or.inr ⟨i,rfl⟩))) (fun i => cleared _ ((belongs _).2 (Or.inl ⟨i,rfl⟩)))
      ((privateAt tmp srcTmp retTmp).1.trans tl) ((privateAt tmp srcTmp retTmp).2.trans tr)
      ((privateAt buf srcBuf retBuf).2.trans br) vacant privateAt
    refine ⟨z,F,_,(init.seq erase).seq run,zu.trans (same.trans user),pay.seq cost,out,?_⟩
    intro j h _
    exact ⟨(endFrame j h.1 h.2).1.trans (kept j h.2).1,(endFrame j h.1 h.2).2.trans (kept j h.2).2⟩)
  refine ⟨z,F,n,exec,user,paid,out,fun j ne => frame j ?_⟩
  by_cases h : j ∈ slots
  · exact Or.inl h
  · exact Or.inr ⟨ne,fun i e => h (e ▸ on i)⟩

theorem seededSuspendedMoveWithReserve {P R U Config : Type} {T H Q h : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (src dst : Fin (142081+2) ↪ Fin T) (ret : Fin 3 ↪ Fin T)
    (srcOff : ∀ i j, ret i ≠ src j) (dstOff : ∀ i j, ret i ≠ childReturnFan dst j)
    (tmp buf : Fin T) (srcTmp : ∀ i, src i ≠ tmp) (srcBuf : ∀ i, src i ≠ buf)
    (retTmp : ∀ i, ret i ≠ tmp) (retBuf : ∀ i, ret i ≠ buf) (distinct : tmp ≠ buf)
    (place : Fin T ↪ Fin H) (label : P → R) (host : R → Pr R H Q prime U)
    (installed : ∀ f, host (label f) = embProg place label (body f))
    (payload count saved aux : Fin H)
    (outside : ∀ i, place i ≠ payload ∧ place i ≠ count ∧ place i ≠ saved ∧ place i ≠ aux)
    (separate : [count,place (ret 0),payload,saved,aux].Nodup)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (words : Config → Fin h → List (Fin (prime+4))) (cells : Config → ℕ) (seed : Config → Stacks T prime)
    (loader : LoadsPackedSeed words cells seed) (headers : Fin h → Fin H)
    (away : ∀ i j, place i ≠ headers j)
    (reserve : (Fin 2 → List (Fin (prime+4))) → (Fin 2 → List (Fin (prime+4))) → ℕ)
    (bounded : ∀ l r, reserve l r ≤ ∑ i, cleanupWeight (l i) (r i)) :
    SeededSuspendedRowsWithReserve body entry src dst ret tmp buf place host payload count saved aux words cells seed headers (3+(142081+2)) reserve :=
  seededRowsWithScratch body entry src dst ret srcOff dstOff tmp buf srcTmp srcBuf retTmp retBuf distinct
    place label host installed payload count saved aux outside separate capacity words cells seed loader headers away
    (moveFramePorts src ret srcOff place) (mem_moveScratch src ret srcOff place) reserve bounded

theorem seededSuspendedMove {P R U Config : Type} {T H Q h : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (src dst : Fin (142081+2) ↪ Fin T) (ret : Fin 3 ↪ Fin T)
    (srcOff : ∀ i j, ret i ≠ src j) (dstOff : ∀ i j, ret i ≠ childReturnFan dst j)
    (tmp buf : Fin T) (srcTmp : ∀ i, src i ≠ tmp) (srcBuf : ∀ i, src i ≠ buf)
    (retTmp : ∀ i, ret i ≠ tmp) (retBuf : ∀ i, ret i ≠ buf) (distinct : tmp ≠ buf)
    (place : Fin T ↪ Fin H) (label : P → R) (host : R → Pr R H Q prime U)
    (installed : ∀ f, host (label f) = embProg place label (body f))
    (payload count saved aux : Fin H)
    (outside : ∀ i, place i ≠ payload ∧ place i ≠ count ∧ place i ≠ saved ∧ place i ≠ aux)
    (separate : [count,place (ret 0),payload,saved,aux].Nodup)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (words : Config → Fin h → List (Fin (prime+4))) (cells : Config → ℕ) (seed : Config → Stacks T prime)
    (loader : LoadsPackedSeed words cells seed) (headers : Fin h → Fin H)
    (away : ∀ i j, place i ≠ headers j) :
    SeededSuspendedRows body entry src dst ret tmp buf place host payload count saved aux words cells seed headers (3+(142081+2)) :=
  seededSuspendedMoveWithReserve body entry src dst ret srcOff dstOff tmp buf srcTmp srcBuf retTmp retBuf distinct
    place label host installed payload count saved aux outside separate capacity words cells seed loader headers away
    (fun _ _ => 0) (fun _ _ => Nat.zero_le _)

/-- Run a seeded child from the scheduled record, preserving every tape except its payload. -/
theorem openedSeededMove {P R U Config : Type} {T H Q h scratchCount : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (src dst : Fin (142081+2) ↪ Fin T) (ret : Fin 3 ↪ Fin T) (tmp buf : Fin T)
    (place : Fin T ↪ Fin H) (host : R → Pr R H Q prime U) (bank : Fin 35 ↪ Fin H)
    (spectator count saved aux : Fin H) (apart : ∀ i, bank i ≠ spectator) (words : Config → Fin h → List (Fin (prime+4))) (cells : Config → ℕ)
    (seed : Config → Stacks T prime) (headers : Fin h → Fin H)
    (rows : SeededSuspendedRows body entry src dst ret tmp buf place host (bank 24) count saved aux words cells seed headers scratchCount)
    (rank : ℕ) (widthOff : bank 1 ∉ frameSlots place) :
    let slots := frameSlots place
    let Label := (Fin T × Bool) ⊕ R
    ∃ (table : Label → Pr Label H Q prime U) (code : Pr Label H Q prime U) (rate : ℕ),
      (∀ f, table (.inr f) = stateMapProg id id Sum.inr (host f)) ∧
      ∀ c (child : Descriptor) (atom w W L cutoff price : ℕ),
      child.width = 64*atom → 142080 ∣ child.rows → child.width = (w+1)*rank →
      let m := volume prime (packedDescriptor (64*atom) (CopyChildLayout.spectators child/142080))
      PackedPieceHandoffWithCharge cleanupWeight m (packedChildOutput atom m) body (body entry) src dst (seed c) price →
      0 < m → let V := (prime^(w+1))^16*W
      ∀ position : Fin (volume prime child) ≃ Fin V,
      (∀ i, (position i).val = (CopyChildLayout.packActive child i).val) →
      let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size
        (binSyms L cutoff) SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
      ∀ u (S : Stacks H prime) x, stored x S →
      S.R spectator = binSyms (CopyChildLayout.spectators child).size (CopyChildLayout.spectators child) →
      let opened := {S with R := Function.update S.R (bank 1) (binSyms child.width.size child.width)}
      (∀ i, opened.R (headers i) = words c i) →
      opened.R count = [] → opened.R saved = [] → opened.L aux = [] → opened.R aux = [] →
      (seed c).L tmp = [] → (seed c).R tmp = [] → (seed c).R buf = [] →
      (∀ i, (seed c).L (ret i) = [] ∧ (seed c).R (ret i) = []) →
      let charge := rate*cells c+4*scratchCount+1+(price+1000000034*V+49)+4*slots.length+1+
        (prime+8)*(slots.map (fun j => (S.L j).length+(S.R j).length+2)).sum
      ∃ z F t y, Exec table code (mk u S) t (mk z F) ∧
        CleanupBound S F t (charge+4*w+23*child.width+16*child.width.size+37) ∧
        z.user = u.user ∧ stored y F ∧ (∀ j, j ≠ bank 24 → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ i, y (position i) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) i := by
  intro slots Label
  obtain ⟨table,wrapper,rate,labels,run⟩ := rows
  refine ⟨table,openedPackedMoveProgram wrapper bank rank [],rate,labels,?_⟩
  intro c child atom w W L cutoff price aligned groups width m handoff pos V position packed
    stored u S x ready spec opened atHeaders hc hs al ar tl tr br vacant charge
  apply openedPackedMoveCallerAt table wrapper bank spectator apart rank [] (by simp) (by simp) child w W L cutoff
    charge position width packed u S x ready spec (by simp)
  intro v G _ _ _ payload
  let wide := packedDescriptor child.width (CopyChildLayout.spectators child)
  have size : volume prime wide = V := by
    have h := Fintype.card_congr position
    simp only [Fintype.card_fin] at h
    rw [← h]
    simp only [wide,volume,packedDescriptor,CopyChildLayout.spectators,one_mul,mul_one]
    ring
  let data := fun i : Fin (volume prime wide) => x (i.cast size)
  have castWord {a b : ℕ} (h : a = b) (f : Fin b → ZMod 2) :
      List.ofFn (fun i : Fin a => f (i.cast h)) = List.ofFn f := by subst b; rfl
  change RecordPayload (bank 24) (fun _ => blank) 0 x opened at payload
  have castPayload : RecordPayload (bank 24) (fun _ => blank) 0 data opened := by
    intro j
    simpa only [data,castWord] using payload j
  obtain ⟨z,F,t,exec,user,paid,out,frame⟩ := run c child atom price aligned groups handoff pos tl tr br vacant data v opened
    castPayload atHeaders hc hs al ar
  have lengths : (slots.map (fun j => (opened.L j).length+(opened.R j).length+2)) =
      slots.map (fun j => (S.L j).length+(S.R j).length+2) := by
    apply List.map_congr_left
    intro j mem
    have ne : j ≠ bank 1 := fun e => widthOff (e ▸ mem)
    simp [opened,ne]
  refine ⟨z,F,t,exec,?_,user,?_,?_⟩
  · change CleanupBound opened F t charge
    change CleanupBound opened F t (rate*cells c+4*scratchCount+1+(price+1000000034*volume prime wide+49)+4*slots.length+1+
      (prime+8)*(slots.map (fun j => (opened.L j).length+(opened.R j).length+2)).sum) at paid
    simpa only [charge,size,lengths] using paid
  · intro j
    simpa only [castWord] using out j
  · exact fun j off _ => frame j off

/-- At a packed parent entry the full bank holds the loaded private seed, one
word per data row, and the two physical controls. -/
theorem LoadsPackedSeed.parentFrameCost {Config : Type} {h T H : ℕ}
    {headers : Config → Fin h → List (Fin (prime+4))} {cells : Config → ℕ} {seed : Config → Stacks T prime}
    (load : LoadsPackedSeed headers cells seed) (place : Fin T ↪ Fin H) (fan : Fin (142081+2) ↪ Fin T) :
    ∃ rate : ℕ, ∀ c V (x : Fin 142081 → Fin V → ZMod 2) (S : Stacks H prime),
      ParentStageWords (fun i => place (fan (i.castAdd 2))) (fan.trans place) V x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L (place j) = (seed c).L j ∧ S.R (place j) = (seed c).R j) →
      let cost := fun j => (S.L j).length+(S.R j).length+2
      ((frameSlots place).map cost).sum ≤ rate*cells c+2*T+142081*(V+2)+
        ∑ i : Fin 2, cost (place (fan (i.natAdd 142081))) := by
  obtain ⟨rate,stock⟩ := load.frameCost
  refine ⟨rate,?_⟩
  intro c V x S words privateAt cost
  let seedCost := fun j => ((seed c).L j).length+((seed c).R j).length+2
  have paid := stock c (List.finRange T) (List.nodup_finRange _)
  change ((List.finRange T).map seedCost).sum ≤ _ at paid
  simp [List.finRange,List.sum_ofFn] at paid
  have split := sum_replace_embedding fan fan.injective (cost ∘ place) seedCost
    (fun i => cost (place (fan i))) (fun _ => rfl) (fun j off => by
      obtain ⟨l,r⟩ := privateAt j (fun i eq => off ⟨i,eq⟩)
      simp only [Function.comp_apply,cost,seedCost,l,r])
  have owners : (∑ i, cost (place (fan i))) = 142081*(V+2)+
      ∑ i : Fin 2, cost (place (fan (i.natAdd 142081))) := by
    rw [Fin.sum_univ_add]
    have row (i : Fin 142081) : cost (place (fan (i.castAdd 2))) = V+2 := by
      simp [cost,words.left i,words.right i]
    simp only [row,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  rw [owners] at split
  have total : ((frameSlots place).map cost).sum = ∑ j, (cost ∘ place) j := by
    simp [frameSlots,List.map_reverse,List.finRange,List.sum_ofFn,Function.comp_def]
  rw [total]
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
