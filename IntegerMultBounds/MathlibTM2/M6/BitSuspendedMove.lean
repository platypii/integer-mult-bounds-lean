module

public import IntegerMultBounds.MathlibTM2.M6.BitSuspendedStack
public import IntegerMultBounds.MathlibTM2.M6.BitPackedMoveCaller
public import IntegerMultBounds.MathlibTM2.Host.StateTransport

/-! A packed MOVE may leave its borrowed bank dirty. Clear it before unwinding
the frame and charge the erasure to the MOVE's existing cleanup budget. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

noncomputable def clearSlots {T : ℕ} (slots : List (Fin T)) (S : Stacks T prime) :=
  replaceBank slots S {S with L := fun _ => [], R := fun _ => []}

/-- Reinstating the same caller words on entry and exit preserves the change
in cleanup charge, for every observed set. -/
private theorem restoredCharge {T : ℕ} (slots js : List (Fin T)) (S F : Stacks T prime) :
    tapeCharge cleanupWeight js (replaceBank slots F S) + tapeCharge cleanupWeight js (clearSlots slots S) =
      tapeCharge cleanupWeight js (clearSlots slots F) + tapeCharge cleanupWeight js S := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [tapeCharge,List.map_cons,List.sum_cons] at ih ⊢
    by_cases h : j ∈ slots <;> simp only [clearSlots,replaceBank,h,ite_true,ite_false] at * <;> omega

/-- Execute a packed MOVE on a borrowed bank with arbitrary incoming words.
The transposed payload survives erasure and every borrowed tape is restored. -/
theorem suspendedMove_run {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (move entry : Pr P T Q prime U) (slots : List (Fin T)) (distinct : slots.Nodup)
    (installed : SuspendedBank body (move.seq (clearWorkTapes slots)) slots entry)
    (payload : Fin T) (external : payload ∉ slots) (v : HS T Q prime U) (S : Stacks T prime)
    {N : ℕ} (y : Fin N → ZMod 2) (price : ℕ)
    (keep : Fin T → Prop) (worker : ∀ u : HS T Q prime U, ∃ a F m, Exec body move (mk u (clearSlots slots S)) m (mk a F) ∧
      a.user = u.user ∧ CleanupBound (clearSlots slots S) F m price ∧
      RecordPayload payload (fun _ => blank) 0 y F ∧ ∀ j, keep j → j ∉ slots → F.L j = S.L j ∧ F.R j = S.R j) :
    ∃ z F n, Exec body entry (mk v S) n (mk z F) ∧ z.user = v.user ∧
      CleanupBound S F n (price+4*slots.length+1+
        (prime+8)*(slots.map (fun j => (S.L j).length+(S.R j).length+2)).sum) ∧
      RecordPayload payload (fun _ => blank) 0 y F ∧
      ∀ j, j ∈ slots ∨ keep j → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨a,D,m,run,user,cost,out,frame⟩ := worker (if slots.isEmpty then v else {v with sym := none})
  obtain ⟨z,same,clear⟩ := clearWorkTapes_exec body slots distinct a D
  let G := clearSlots slots D
  have clean (j) (h : j ∈ slots) : G.L j = [] ∧ G.R j = [] := by simp [G,clearSlots,replaceBank,h]
  have bill := cleanupBound_clearBank slots distinct cost (Nat.le_refl (tapeCharge cleanupWeight slots D+1))
    (F := G) clean (fun j => by by_cases h : j ∈ slots <;> simp [G,clearSlots,replaceBank,h])
  have initial : tapeCharge cleanupWeight slots (clearSlots slots S) = 4*slots.length := by
    unfold tapeCharge
    rw [List.map_congr_left (g := fun _ => 4) (fun j h => by simp [cleanupWeight,clearSlots,replaceBank,h])]
    simp [List.map_const',Nat.mul_comm]
  rw [initial] at bill
  obtain ⟨n,paid,exec⟩ := installed.replay S G distinct clean _ v z (run.seq clear)
  refine ⟨z,replaceBank slots G S,n,exec,same.trans (by split at user <;> exact user),?_,?_,?_⟩
  · intro js nd
    have bound := bill js nd
    have eq := restoredCharge slots js S D
    change n+tapeCharge cleanupWeight js _ ≤ tapeCharge cleanupWeight js S+_
    change _+tapeCharge cleanupWeight js G ≤ tapeCharge cleanupWeight js (clearSlots slots S)+_ at bound
    have restored : replaceBank slots G S = replaceBank slots D S := by
      unfold G clearSlots replaceBank
      congr 1 <;> funext j <;> by_cases h : j ∈ slots <;> simp [h]
    rw [restored]
    change n ≤ m+(tapeCharge cleanupWeight slots D+1)+_ at paid
    dsimp only [G] at bound
    omega
  · intro j
    simpa [G,clearSlots,replaceBank,external] using out j
  · intro j h
    by_cases mem : j ∈ slots
    · simp [replaceBank,mem]
    · simpa [replaceBank,G,clearSlots,mem] using frame j (h.resolve_left mem) mem

/-- Install the save and restore procedures alongside the original worker labels. -/
theorem installedSuspendedMove {R U : Type} {H Q k : ℕ} (ports : Fin k ↪ Fin H)
    (host : R → Pr R H Q prime U) (move : Pr R H Q prime U) :
    let slots := frameSlots ports
    let Label := (Fin k × Bool) ⊕ R
    ∃ (table : Label → Pr Label H Q prime U) (wrapper : Pr Label H Q prime U),
      (∀ f, table (.inr f) = stateMapProg id id Sum.inr (host f)) ∧
      ∀ (payload : Fin H), payload ∉ slots → ∀ (v : HS H Q prime U) (S : Stacks H prime)
        {N : ℕ} (y : Fin N → ZMod 2) (price : ℕ) (keep : Fin H → Prop),
        (∀ u : HS H Q prime U, ∃ a F m, Exec host move (mk u (clearSlots slots S)) m (mk a F) ∧
          a.user = u.user ∧ CleanupBound (clearSlots slots S) F m price ∧ RecordPayload payload (fun _ => blank) 0 y F ∧
          ∀ j, keep j → j ∉ slots → F.L j = S.L j ∧ F.R j = S.R j) →
        ∃ z F n, Exec table wrapper (mk v S) n (mk z F) ∧ z.user = v.user ∧
          CleanupBound S F n (price+4*slots.length+1+
            (prime+8)*(slots.map (fun j => (S.L j).length+(S.R j).length+2)).sum) ∧
          RecordPayload payload (fun _ => blank) 0 y F ∧
          ∀ j, j ∈ slots ∨ keep j → F.L j = S.L j ∧ F.R j = S.R j := by
  intro slots Label
  let code : Pr Label H Q prime U := stateMapProg id id Sum.inr move
  let call := code.seq (clearWorkTapes slots)
  let table := bankTable ports call (fun f => stateMapProg id id Sum.inr (host f))
  let wrapper := bankEntry call k le_rfl
  have chain : SuspendedBank table call slots wrapper := by
    simpa [slots,frameSlots,table,List.map_reverse,wrapper] using bankTable_installed ports call
      (fun f => stateMapProg id id Sum.inr (host f)) _ le_rfl
  have nd : slots.Nodup := by simpa [slots,frameSlots] using (List.nodup_finRange _).map ports.injective
  refine ⟨table,wrapper,fun _ => rfl,?_⟩
  intro payload off v S N y price keep worker
  apply suspendedMove_run table code wrapper slots nd chain payload off v S y price keep
  intro u
  obtain ⟨a,F,m,run,spec⟩ := worker u
  exact ⟨a,F,m,stateMap_exec id id (fun _ => rfl) Sum.inr (body' := table) (fun _ => rfl) run,spec⟩

/-- The three return controls and the complete input fan occupy the borrowed bank. -/
def moveFramePorts {T H r k : ℕ} (src : Fin k ↪ Fin T) (ret : Fin r ↪ Fin T)
    (apart : ∀ i j, ret i ≠ src j) (place : Fin T ↪ Fin H) : Fin (r+k) ↪ Fin H :=
  (Fin.Embedding.append (Set.disjoint_range_iff.mpr apart)).trans place

private theorem moveFrameRanges {T H r k : ℕ} (src : Fin k ↪ Fin T) (ret : Fin r ↪ Fin T)
    (apart : ∀ i j, ret i ≠ src j) (place : Fin T ↪ Fin H) :
    let slots := frameSlots (moveFramePorts src ret apart place)
    (∀ i, place (src i) ∈ slots) ∧ (∀ i, place (ret i) ∈ slots) ∧
      ∀ j, (∀ i, place i ≠ j) → j ∉ slots := by
  intro slots
  constructor
  · intro i
    exact (mem_frameSlots _ _).2 ⟨i.natAdd r,by simp [moveFramePorts,Fin.Embedding.append]⟩
  constructor
  · intro i
    exact (mem_frameSlots _ _).2 ⟨i.castAdd k,by simp [moveFramePorts,Fin.Embedding.append]⟩
  · intro j away h
    obtain ⟨i,eq⟩ := (mem_frameSlots _ _).1 h
    exact away _ eq

private theorem frameSlots_sum {T k : ℕ} (ports : Fin k ↪ Fin T) (f : Fin T → ℕ) :
    ((frameSlots ports).map f).sum = ∑ j, f (ports j) := by
  simp [frameSlots,List.map_reverse,Function.comp_def,List.finRange,List.sum_ofFn]

private theorem moveFrame_sum {T H r k : ℕ} (src : Fin k ↪ Fin T) (ret : Fin r ↪ Fin T)
    (apart : ∀ i j, ret i ≠ src j) (place : Fin T ↪ Fin H) (f : Fin H → ℕ) :
    ((frameSlots (moveFramePorts src ret apart place)).map f).sum =
      (∑ i, f (place (ret i))) + ∑ i, f (place (src i)) := by
  rw [frameSlots_sum,Fin.sum_univ_add]
  simp [moveFramePorts,Fin.Embedding.append]

/-- Count the words on the concrete MOVE bank at a packed parent boundary.
Only five control tapes remain outside the data-row count. -/
theorem parentMoveFrameCost {T H V : ℕ} (src : Fin (142081+2) ↪ Fin T) (ret : Fin 3 ↪ Fin T)
    (apart : ∀ i j, ret i ≠ src j) (place : Fin T ↪ Fin H) (S : Stacks H prime)
    (x : Fin 142081 → Fin V → ZMod 2)
    (words : ParentStageWords (fun i => place (src (i.castAdd 2))) (src.trans place) V x S) :
    let f := fun j => (S.L j).length+(S.R j).length+2
    ((frameSlots (moveFramePorts src ret apart place)).map f).sum =
      (∑ i, f (place (ret i))) + (142081*(V+2) + ∑ i : Fin 2, f (place (src (i.natAdd 142081)))) := by
  intro f
  rw [moveFrame_sum,Fin.sum_univ_add (a := 142081) (b := 2)]
  have cell (i : Fin 142081) : f (place (src (i.castAdd 2))) = V+2 := by
    simp [f,words.left i,words.right i]
  simp only [cell,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

/-- Execution and cost of the packed split, recursive call, and merge with restored caller tapes. -/
def SuspendedRows {P R U : Type} {T H Q k : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (src dst : Fin (142081+2) ↪ Fin T) (ret : Fin 3 ↪ Fin T) (tmp buf : Fin T)
    (place : Fin T ↪ Fin H) (host : R → Pr R H Q prime U) (payload count saved aux : Fin H)
    (ports : Fin k ↪ Fin H) : Prop :=
    let slots := frameSlots ports
    let Label := (Fin k × Bool) ⊕ R
    ∃ (table : Label → Pr Label H Q prime U) (wrapper : Pr Label H Q prime U),
      (∀ f, table (.inr f) = stateMapProg id id Sum.inr (host f)) ∧
      ∀ (child : Descriptor) (atom price : ℕ) seed, child.width = 64*atom → 142080 ∣ child.rows →
      let lane := packedDescriptor (64*atom) (CopyChildLayout.spectators child / 142080)
      let m := volume prime lane
      let wide := packedDescriptor child.width (CopyChildLayout.spectators child)
      PackedPieceHandoffWithCharge cleanupWeight m (packedChildOutput atom m) body (body entry) src dst seed price →
      0 < m → ∀ (x : Fin (volume prime wide) → ZMod 2) u (S : Stacks H prime),
      let D := clearSlots slots S
      let B := embStk place D
      RecordPayload payload (fun _ => blank) 0 x S →
      D.R count = [] → D.R saved = [] → D.L aux = [] → D.R aux = [] →
      B.L tmp = [] → B.R tmp = [] → B.R buf = [] →
      (∀ i, seed.L (ret i) = [] ∧ seed.R (ret i) = []) →
      (∀ j, (∀ i, src i ≠ j) → (∀ i, ret i ≠ j) → B.L j = seed.L j ∧ B.R j = seed.R j) →
      ∃ z F n, Exec table wrapper (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (price+1000000034*volume prime wide+49+4*slots.length+1+
          (prime+8)*(slots.map (fun j => (S.L j).length+(S.R j).length+2)).sum) ∧
        RecordPayload payload (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (v := wide) (one_dvd wide.rows) x) F ∧
        ∀ j, j ∈ slots ∨ (j ≠ payload ∧ ∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j

private theorem packedRowsWithFrame {P R U : Type} {T H Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
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
    {k : ℕ} (ports : Fin k ↪ Fin H) (sources : ∀ i, place (src i) ∈ frameSlots ports)
    (returns : ∀ i, place (ret i) ∈ frameSlots ports) (off : payload ∉ frameSlots ports) :
    SuspendedRows body entry src dst ret tmp buf place host payload count saved aux ports := by
  obtain ⟨move,execute⟩ := packedRowsOnChildBank body entry src dst ret srcOff dstOff tmp buf
    srcTmp srcBuf retTmp retBuf distinct place label host installed payload count saved aux outside separate capacity
  let slots := frameSlots ports
  obtain ⟨table,wrapper,labels,wrap⟩ := installedSuspendedMove ports host move
  refine ⟨table,wrapper,labels,?_⟩
  intro child atom price seed width rows lane m wide
    handoff pos x u S D B input countAt savedAt al ar tl tr br vacant rest
  refine wrap payload off u S
    (Shared50RecursiveNodeRows.transpose (v := wide) (one_dvd wide.rows) x) (price+1000000034*volume prime wide+49)
    (fun j => j ≠ payload ∧ ∀ i, place i ≠ j) ?_
  intro v
  obtain ⟨a,F,n,run,user,paid,out,frame⟩ := execute child atom price seed width rows handoff pos x v D
    (fun j => by simpa [D,clearSlots,replaceBank,off] using input j) countAt savedAt al ar
    (fun i => by simp [embStk,D,clearSlots,replaceBank,sources]) (fun i => by simp [embStk,D,clearSlots,replaceBank,returns])
    tl tr br vacant rest
  refine ⟨a,F,n,run,user,paid,out,?_⟩
  intro j h mem
  change j ∉ frameSlots ports at mem
  simpa [D,clearSlots,replaceBank,mem] using frame j h.1 h.2

/-- The physical split and merge can borrow occupied source and return tapes
from a suspended parent. All preparation hypotheses refer to the remaining seed. -/
theorem suspendedRowsOnChildBank {P R U : Type} {T H Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (src dst : Fin (142081+2) ↪ Fin T) (ret : Fin 3 ↪ Fin T)
    (srcOff : ∀ i j, ret i ≠ src j) (dstOff : ∀ i j, ret i ≠ childReturnFan dst j)
    (tmp buf : Fin T) (srcTmp : ∀ i, src i ≠ tmp) (srcBuf : ∀ i, src i ≠ buf)
    (retTmp : ∀ i, ret i ≠ tmp) (retBuf : ∀ i, ret i ≠ buf) (distinct : tmp ≠ buf)
    (place : Fin T ↪ Fin H) (label : P → R) (host : R → Pr R H Q prime U)
    (installed : ∀ f, host (label f) = embProg place label (body f))
    (payload count saved aux : Fin H)
    (outside : ∀ i, place i ≠ payload ∧ place i ≠ count ∧ place i ≠ saved ∧ place i ≠ aux)
    (separate : [count,place (ret 0),payload,saved,aux].Nodup)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    SuspendedRows body entry src dst ret tmp buf place host payload count saved aux (moveFramePorts src ret srcOff place) := by
  obtain ⟨sources,returns,excludes⟩ := moveFrameRanges src ret srcOff place
  exact packedRowsWithFrame body entry src dst ret srcOff dstOff tmp buf srcTmp srcBuf retTmp retBuf
    distinct place label host installed payload count saved aux outside separate capacity _ sources returns
    (excludes _ (fun i => (outside i).1))

/-- The physical row splitter leaves a bank whose entire suspension bill is
linear in the input volume, including the controls' actual stack lengths. -/
theorem splitInputFrameCost {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin (intervalSplitTapes+1) ↪ Fin T)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ program : Pr P T Q prime U, ∀ m, 0 < m → ∀ (x : Fin (m*142080) → ZMod 2) u (S : Stacks T prime),
      S.R (bank (Fin.succ 0)) = List.ofFn (fun i => SparseRoleCircuit.encode (x i)) →
      (∀ j, S.L (bank j) = []) → (∀ j, j ≠ Fin.succ 0 → S.R (bank j) = []) →
      ∃ z F t, Exec body program (mk u S) t (mk z F) ∧ z.user = u.user ∧
        t ≤ (149*(intervalSplitTapes+5)+5)*(m*142080)+24 ∧
        HelperFan ((withHelperPort (intervalOwners 142080)).trans bank)
          (Fin.lastCases (fun _ => 0) (fun row i => x (finProdFinEquiv (i,row)))) F ∧
        ((frameSlots bank).map (fun j => (F.L j).length+(F.R j).length+2)).sum ≤
          (intervalSplitTapes+1)*(301*(m*142080)+4) ∧
        ∀ j, (∀ k, bank k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨program,run⟩ := placedChildInputSpace_exec body bank capacity
  refine ⟨program,?_⟩
  intro m pos x u S source left empty
  obtain ⟨z,F,t,exec,user,paid,_,rows,space,frame⟩ := run m pos x u S source left empty
  refine ⟨z,F,t,exec,user,paid,rows,?_,frame⟩
  rw [frameSlots_sum]
  calc
    _ ≤ ∑ _j : Fin (intervalSplitTapes+1), (301*(m*142080)+4) := by
      apply Finset.sum_le_sum
      intro j _
      have h := space j
      omega
    _ = _ := by simp

/-- The charged initializer bounds the words spilled from any subset of the
parent seed. Its other tapes contribute nothing to the estimate. -/
theorem LoadsPackedSeed.frameCost {Config : Type} {k T : ℕ}
    {words : Config → Fin k → List (Fin (prime+4))} {volume : Config → ℕ}
    {seed : Config → Stacks T prime} (load : LoadsPackedSeed words volume seed) :
    ∃ rate : ℕ, ∀ c (slots : List (Fin T)), slots.Nodup →
      (slots.map (fun j => ((seed c).L j).length+((seed c).R j).length+2)).sum ≤
        rate*volume c+2*slots.length := by
  obtain ⟨rate,compile⟩ := load
  refine ⟨rate,?_⟩
  intro c slots nd
  let bank := Fin.castAddEmb k (n := T)
  let source := Fin.natAddEmb T (m := k)
  let S : Stacks (T+k) prime := ⟨[],[],fun _ => [],Fin.append (fun _ => []) (words c)⟩
  let u : HS (T+k) 1 prime Unit := ⟨false,none,0,fun _ => blank,none,()⟩
  obtain ⟨_,execute⟩ := compile (P := Empty) (U := Unit) (Q := 1) Empty.elim bank source
    (fun i j eq => by have := congrArg Fin.val eq; change i.val = T+j.val at this; omega)
  obtain ⟨_,F,n,_,_,paid,loaded,_⟩ := execute c u S (fun i => by simp [S,source])
    (fun i => by simp [S,bank])
  have bill := paid (slots.map bank) (nd.map bank.injective)
  have initial : tapeCharge cleanupWeight (slots.map bank) S = 4*slots.length := by
    simp [tapeCharge,cleanupWeight,S,bank,List.map_const',Function.comp_def,Nat.mul_comm]
  have final : 2*(slots.map (fun j => ((seed c).L j).length+((seed c).R j).length+2)).sum ≤
      tapeCharge cleanupWeight (slots.map bank) F := by
    clear bill nd initial
    induction slots with
    | nil => simp [tapeCharge]
    | cons j js ih =>
      simp only [List.map_cons,List.sum_cons,tapeCharge,cleanupWeight] at ih ⊢
      rw [(loaded j).1,(loaded j).2]
      omega
  change n+tapeCharge cleanupWeight (slots.map bank) F ≤ tapeCharge cleanupWeight (slots.map bank) S+_ at bill
  rw [initial] at bill
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
