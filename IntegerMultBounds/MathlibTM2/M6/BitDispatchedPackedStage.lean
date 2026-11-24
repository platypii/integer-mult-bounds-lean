module

public import IntegerMultBounds.MathlibTM2.M6.BitInitializedPackedStage
public import IntegerMultBounds.MathlibTM2.M6.BitStageCallerLayout

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

def callerSeed {k H : ℕ} (fan : Fin (k+1) ↪ Fin H) (cutoff : List (Fin (prime+4)))
    (external : Fin 37 → List (Fin (prime+4))) : Stacks (H+37) prime :=
  ⟨[],[],fun _ => [],Fin.append (Function.update (fun _ => []) (fan (Fin.last k)) cutoff) external⟩

private theorem callerSeed_ready {k H : ℕ} (fan : Fin (k+1) ↪ Fin H) (cutoff : List (Fin (prime+4)))
    (external : Fin 37 → List (Fin (prime+4))) (S : Stacks (H+37) prime) :
    let place := Fin.castAddEmb 37 (n := H)
    let data := (Fin.castAddEmb 1 (n := k)).trans fan
    PrivateTapes (data.trans place) (callerSeed fan cutoff external) S →
    (∀ i : Fin 37, S.R (i.natAdd H) = external i) ∧
    (∀ j, (∀ i, fan i ≠ j) → S.L (place j) = [] ∧ S.R (place j) = []) ∧
    S.R (place (fan (Fin.last k))) = cutoff := by
  intro place data fresh
  refine ⟨?_,?_,?_⟩
  · intro i
    have h := fresh (i.natAdd H) (fun j eq => by
      have val := congrArg Fin.val eq
      change (data j).val = H+i.val at val
      have := (data j).isLt
      omega)
    simpa only [callerSeed,Fin.append_right] using h.2
  · intro j off
    have h := fresh (place j) (fun i => place.injective.ne (off (i.castAdd 1)))
    simpa only [callerSeed,place,Fin.coe_castAddEmb,Fin.append_left,Function.update_of_ne (off _).symm] using h
  · have h := fresh (place (fan (Fin.last k))) (fun i eq =>
      ne_of_lt i.castSucc_lt_last (fan.injective (place.injective eq)))
    simpa only [callerSeed,place,Fin.coe_castAddEmb,Fin.append_left,Function.update_self] using h.2

private theorem stageHeaderLoadCost (node : Descriptor) (positive : node.Positive) :
    seedLoadBill (fun i => (Routines.hdr node i).map (bitSymbol (a := prime))) ≤
      48*volume prime node+85 := by
  have bits (i : Fin 6) : (Routines.hdr node i).length ≤ volume prime node+1 := by
    have width := GrowingCounterData.canonical_width _ ((Routines.hdr_headers node).2 i)
    rw [(Routines.hdr_headers node).1 i] at width
    exact width.trans (Nat.add_le_add_right ((Nat.log2_le_self _).trans
      (RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le node positive i)) 1)
  have total := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 6)))
    (f := fun i => 8*(Routines.hdr node i).length+6) (g := fun _ => 8*(volume prime node+1)+6)
    (fun i _ => Nat.add_le_add_right (Nat.mul_le_mul_left 8 (bits i)) 6)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at total
  simp only [seedLoadBill,List.length_map]
  omega

/-- With the cutoff on the last fan tape, copying the six descriptor words
establishes the private-tape invariant of the dispatched stage. -/
theorem loadStageCallerSeed {k H T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (fan : Fin (k+1) ↪ Fin H) (bank : Fin (H+37) ↪ Fin T)
    (source : Fin 6 → Fin T) (tmp saved : Fin T) :
    let ext := (Fin.natAddEmb H (m := 37)).trans bank
    let core := (Fin.castAddEmb 37 (n := H)).trans bank
    let data := ((Fin.castAddEmb 1 (n := k)).trans fan).trans (Fin.castAddEmb 37)
    (∀ i j, ext (callerHeaderPorts i) ≠ source j) →
    (∀ i, [source i,ext (callerHeaderPorts i),tmp,saved].Nodup) →
    ∃ code : Pr P T Q prime U, ∀ (node : Descriptor) u (S : Stacks T prime),
      let words := fun i => (Routines.hdr node i).map (bitSymbol (a := prime))
      let cutoff := S.R (core (fan (Fin.last k)))
      node.Positive → (∀ i, S.R (source i) = words i) →
      (∀ j, S.L (ext j) = [] ∧ S.R (ext j) = []) →
      (∀ j, (∀ i : Fin k, fan (i.castAdd 1) ≠ j) → S.L (core j) = []) →
      (∀ j, (∀ i, fan i ≠ j) → S.R (core j) = []) →
      S.R tmp = [] → S.R saved = [] →
      ∃ v R n, Exec body code (mk u S) n (mk v {S with R := R}) ∧ v.user = u.user ∧
        CleanupBound S {S with R := R} n (48*volume prime node+85) ∧
        PrivateTapes data (callerSeed fan cutoff (callerHeaderBank words)) (embStk bank {S with R := R}) ∧
        ∀ j, (∀ i, ext (callerHeaderPorts i) ≠ j) → R j = S.R j := by
  intro ext core data apart regs
  obtain ⟨code,load⟩ := loadCallerHeaderBank body ext source tmp saved apart regs
  refine ⟨code,?_⟩
  intro node u S words cutoff positive headers vacant left right ht hs
  obtain ⟨v,R,n,run,user,bill,loaded,off⟩ := load u S (fun j => (vacant j).2) ht hs
  rw [show (fun i => S.R (source i)) = words from funext headers] at bill loaded
  refine ⟨v,R,n,run,user,fun js nd => (bill js nd).trans (Nat.add_le_add_left (stageHeaderLoadCost node positive) _),?_,off⟩
  intro j
  induction j using Fin.addCases with
  | right j =>
    intro _
    exact ⟨(vacant j).1,(loaded j).trans (Fin.append_right ..).symm⟩
  | left j =>
    intro outside
    have away (i : Fin k) : fan (i.castAdd 1) ≠ j := fun eq => outside i (congrArg (Fin.castAdd 37) eq)
    have keep : R (core j) = S.R (core j) := off _ (fun i eq => by
      have val := congrArg Fin.val (bank.injective eq)
      change H+(callerHeaderPorts i).val = j.val at val
      have := j.isLt
      omega)
    refine ⟨left j away,?_⟩
    change R (core j) = Fin.append _ (callerHeaderBank words) (j.castAdd 37)
    rw [Fin.append_left,keep]
    by_cases hit : j = fan (Fin.last k)
    · subst j
      rw [Function.update_self]
    · rw [Function.update_of_ne hit]
      apply right
      intro i
      induction i using Fin.lastCases with
      | last => exact Ne.symm hit
      | cast i => exact away i

/-- Initialize a basis pass of a correction chart from its atom width and
spectator count. The first two slots double as temporary copy registers. -/
theorem basisPortLoader {Config : Type} {d : ℕ} (ops : List (FlatCoordinateSchedule.Op d))
    (dimension : 0 < d) (w W : Config → ℕ) (positive : ∀ c, 0 < W c) :
    let words := fun c => (![binSyms (A := prime) (w c).size (w c),binSyms (W c).size (W c)] :
      Fin 2 → List (Fin (prime+4)))
    LoadsPackedSeed words (fun c => (prime^(w c))^d*W c) (fun c => basisHeaderStacks ops (w c) (W c)) := by
  intro words
  refine ⟨40,?_⟩
  intro P U T Q body bank source apart
  let ports := basisSeedPorts ops
  let tmp : Fin (FlatCoordinateCleanSchedule.tapeCount ops) := ⟨0,by
    have := (ports 0).isLt
    change 2 < _ at this
    omega⟩
  let saved : Fin (FlatCoordinateCleanSchedule.tapeCount ops) := ⟨1,by
    have := (ports 0).isLt
    change 2 < _ at this
    omega⟩
  have a (i) : ports i ≠ tmp := by
    intro eq
    have h := congrArg Fin.val eq
    change 2+i.val = 0 at h
    omega
  have b (i) : ports i ≠ saved := by
    intro eq
    have h := congrArg Fin.val eq
    change 2+i.val = 1 at h
    omega
  obtain ⟨code,run⟩ := loadBasisWorkerSeed body ops bank source (bank tmp) (bank saved)
    (fun i j => apart _ _) (fun i => by
      simp [List.nodup_cons,(apart _ _).symm,bank.injective.eq_iff,
        (show tmp ≠ saved by intro h; exact Nat.zero_ne_one (congrArg Fin.val h))]
      exact ⟨a i,b i⟩)
  refine ⟨code,?_⟩
  intro c u S header vacant
  obtain ⟨z,F,t,exec,user,bill,set,off⟩ := run (w c) (W c) u S (fun _ => True) (fun _ => trivial)
    (header 0) (header 1) (fun j _ => vacant j) (vacant tmp).2 (vacant saved).2
  refine ⟨z,F,t,exec,user,?_,fun j => set j trivial,fun j away => off j (fun i => away _)⟩
  have p := pow_pos Shared50ModularControl.prime_prime.pos (w c)
  have h := Nat.le_self_pow dimension.ne' (prime^(w c))
  have width := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt (n := w c)).le
  have left := Nat.le_mul_of_pos_right ((prime^(w c))^d) (positive c)
  have right := Nat.le_mul_of_pos_left (W c) (pow_pos p d)
  have bits (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  intro js nd
  have cost : 8*((w c).size+(W c).size)+24 ≤ 40*((prime^(w c))^d*W c) := by
    have := bits (w c)
    have := bits (W c)
    have := positive c
    omega
  exact (bill js nd).trans (Nat.add_le_add_left cost _)

/-- A fixed chart schedule can run each port initializer on its own bank.
The resulting program has one linear rate for the complete list. -/
theorem compiledPortLoader {Config α : Type} {k h N : ℕ} (slot : α → Fin (k+1))
    (port : α → SharedBankStage.Stage _ 1 prime (@portOwner N))
    (words : Config → Fin h → List (Fin (prime+4))) (V : Config → ℕ) (positive : ∀ c, 0 < V c)
    (seed : Config → ∀ j, Stacks (port j).tapes prime) (jobs : List α)
    (load : ∀ j ∈ jobs, LoadsPackedSeed words V (fun c => seed c j)) :
    LoadsPackedSeed words V (fun c => compiledPortStacks slot port (seed c) jobs) := by
  have blank (t) : LoadsPackedSeed words V (fun _ => blankPortStacks t) := by
    refine ⟨1,?_⟩
    intro P U T Q body bank source apart
    refine ⟨Prog.act .done,?_⟩
    intro c u S headers vacant
    refine ⟨u,S,1,Exec.act .done _,rfl,?_,vacant,fun _ _ => ⟨rfl,rfl⟩⟩
    intro js unique
    have := positive c
    omega
  induction jobs with
  | nil => exact blank _
  | cons j js ih =>
    exact ((blank _).join ((load j List.mem_cons_self).join (blank k))).join
      (ih (fun i hi => load i (List.mem_cons_of_mem _ hi)))

/-- The dispatched sweep's inner caller needs just the cutoff word and the six
descriptor words. All other registers, including the copy scratch, start blank. -/
theorem stageCallerLoader {k H : ℕ} (fan : Fin (k+1) ↪ Fin H) :
    let words := fun (c : CutoffNodeInput) => Fin.cons (binSyms (A := prime) c.root.width.size c.cutoff)
      (fun i => (Routines.hdr c.node i).map bitSymbol)
    LoadsPackedSeed words CutoffNodeInput.cells (fun c => callerSeed fan (words c 0)
      (callerHeaderBank (fun i => words c i.succ))) := by
  classical
  intro words
  let ext := Fin.natAddEmb H (m := 37)
  let last := (fan (Fin.last k)).castAdd 37
  have apart (i : Fin 37) : last ≠ ext i := by
    intro eq
    have h := congrArg Fin.val eq
    change (fan (Fin.last k)).val = H+i.val at h
    omega
  let slots : Fin 7 ↪ Fin (H+37) := ⟨Fin.cons last (ext ∘ callerHeaderPorts),by
    intro i j eq
    induction i using Fin.cases <;> induction j using Fin.cases <;> simp_all [ext.injective.eq_iff,callerHeaderPorts.injective.eq_iff]
    exact apart _ eq.symm⟩
  have away (j : Fin 37) (high : 6 ≤ j.val) (i : Fin 7) : slots i ≠ ext j := by
    induction i using Fin.cases with
    | zero => exact apart j
    | succ i =>
      apply ext.injective.ne
      intro eq
      have h := congrArg Fin.val eq
      change i.val = j.val at h
      omega
  have load := LoadsPackedSeed.headers words CutoffNodeInput.cells slots id (ext 6) (ext 7)
    (ext.injective.ne (by decide)) (away 6 (by decide)) (away 7 (by decide)) (142+133*142080)
    (fun c => by
      have setup := c.remainderSetup_le 1
      have pos : 0 < volume prime c.node := by
        rw [← c.cells_share]
        have h := c.idlePositive
        unfold CutoffNodeInput.cells
        have hp := Shared50ModularControl.prime_prime.pos
        positivity
      have bill := descriptorSeedBill c.node pos
      rw [← c.cells_share] at bill
      simp only [seedLoadBill,Fin.sum_univ_succ (n := 6),id_eq,words,Fin.cons_zero,Fin.cons_succ,length_binSyms]
      change (∑ i : Fin 6, (8*((Routines.hdr c.node i).map (bitSymbol (a := prime))).length+6))+1 ≤ _ at bill
      simp only [Nat.one_mul] at setup
      omega)
  have contents (c : CutoffNodeInput) : (callerSeed fan (words c 0)
      (callerHeaderBank (fun i => words c i.succ))).R = Function.extend slots (words c) (fun _ => []) := by
    funext j
    by_cases hit : ∃ i, slots i = j
    · obtain ⟨i,rfl⟩ := hit
      rw [slots.injective.extend_apply]
      induction i using Fin.cases with
      | zero =>
        change Fin.append _ _ ((fan (Fin.last k)).castAdd 37) = _
        rw [Fin.append_left,Function.update_self]
      | succ i =>
        change Fin.append _ _ ((callerHeaderPorts i).natAdd H) = _
        rw [Fin.append_right]
        exact dite_eq_left i.isLt
    · rw [Function.extend_apply' _ _ _ hit]
      induction j using Fin.addCases with
      | left j =>
        have ne : j ≠ fan (Fin.last k) := by rintro rfl; exact hit ⟨0,rfl⟩
        simp [callerSeed,Function.update_of_ne ne]
      | right j =>
        have outside : ¬ j.val < 6 := fun h => hit ⟨(⟨j.val,h⟩ : Fin 6).succ,rfl⟩
        simp [callerSeed,callerHeaderBank,outside]
  change LoadsPackedSeed words _ (fun c => ⟨[],[],fun _ => [],(callerSeed fan (words c 0) _).R⟩)
  simpa only [contents,id_eq] using load

/-- Install the stopped leaves and construct the restored sweep from the
cutoff word and the six parent descriptor headers. -/
theorem dispatchedRestoredWorker [M8.Machine.Net] (n : Fin 9) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let I := Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)
    let k := 142081+2
    ∃ (pre : StageRun → Fin l → MoveIndex) (post : StageRun → Fin r → MoveIndex),
    let child := fun i : I => invocationChildren n i.1 (pre i.1) (post i.1) i.2.1 i.2.2
    ∃ (ts : I → ℕ) (states : ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts i)),
    ∃ leafRate : ℝ, ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (large : ∀ i, P → Pr (WorkerLabel P) (ts i) Q prime U) (f : I → P),
    ∃ body : ∀ i, WorkerLabel P → Pr (WorkerLabel P) (ts i) Q prime U, (∀ i g, body i (.active g) = large i g) ∧
    ∃ (H : ℕ) (fan : Fin (k+1) ↪ Fin H)
      (table : I × WorkerLabel P → Pr (I × WorkerLabel P) (H+37) Q prime U)
      (worker : Pr (I × WorkerLabel P) (H+37) Q prime U) (rate : ℝ),
    let data := (Fin.castAddEmb 1).trans (fan.trans (Fin.castAddEmb 37))
    ∀ c : CutoffNodeInput,
    let w := c.w+1
    let V := (prime^w)^16*c.stageWidth
    let desc := fun i => scheduledChild prime c.node (child i)
    ∃ position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V,
    (∀ i, invocationCoordinates i.2.1 w c.stageWidth (position i)) ∧
    ∀ (budget : ℕ → ℕ) (childRate : ℝ), leafRate ≤ childRate →
    let time := stageBranchTime c.node c.cutoff childRate budget
    (∀ i, c.cutoff < (desc i).width →
      if i.2.1 = 1 then ScheduledChildExec c.node (desc i) c.w c.stageWidth (ports i) (binSyms c.root.width.size c.cutoff)
        (position i) (body i) (.active (f i)) (budget (child i).val) true
      else MoveOnBankExec c.node (desc i) c.w c.stageWidth (movePrefix.trans (ports i)) (binSyms c.root.width.size c.cutoff)
        (position i) (body i) (large i (f i)) (budget (child i).val) true) →
    let seed := callerSeed fan (binSyms c.root.width.size c.cutoff)
      (callerHeaderBank (fun i => (Routines.hdr c.node i).map (bitSymbol (a := prime))))
    ∀ x u S, HelperFan data x S → PrivateTapes data seed S →
      ∃ z F t y, Exec table worker (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (⌈rate*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)⌉₊+
          ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum) ∧
        HelperFan data y F ∧ RestoredBorrowedStage n w c.B c.stageFactor x y := by
  classical
  intro l r I k
  obtain ⟨pre,post,ts,states,ports,leafRate,build⟩ := callerRestoredStage n
  refine ⟨pre,post,ts,states,ports,leafRate,?_⟩
  intro P U Q cap large f
  obtain ⟨body,active,T,shared,owners,banks,align,inner,rate,compile⟩ :=
    build cap large f
  generalize hR : LeafCore.small = R at inner compile
  let H := 80+((T+273)+R)
  let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb R)).trans (Fin.natAddEmb 80)
  let archive := archiveSetupPlacement 80 T R
  let place := Fin.castAddEmb 37 (n := H)
  let fan := shared.trans owner
  let data := (Fin.castAddEmb 1 (n := k)).trans fan
  obtain ⟨source,r,power,tmp,saved,dimensions,division,input,quotientPort,divisionOff,divisionSafe,radixPort,unitPort,dimensionFrame,
    atomOff,atomPorts,privateDimensions,clockWidth,powerClock,clockOff,sourceSafe,placeSafe,tmpSafe,savedSafe,apart,regs⟩ :=
    stageCallerLayout owner archive (fun i => (archiveSetupPlacement_frame (R := 80) (T := T) (L := R) i).1)
  obtain ⟨worker,stage⟩ := compile place source r power tmp saved dimensions division
    quotientPort divisionOff divisionSafe radixPort unitPort dimensionFrame atomOff atomPorts privateDimensions
    clockWidth powerClock clockOff sourceSafe placeSafe tmpSafe savedSafe apart regs
  let table := fun f => embProg place id (inner f)
  refine ⟨body,active,H,fan,table,worker,rate,?_⟩
  intro innerFan c w V desc
  obtain ⟨position,_,_,coords,run⟩ := stage c
  refine ⟨position,coords,?_⟩
  intro budget childRate enough time recurse
  let word := binSyms (A := prime) c.root.width.size c.cutoff
  let words := fun i => (Routines.hdr c.node i).map (bitSymbol (a := prime))
  let external := callerHeaderBank words
  have externalReady := input words
  let kids := ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum
  let fee := rate*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)
  intro seed x u S live fresh
  obtain ⟨readExt,empty,cutoff⟩ := callerSeed_ready fan word external S fresh
  obtain ⟨headers,clocks,temps,ht,hs,divide,atom,t₄,t₅⟩ := externalReady S.R readExt
  have invoke := run budget childRate enough recurse
  have fanView (a : Fin 142081 → Fin V → ZMod 2) (G : Stacks (H+37) prime) :
      HelperFan innerFan a G ↔ HelperFan data a (embStk place G) := Iff.rfl
  have start := invoke x u S ((fanView x S).mp live) cutoff headers clocks temps
  have prepared := start (fun j => empty (archive j) (fun i => ((archiveSetupPlacement_frame (R := 80) (T := T) (L := R) j).1 (shared i)).symm))
    ht hs divide atom t₄ t₅
  obtain ⟨z,F,t,y,exec,bill,user,out,done⟩ := prepared
    (fun i l priv => empty (owner (banks i l)) (fun h eq => priv h ((banks i).injective
      ((align i h).trans (owner.injective eq)))))
    (fun j off _ => empty j (fun i => off (shared i)))
  refine ⟨z,F,t,y,exec,user,?_,(fanView y F).mpr out,done⟩
  intro js nd
  have paid := bill js nd
  rw [← c.stageCells] at paid
  change (t : ℝ)+_ ≤ _+fee+(kids : ℝ) at paid
  exact_mod_cast (show (t : ℝ)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
    (((⌈fee⌉₊+kids : ℕ) : ℝ)) by push_cast; linarith only [paid,Nat.le_ceil fee])

/-- Install stopped-leaf dispatch in each selected occurrence. Only the active
children require recursive execution contracts. -/
theorem dispatchedPackedStage [M8.Machine.Net] (n : Fin 9) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let I := Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)
    let k := 142081+2
    ∃ (pre : StageRun → Fin l → MoveIndex) (post : StageRun → Fin r → MoveIndex),
    let child := fun i : I => invocationChildren n i.1 (pre i.1) (post i.1) i.2.1 i.2.2
    ∃ (ts : I → ℕ) (states : ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts i)),
    ∃ leafRate : ℝ, ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (large : ∀ i, P → Pr (WorkerLabel P) (ts i) Q prime U) (f : I → P),
    ∃ body : ∀ i, WorkerLabel P → Pr (WorkerLabel P) (ts i) Q prime U, (∀ i g, body i (.active g) = large i g) ∧
    ∃ (T : ℕ) (src dst : Fin k ↪ Fin T) (host : I × WorkerLabel P → Pr (I × WorkerLabel P) T Q prime U)
      (code : Pr (I × WorkerLabel P) T Q prime U) (localCost : ℕ → ℕ → ℕ),
    (∃ D : ℝ, ∀ w V : ℕ, 0 < w → 0 < V → (localCost w V : ℝ) ≤
      D*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)) ∧ ∀ c : CutoffNodeInput,
    let w := c.w+1
    let V := (prime^w)^16*c.stageWidth
    let desc := fun i => scheduledChild prime c.node (child i)
    ∃ position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V,
    (∀ i, invocationCoordinates i.2.1 w c.stageWidth (position i)) ∧
    ∀ (budget : ℕ → ℕ) (rate : ℝ), leafRate ≤ rate →
    let time := stageBranchTime c.node c.cutoff rate budget
    (∀ i, c.cutoff < (desc i).width →
      if i.2.1 = 1 then ScheduledChildExec c.node (desc i) c.w c.stageWidth (ports i) (binSyms c.root.width.size c.cutoff)
        (position i) (body i) (.active (f i)) (budget (child i).val) true
      else MoveOnBankExec c.node (desc i) c.w c.stageWidth (movePrefix.trans (ports i)) (binSyms c.root.width.size c.cutoff)
        (position i) (body i) (large i (f i)) (budget (child i).val) true) →
    let W := c.B*prime^(64*(w*64))*c.stageFactor
    let size : (prime^w)^128*W = V :=
      (ordinaryCompact_width _ _).symm.trans (by simp [V,W,CutoffNodeInput.stageWidth,Nat.mul_assoc,w])
    ∃ seed, PackedPieceHandoffWithCharge cleanupWeight V (fun x y => ∀ j : Fin W,
      let address := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
      readRoles address y = (Piece.stage n).run (readRoles address x)) host code src dst seed
      (localCost w V+((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum) := by
  classical
  intro l r I k
  obtain ⟨pre,post,ts,states,ports,leafRate,build⟩ := dispatchedRestoredWorker n
  obtain ⟨C,base,tapes,chartStates,chart⟩ := borrowedFlatHandoffWithCharge
  refine ⟨pre,post,ts,max states chartStates,ports,leafRate,?_⟩
  intro P U Q cap large f
  obtain ⟨body,active,H,fan,table,worker,rate,stage⟩ := build ((Nat.le_max_left ..).trans cap) large f
  let data := (Fin.castAddEmb 1 (n := k)).trans (fan.trans (Fin.castAddEmb 37))
  obtain ⟨N,host,code,src,dst,pack⟩ := chart n data table worker ((Nat.le_max_right ..).trans cap)
  let overhead := fun w V => 13*((base*V+17760*(2*LeafCore.coreCost V w+14))*(tapes+5)+12)
  let localCost := fun (w V : ℕ) => overhead w V+⌈rate*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)⌉₊+
    ⌈C*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊+(142081*(10*V+10)+1)
  refine ⟨body,active,N,src,dst,host,code,localCost,packedStageCost_bound base tapes rate C,?_⟩
  intro c w V desc
  obtain ⟨position,coords,run⟩ := stage c
  refine ⟨position,coords,?_⟩
  intro budget childRate enough time recurse W size
  let word := binSyms (A := prime) c.root.width.size c.cutoff
  let words := fun i => (Routines.hdr c.node i).map (bitSymbol (a := prime))
  let external := callerHeaderBank words
  let initial := callerSeed fan word external
  let kids := ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum
  let fee := rate*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)
  have hb : 0 < c.B := Nat.pos_of_mul_pos_right (c.label ▸ c.stagePositive.2.2.1)
  have hk : 0 < c.stageFactor := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos c.stagePositive.1 c.stagePositive.2.1)
    c.stagePositive.2.2.2.1) c.stagePositive.2.2.2.2
  obtain ⟨seed,handoff⟩ := pack (w := w) (B := c.B) (K := c.stageFactor) (⌈fee⌉₊+kids) initial
    (Nat.succ_pos _) hb hk (by
      intro x u S live fresh
      obtain ⟨z,F,t,y,exec,user,bill,out,done⟩ := run budget childRate enough recurse x u S live fresh
      exact ⟨z,F,t,y,exec,bill,user,out,done⟩)
  refine ⟨seed,?_⟩
  have price : localCost w V+kids = overhead w V+(⌈fee⌉₊+kids)+
      ⌈C*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊+(142081*(10*V+10)+1) := by
    dsimp only [localCost,fee]
    omega
  rw [price]
  exact handoff

end IntegerMultBounds.MathlibTM2.M6.BitNode
