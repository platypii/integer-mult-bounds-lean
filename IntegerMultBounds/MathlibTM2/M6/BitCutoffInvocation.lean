module

public import IntegerMultBounds.MathlibTM2.M6.BitWorkerDispatch

/-! Install charged cutoff workers throughout one selected PR589 invocation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host
open Certificates.PR589 RecursiveInterchangeLayout M8.RevMachine
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

noncomputable def invocationWorkerRecord (j : Fin 3) (child : Descriptor) (L cutoff : ℕ) : List (Fin (prime+4)) :=
  let header := binSyms L cutoff
  let n := CopyChildLayout.spectators child
  if j = 1 then header else binSyms n.size n ++ separator :: header

-- Restore the lane-volume division formula from 0c1d2539.
/-- COPY needs the cutoff alone. MOVE prefixes it with the existing trailing exchange header. -/
noncomputable def invocationArchive (j : Fin 3) (field cutoff : List (Fin (prime+4))) :=
  if j = 1 then cutoff else field ++ separator :: cutoff

/-- Initialize the worker's archive from the live cutoff and the rank-selected exchange header. -/
theorem writeInvocationArchive {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin 35 ↪ Fin T) (cut : Fin T) (headers : Fin 127 → Fin 6 → Fin T)
    (offCut : ∀ j, bank j ≠ cut) (offHeader : ∀ i j, bank j ≠ headers i 5)
    (slot : Fin 3) (rank : ℕ) (positive : 0 < rank) (bound : rank ≤ 64) :
    let i : Fin 127 := ⟨2*rank-2,by omega⟩
    ∃ code : Pr P T Q prime U, ∀ (child : Descriptor) (w W L cutoff : ℕ),
      child.width = (w+1)*rank → volume prime child = (prime^(w+1))^16*((prime^(w+1))^112*W) →
      ∀ u (S : Stacks T prime), S.R cut = binSyms L cutoff →
      (slot ≠ 1 → S.R (headers i 5) = (Routines.hdr (helperAdjacentView (w+1) 1 W i) 5).map bitSymbol) →
      S.R (bank 34) = [] → S.R (bank 0) = [] → S.R (bank 1) = [] →
      let word := invocationWorkerRecord slot child L cutoff
      ∃ z t, Exec body code (mk u S) t (mk z {S with R := Function.update S.R (bank 34) word}) ∧
        z.user = u.user ∧ t ≤ 6*word.length+7 := by
  intro i
  by_cases copy : slot = 1
  · refine ⟨bcopy cut (bank 34) (bank 0) (bank 1),?_⟩
    intro child w W L cutoff shape size u S header field empty a b word
    obtain ⟨z,user,run⟩ := bcopy_exec (body := body) (a := cut) (c := bank 34) (t₁ := bank 0) (t₂ := bank 1)
      (by simp [Ne.symm (offCut _)]) u S a b
    rw [header,empty,List.append_nil,length_binSyms] at run
    exact ⟨z,_,by simpa [word,invocationWorkerRecord,copy] using run,user,by simp [word,invocationWorkerRecord,copy,length_binSyms]⟩
  · obtain ⟨code,prepare⟩ := prepareMoveArchive body bank cut headers offCut offHeader rank positive bound
    refine ⟨code,?_⟩
    intro child w W L cutoff shape size u S header field empty a b word
    obtain ⟨z,run,user⟩ := prepare child w W L cutoff shape size u S header (field copy) empty a b
    refine ⟨z,_,by simpa [word,invocationWorkerRecord,copy] using run,user,?_⟩
    simp [word,invocationWorkerRecord,copy,length_binSyms]
    omega

/-- Start and finish with an empty occurrence archive. The worker's budget is
charged once; copying and retiring its temporary archive cost at most 33 steps per cell. -/
theorem callInvocationFromHeaders [M8.Machine.Net] {P U : Type} {T Q : ℕ}
    (body : P → Pr P T Q prime U) (entry : P)
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (cut : Fin T) (headers : Fin 127 → Fin 6 → Fin T)
    (offCut : ∀ j, scheduledRecordPorts ports j ≠ cut)
    (offHeader : ∀ i j, scheduledRecordPorts ports j ≠ headers i 5)
    (slot : Fin 3) (rank : ℕ) (positive : 0 < rank) (bound : rank ≤ 64) :
    let bank := scheduledRecordPorts ports
    let i : Fin 127 := ⟨2*rank-2,by omega⟩
    ∃ code : Pr P T Q prime U, ∀ (node child : Descriptor) w W L cutoff price,
      let suffix := (prime^(w+1))^112*W
      let V := volume prime child
      child.width = (w+1)*rank → V = (prime^(w+1))^16*suffix → L ≤ V → 0 < V →
      ∀ position, ScheduledChildExec node child w suffix ports (invocationWorkerRecord slot child L cutoff)
        position body entry price true → child.width < node.width →
      let stored := RecordReady (b := prime) (w := w) (d := 16) (W := suffix) bank
        (prime^(w+1)).size suffix.size [] SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
      let clean := fun (S : Stacks T prime) => ∀ j : Fin (rowSwapBlock.tapes+35), 35 ≤ j.val →
        S.L (ports j) = [] ∧ S.R (ports j) = []
      ∀ word u S, stored word S → clean S → S.R cut = binSyms L cutoff →
        (slot ≠ 1 → S.R (headers i 5) = (Routines.hdr (helperAdjacentView (w+1) 1 W i) 5).map bitSymbol) →
        ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧ CleanupBound S F t (price+33*V) ∧
          z.user = u.user ∧ stored y F ∧ clean F ∧
          (∀ j, (∀ k, ports k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
          ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) h := by
  intro bank i
  obtain ⟨load,write⟩ := writeInvocationArchive body bank cut headers offCut offHeader slot rank positive bound
  refine ⟨load.seq ((body entry).seq (bclear (bank 34))),?_⟩
  intro node child w W L cutoff price suffix V shape size precision live position worker smaller stored clean word u S ready free header field
  let archive := invocationWorkerRecord slot child L cutoff
  obtain ⟨v,a,start,user,time⟩ := write child w W L cutoff shape size u S header field ready.archive
    (ready.scratch 0 (by decide)).2 (ready.scratch 1 (by decide)).2
  have high (j : Fin (rowSwapBlock.tapes+35)) (hj : 35 ≤ j.val) : ports j ≠ bank 34 := by
    intro eq
    have h := congrArg Fin.val (ports.injective eq)
    change j.val = 34 at h
    omega
  obtain ⟨q,D,t,y,run,paid,same,out,blank,frame,read⟩ := worker smaller v _ word
    (replaceArchive bank [] archive word S ready)
    (fun j hj => ⟨(free j hj).1,(Function.update_of_ne (high j hj) ..).trans (free j hj).2⟩)
  obtain ⟨z,done,_,clear⟩ := bclear_exec (body := body) (bank 34) q D
  rw [out.archive] at clear
  refine ⟨z,_,_,y,start.seq (run.seq clear),?_,done.trans (same.trans user),
    replaceArchive bank archive [] y D out,?_,?_,read⟩
  · have restored := paid.updateRight (bank 34) [] ((Function.update_self ..).trans out.archive.symm)
    have initial : ({S with R := Function.update (Function.update S.R (bank 34) archive) (bank 34) []} : Stacks T prime) = S := by
      congr 1
      rw [Function.update_idem,← ready.archive,Function.update_eq_self]
    change CleanupBound {S with R := Function.update (Function.update S.R (bank 34) archive) (bank 34) []}
      {D with R := Function.update D.R (bank 34) []} t price at restored
    rw [initial] at restored
    have mass : CopyChildLayout.spectators child ≤ V := by
      have h : V = (prime^child.width*prime^child.width)*CopyChildLayout.spectators child := by
        unfold V volume CopyChildLayout.spectators
        ring
      rw [h]
      exact Nat.le_mul_of_pos_left _ (by have := Shared50ModularControl.prime_prime.pos; positivity)
    have digits := (Nat.size_le.mpr Nat.lt_two_pow_self).trans mass
    have length : archive.length ≤ 2*V+1 := by
      by_cases h : slot = 1 <;> simp [archive,invocationWorkerRecord,h,length_binSyms] <;> omega
    intro js nd
    have bill := restored js nd
    change a ≤ 6*archive.length+7 at time
    change a+(t+(2*archive.length+2))+_ ≤ _+_
    omega
  · intro j hj
    exact ⟨(blank j hj).1,(Function.update_of_ne (high j hj) ..).trans (blank j hj).2⟩
  · intro j outside
    have ne : j ≠ bank 34 := (outside _).symm
    exact ⟨(frame j outside).1,(Function.update_of_ne ne ..).trans ((frame j outside).2.trans (Function.update_of_ne ne ..))⟩

/-- Install the charged worker for one slot of the selected invocation. Its
table is fixed before the descriptor, cutoff and recursive budget are supplied. -/
theorem installInvocationWorker [M8.Machine.Net] :
    ∃ C : ℝ, ∀ {P U : Type} {T Q : ℕ} (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
      (_cap : max columnCapacity stoppedCopyMachine.1 ≤ Q) (n : Fin 9) (p : StageRun)
      (j : Fin 3) (k : Fin nodeChildren5.length), (j = 1 → ∃ i, k = copyChildPosition (n,p,i)) →
      ∀ (large : P → Pr (WorkerLabel P) T Q prime U) (f : P),
      ∃ body : WorkerLabel P → Pr (WorkerLabel P) T Q prime U,
      (∀ g, body (.active g) = large g) ∧
      ∀ (node : Descriptor) (w W rows L cutoff budget : ℕ), node.width = 64*(w+1) →
      node.rows = 142080*rows → 0 < W → cutoff < 2^L →
      let child := scheduledChild prime node k
      child.width.size ≤ L → ∀ position, invocationCoordinates (v := child) j (w+1) W position →
      ∀ rate : ℝ, C ≤ rate →
      let header := binSyms (A := prime) L cutoff
      let price := if cutoff < child.width then budget else
        ⌊(rate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊
      (cutoff < child.width → if j = 1 then
        ScheduledChildExec node child w W ports header position body (.active f) budget true
        else MoveOnBankExec node child w W (movePrefix.trans ports) header position body (body (.active f)) budget true) →
      ScheduledChildExec node child w W ports (invocationWorkerRecord j child L cutoff) position body .entry
        (price+4*w+23*child.width+22*L+8*(CopyChildLayout.spectators child).size+61) true := by
  obtain ⟨copyRate,copy⟩ := cutoffCopyProgram true
  let core : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
  refine ⟨max (391*(163+core)) copyRate,?_⟩
  intro P U T Q ports cap n p j k slot large f
  by_cases mid : j = 1
  · obtain ⟨i,rfl⟩ := slot mid
    let cmp := cutoffColumnSlots.trans (scheduledRecordPorts ports)
    let fits := (le_max_right _ _).trans cap
    let body := workerTable (fun a b => (ordinaryCutoffTest cmp 7).seq
      (.cond (fun z => symBit (z.scan (cmp 7))) a b)) (stoppedCopyProgram ports fits) large f
    refine ⟨body,fun _ => rfl,?_⟩
    intro node w W rows L cutoff budget width split pos cutFits child digits position coords rate enough header price recur
    rw [invocationWorkerRecord,ite_eq_left mid]
    apply ScheduledChildExec.weaken (copy ports fits body .entry (.active f) .leaf rfl rfl node n p i w W rows L cutoff
      width split cutFits digits position (by simpa only [invocationCoordinates,ite_eq_left mid] using coords)
      pos rate budget ((le_max_right _ _).trans enough) (fun h => by simpa only [ite_eq_left mid] using recur h))
    dsimp only [price,child]
    omega
  · let rank := nodeChildren5[k.val]
    obtain ⟨leaf,move⟩ := scheduledTwoFieldMove (P := WorkerLabel P) (U := U) ports ((le_max_left _ _).trans cap)
      rank (nodeChildren5_bounds k).1 true (fun _ => (nodeChildren5_bounds k).2.trans (by decide : 42 ≤ 64))
    let body := workerTable (twoFieldDispatch (movePrefix.trans ports) (ports moveSpectatorPort) rank) leaf large f
    refine ⟨body,fun _ => rfl,?_⟩
    intro node w W rows L cutoff budget width split pos cutFits child digits position coords rate enough header price recur
    have shape : child.width = (w+1)*rank := by
      change rank*(node.width/64) = _
      rw [width,Nat.mul_div_cancel_left _ (by decide),Nat.mul_comm]
    rw [invocationWorkerRecord,ite_eq_right mid]
    exact move body .entry (.active f) .leaf rfl rfl node child w W L cutoff budget shape cutFits digits position
      (by simpa only [invocationCoordinates,ite_eq_right mid] using coords) pos rate ((le_max_left _ _).trans enough)
      (fun h => by simpa only [ite_eq_right mid] using recur h)

/-- Cost at the global child index used by the invocation's contiguous bill. -/
noncomputable def cutoffInvocationTime [M8.Machine.Net] (node : Descriptor) (L cutoff : ℕ) (rate : ℝ)
    (budget : ℕ → ℕ) (i : ℕ) : ℕ :=
  if h : i < nodeChildren5.length then
    let d := scheduledChild prime node ⟨i,h⟩
    let price := if cutoff < d.width then budget i else
      ⌊(rate*(d.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime d⌋₊
    price+22*(L-node.width)
  else 0

/-- The selected invocation with fixed cutoff tables installed for every MOVE
and COPY. Smaller active children are the only remaining execution premises. -/
theorem selectedCutoffInvocation [M8.Machine.Net] (P U : Type) (n : Fin 9) (p : StageRun) :
    let l := (phaseMoveBlocks (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)).1.length
    let r := (phaseMoveBlocks (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter)).1.length
    let count := invocationCounts l r
    ∃ (pre : Fin l → MoveIndex) (post : Fin r → MoveIndex),
    (∀ i, (pre i).val = i.val) ∧ (∀ i, (post i).val = l+i.val) ∧
    let child := invocationChildren n p pre post
    ∃ (ts : ∀ j, Fin (count j) → ℕ) (ports : ∀ j i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts j i))
      (states : ℕ) (leafRate : ℝ), ∀ {Q : ℕ}, states ≤ Q →
    ∀ (large : ∀ j i, P → Pr (WorkerLabel P) (ts j i) Q prime U) (f : ∀ j, Fin (count j) → P),
    ∃ body : ∀ j i, WorkerLabel P → Pr (WorkerLabel P) (ts j i) Q prime U,
    (∀ j i g, body j i (.active g) = large j i g) ∧
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (cut : Fin T)
      (host : (Σ j, Fin (count j) × WorkerLabel P) → Pr (Σ j, Fin (count j) × WorkerLabel P) T Q prime U)
      (code : Pr (Σ j, Fin (count j) × WorkerLabel P) T Q prime U) (a b c : ℕ),
    (∃ D : ℝ, ∀ w V : ℕ, 0 < V → (((a+b*swapVolumeRate w)*V+c : ℕ) : ℝ) ≤
      D*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)) ∧
    ∀ (node : Descriptor) (w B rows : ℕ), node.width = 64*(w+1) → node.rows = 142080*rows →
    node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := node.beforeRows*rows*node.between*node.afterD
    let blocks := M^112*B
    let W := blocks*prime^(64*((w+1)*64))*K
    let V := M^16*W
    let desc := fun j i => scheduledChild prime node (child j i)
    0 < W → ∃ position : ∀ j i, Fin (volume prime (desc j i)) ≃ Fin V,
    (∀ j i, invocationCoordinates j (w+1) W (position j i)) ∧
    ∀ (L cutoff : ℕ) shared, ∃ seed : Stacks T prime, embStk fan seed = shared ∧ seed.R cut = binSyms L cutoff ∧
    ∀ (budget : ℕ → ℕ) (rate : ℝ), leafRate ≤ rate → cutoff < 2^L →
    node.width.size ≤ L →
    let time := cutoffInvocationTime node L cutoff rate budget
    (∀ j i, let d := desc j i
      cutoff < d.width → d.width < node.width →
      if j = 1 then ScheduledChildExec node d w W (ports j i) (binSyms L cutoff) (position j i)
        (body j i) (.active (f j i)) (budget (child j i).val) true
      else MoveOnBankExec node d w W (movePrefix.trans (ports j i)) (binSyms L cutoff) (position j i)
        (body j i) (large j i (f j i)) (budget (child j i).val) true) →
      ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, PrivateTapes fan seed S → HelperFan fan x S →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ CleanupBound S F t
        ((a+b*swapVolumeRate w)*V+c+((List.range' (stageChildStart n+runChildStart p) Geometry.Moves.localPaid.length).map time).sum) ∧
        z.user = u.user ∧ HelperFan fan y F ∧ BorrowedStep n (w+1) blocks K p x y := by
  classical
  intro l r count
  obtain ⟨pre,post,first,last,ts,ports,states,build⟩ := selectedInvocation (WorkerLabel P) U n p
  obtain ⟨C,install⟩ := installInvocationWorker
  refine ⟨pre,post,first,last,ts,ports,max states (max columnCapacity stoppedCopyMachine.1),C,?_⟩
  intro Q cap large f
  let child := invocationChildren n p pre post
  have slots (j : Fin 3) (i : Fin (count j)) : j = 1 → ∃ k, child j i = copyChildPosition (n,p,k) := by
    rintro rfl
    exact ⟨i,rfl⟩
  choose body active worker using fun j i => install (ports j i) ((le_max_right _ _).trans cap)
    n p j (child j i) (slots j i) (large j i) (f j i)
  obtain ⟨T,fan,cut,host,code,a,b,c,_,run⟩ := build ((le_max_left _ _).trans cap) body (fun _ _ => .entry)
  refine ⟨body,active,T,fan,cut,host,code,a+5000*Geometry.Moves.localPaid.length,b,c,?_,?_⟩
  · simpa only [Nat.zero_mul,Nat.add_zero] using borrowedWorkerCost (a+5000*Geometry.Moves.localPaid.length) b 0 c
  intro node w B rows width split label M K blocks W V desc pos
  obtain ⟨position,coords,execute⟩ := run node w B rows width split label pos
  refine ⟨position,coords,?_⟩
  intro L cutoff shared
  let tail := B*prime^(64*((w+1)*64))*K
  let exchange (j) (i : Fin (count j)) : Fin 127 :=
    ⟨2*nodeChildren5[(child j i).val]-2,by have := (nodeChildren5_bounds (child j i)).2; omega⟩
  let record := fun j i => invocationArchive j
    ((Routines.hdr (helperAdjacentView (w+1) 1 tail (exchange j i)) 5).map bitSymbol) (binSyms L cutoff)
  have records j i : invocationWorkerRecord j (desc j i) L cutoff = record j i := by
    let rank := nodeChildren5[(child j i).val]
    have shape : (desc j i).width = (w+1)*rank := by
      change rank*(node.width/64) = _
      rw [width,Nat.mul_div_cancel_left _ (by decide),Nat.mul_comm]
    have size := Fintype.card_congr (position j i)
    simp only [Fintype.card_fin] at size
    have field := moveSpectatorHeader (desc j i) w tail rank (nodeChildren5_bounds _).1
      ((nodeChildren5_bounds _).2.trans (by decide : 42 ≤ 64)) shape (by simpa [V,W,blocks,M,K,tail,Nat.mul_assoc] using size)
    change _ = invocationArchive j _ _
    unfold invocationArchive invocationWorkerRecord
    rw [show (Routines.hdr (helperAdjacentView (w+1) 1 tail (exchange j i)) 5).map (bitSymbol (a := prime)) = _ from field]
  obtain ⟨seed,view,header,run⟩ := execute record (binSyms L cutoff) shared
  refine ⟨seed,view,header,?_⟩
  intro budget rate enough fits digits time recurse
  let charged := fun k => time k+5000*V
  have children : ∀ j i, ScheduledChildExec node (desc j i) w W (ports j i)
      (invocationWorkerRecord j (desc j i) L cutoff) (position j i) (body j i) .entry (charged (child j i).val) true := by
    intro j i
    have smaller : (desc j i).width < node.width := by
      change nodeChildren5[(child j i).val]*(node.width/64) < node.width
      rw [width,Nat.mul_div_cancel_left _ (by decide)]
      exact Nat.mul_lt_mul_of_pos_right ((nodeChildren5_bounds _).2.trans_lt (by decide : 42 < 64)) (Nat.succ_pos w)
    have bill := worker j i node w W rows L cutoff (budget (child j i).val) width split pos fits
      ((Nat.size_le_size smaller.le).trans digits) (position j i) (coords j i) rate enough
      (fun h => by simpa only [active] using recurse j i h smaller)
    apply bill.weaken
    dsimp only [charged,time,cutoffInvocationTime]
    rw [dite_eq_left (child j i).isLt]
    have overhead := cutoffDispatchOverhead node w B K L width (child j i) pos (position j i)
    have size := Fintype.card_congr (position j i)
    simp only [Fintype.card_fin] at size
    change volume prime (scheduledChild prime node (child j i)) = V at size
    rw [size] at overhead
    let d := scheduledChild prime node (child j i)
    let price := if cutoff < d.width then budget (child j i).val else
      ⌊(rate*(d.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime d⌋₊
    change price+4*w+23*d.width+22*L+8*(CopyChildLayout.spectators d).size+61 ≤ price+22*(L-node.width)+5000*V
    change 4*w+23*d.width+22*L+8*(CopyChildLayout.spectators d).size+61 ≤ 5000*V+22*(L-node.width) at overhead
    omega
  intro x u S fresh live
  obtain ⟨z,F,t,y,step,paid,user,out,sem⟩ := run charged (fun j i => records j i ▸ children j i) x u S fresh live
  refine ⟨z,F,t,y,step,?_,user,out,sem⟩
  have addCost (indices : List ℕ) :
      (indices.map charged).sum = (indices.map time).sum+indices.length*(5000*V) := by
    simp [charged,List.sum_map_add,List.map_const']
  rw [addCost,List.length_range'] at paid
  have regroup (m total : ℕ) : (a+b*swapVolumeRate w)*V+c+(total+m*(5000*V)) =
      (a+5000*m+b*swapVolumeRate w)*V+c+total := by ring
  rw [regroup] at paid
  exact paid


end IntegerMultBounds.MathlibTM2.M6.BitNode
