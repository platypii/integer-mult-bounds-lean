module

public import IntegerMultBounds.MathlibTM2.M6.BitCompiledPackedParent

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open IntervalDescriptor
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

/-- Assemble the nine selected packed stages and the idle interval calls into the
parent transpose. The child directory partitions their recursive budgets. -/
theorem initializedPackedNode [M8.Machine.Net] (P U Config : Type) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let I := Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)
    ∃ (pre : Fin 9 → StageRun → Fin l → MoveIndex) (post : Fin 9 → StageRun → Fin r → MoveIndex),
    let child := fun n (i : I) => invocationChildren n i.1 (pre n i.1) (post n i.1) i.2.1 i.2.2
    ∃ (ts : Fin 9 → I → ℕ) (states : ℕ) (ports : ∀ n i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts n i)),
    ∀ {Q : ℕ}, states ≤ Q → ∃ (N : ℕ) (leafRate : ℝ), ∀ (large : ∀ n i, P → Pr (WorkerLabel P) (ts n i) Q prime U) (f : Fin 9 → I → P)
      (idleLarge : P → Pr (Unit ⊕ P) (72+N) Q prime U) (idleEntry : Fin 9 → P),
    ∃ (body : ∀ n i, WorkerLabel P → Pr (WorkerLabel P) (ts n i) Q prime U)
      (idleBody : Unit ⊕ P → Pr (Unit ⊕ P) (72+N) Q prime U),
    (∀ n i g, body n i (.active g) = large n i g) ∧ (∀ g, idleBody (.inr g) = idleLarge g) ∧
    ∃ (localWork : Fin 9 → ℕ → ℕ → ℕ) (assemblyRate : ℕ),
    (∃ C : ℝ, ∀ v : CutoffNodeInput, (v.localCharge localWork assemblyRate : ℝ) ≤
      C*((volume prime v.node : ℝ)*(v.node.width : ℝ)^M8.Machine.BudgetBound.tau)) ∧
    ∀ input : Config → CutoffNodeInput,
    let desc := fun c n i => scheduledChild prime (input c).node (child n i)
    ∃ position : ∀ c n i, Fin (volume prime (desc c n i)) ≃ Fin ((prime^((input c).w+1))^16*(input c).stageWidth),
    (∀ c n i, invocationCoordinates i.2.1 ((input c).w+1) (input c).stageWidth (position c n i)) ∧
    ∀ (budget : Config → ℕ → ℕ) (rate : ℝ), leafRate ≤ rate →
    let time := fun c => stageBranchTime (input c).node (input c).cutoff rate (budget c)
    (∀ c n i, let v := input c
      v.cutoff < (desc c n i).width →
      if i.2.1 = 1 then ScheduledChildExec v.node (desc c n i) v.w v.stageWidth (ports n i) (binSyms v.root.width.size v.cutoff)
        (position c n i) (body n i) (.active (f n i)) (budget c (child n i).val) true
      else MoveOnBankExec v.node (desc c n i) v.w v.stageWidth (movePrefix.trans (ports n i)) (binSyms v.root.width.size v.cutoff)
        (position c n i) (body n i) (large n i (f n i)) (budget c (child n i).val) true) →
    (∀ c n (j : Fin idleCopies.length), let v := input c
      let i := idleDirectoryIndex (n,j)
      let e := idleInterval n idleCopies[j.val].2
      v.cutoff < (scheduledChild prime v.node i).width →
      IntervalWorkerExec idleBody (.inr (idleEntry n)) (phaseIntervalChild (e.1+1) (e.2+1) (v.w+1) v.idleWidth 64)
        (v.w+1) v.idleWidth (budget c i.val) (binSyms v.root.width.size v.cutoff)) →
    ∃ (R : Type) (T : ℕ) (table : R → Pr R T Q prime U), ∃ code src dst, ∃ seed : Config → Stacks T prime,
      LoadsPackedSeed (nodeSeedWords ∘ input) (CutoffNodeInput.cells ∘ input) seed ∧ LoadsNodeSeedFromRecord input seed ∧
      SplitRecordChildFamily (P := R) (U := U) (Q := Q) input table dst (fun c =>
        (input c).localCharge localWork assemblyRate+∑ i : Fin nodeChildren5.length, time c i.val) ∧
      SplitRecordTreeFamily (P := R) (U := U) (Q := Q) input table dst rate budget ∧
      ∀ c, let v := input c
        PackedPieceHandoffWithCharge cleanupWeight v.cells (packedChildOutput (v.w+1) v.cells) table code src dst (seed c)
          (v.localCharge localWork assemblyRate+∑ i : Fin nodeChildren5.length, time c i.val) := by
  classical
  intro l r I
  have stages := flatDispatchedHandoff
  dsimp only at stages
  choose pre post ts states ports rates build using stages
  obtain ⟨q,assemble⟩ := assembledFlatNodeFamilyWithSeed (U := U) (Config := Config)
  let merge := 7+(CyclicRowCycle.states 142080+5)+4
  refine ⟨pre,post,ts,max (Finset.univ.sup states) (max q (max columnCapacity (merge+merge))),ports,?_⟩
  intro Q capacity
  have room := (Nat.le_max_right ..).trans capacity
  have idleRoom := (Nat.le_max_right ..).trans room
  obtain ⟨leafRate,N,leaf,_,dispatchIdle⟩ := seededIdleDispatch (U := U)
    ((Nat.le_max_left ..).trans idleRoom) ((Nat.le_max_right ..).trans idleRoom)
  refine ⟨N,max leafRate (Finset.univ.sup' Finset.univ_nonempty rates),?_⟩
  intro large f idleLarge idleEntry
  let idleBody : Unit ⊕ P → Pr (Unit ⊕ P) (72+N) Q prime U :=
    Sum.elim (fun g => embProg (Function.Embedding.refl _) Sum.inl (leaf g)) idleLarge
  choose body active tapes src dst host code cost seed load bound step using fun n => build n
    ((Finset.le_sup (Finset.mem_univ n)).trans ((Nat.le_max_left ..).trans capacity)) (large n) (f n)
  refine ⟨body,idleBody,active,fun _ => rfl,?_⟩
  obtain ⟨assemblyRate,join⟩ := assemble ((Nat.le_max_left ..).trans room)
  let localWork := fun n w V => cost n (w+1) V
  obtain ⟨C,localBound⟩ := CutoffNodeInput.localCharge_bound localWork assemblyRate (fun n =>
    ⟨(bound n).choose,fun w V hv => (bound n).choose_spec (w+1) V (Nat.succ_pos _) hv⟩)
  refine ⟨localWork,assemblyRate,⟨C,localBound⟩,?_⟩
  intro input desc
  choose positions coords runs using fun c n => step n (input c)
  refine ⟨positions,coords,?_⟩
  intro budget rate enough time recurse idle
  let work := fun c n => localWork n (input c).w (input c).cells
  let price := fun c n => work c n+((List.range' (stageChildStart n)
    (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map (time c)).sum
  let dispatch := fun c (i : Fin nodeChildren5.length) => 2*volume prime (scheduledChild prime (input c).node i)+time c i.val
  let W := fun c => (input c).idleWidth*142080
  let V := fun c => (prime^((input c).w+1))^128*W c
  let overhead := fun c => 1+(142081*(10*V c+10)+1)
  let idleCost := fun c (n : Fin 9) => (∑ j : Fin idleCopies.length, dispatch c (idleDirectoryIndex (n,j)))+1+(142081*(10*V c+10)+1)
  have positive (c : Config) : 0 < V c := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos (input c).idlePositive (by decide))
  let admissible := fun {T} (seed : Config → Stacks T prime) =>
    LoadsPackedSeed (nodeSeedWords ∘ input) V seed
  have assembleNode := join (@admissible) (LoadsPackedSeed.fixed _ V positive)
    (fun _ _ => LoadsPackedSeed.join) (fun c => (input c).w+1) W V (fun _ => rfl) positive (fun _ => Equiv.refl _) price idleCost
  obtain ⟨R,T,table,program,src,dst,initial,ready,run⟩ := assembleNode (by
    intro n
    refine ⟨_,tapes n,host n,code n,src n,dst n,_,nodeSweepLoader input (load n),?_⟩
    intro c
    have run := runs c n (budget c) rate ((Finset.le_sup' rates (Finset.mem_univ n)).trans
      ((le_max_right _ _).trans enough)) (recurse c n)
    exact stageCast n (input c).stageTail _ (cost n ((input c).w+1)) run) (by
    intro n
    let Job := (Fin 32 × Fin 5) × Fin 222
    let slot := (Fin.castAddEmb N) (24 : Fin 72)
    have workers (k : Job) := dispatchIdle idleBody Sum.inl (fun _ => rfl) n (idleCopyIndex k) (.inr (idleEntry n))
    obtain ⟨H,host,worker,src,dst,origin,free,prep⟩ := uniformRemainderWindow n (fun _ => 72+N) (fun _ => Unit ⊕ P)
      (fun _ => slot) (fun _ => idleBody) (fun k => (workers k).choose)
    refine ⟨_,H,host,worker,src,dst,_,nodeIdleLoader input origin free,?_⟩
    intro c
    have installed := prep ((input c).w+1) (W c)
      (fun _ => idleDispatchStacks N (input c).w (input c).idleWidth (input c).root.width.size (input c).cutoff) (dispatch c) (by
      intro k
      let j := idleCopyIndex k
      have run := (workers k).choose_spec
      intro word u S left right fresh
      let v := input c
      let i := idleDirectoryIndex (n,j)
      obtain ⟨z,F,t,y,exec,user,out,read,bill⟩ := run v.root v.path v.depth v.b v.cutoff v.w v.groups
        v.levels v.base v.rootWidth v.stop v.active v.width v.rows v.idlePositive word u S left right fresh
        (budget c i.val) (idle c n j)
      refine ⟨z,F,t,y,exec,?_,user,out,?_⟩
      · intro js nd
        apply (bill js nd).trans
        rw [Nat.add_assoc]
        apply Nat.add_le_add_left
        change 2*volume prime (scheduledChild prime v.node i)+_ ≤ 2*volume prime (scheduledChild prime v.node i)+time c i.val
        apply Nat.add_le_add_left
        simp only [time,stageBranchTime,dite_eq_left i.isLt]
        split
        · rfl
        · apply Nat.floor_mono
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans enough) (by positivity)) (by positivity)
      · change parentIntervalRead n idleCopies[j.val].2 (v.w+1) (v.idleWidth*142080) word y at read
        simpa only [j,idleCopyIndex_get] using read)
    exact installed)
  have fromRecord := LoadsPackedSeed.fromNodeRecord ready
  refine ⟨R,T,table,program,src,dst,initial,ready,fromRecord,?_⟩
  suffices physical : ∀ c, let v := input c
      PackedPieceHandoffWithCharge cleanupWeight v.cells (packedChildOutput (v.w+1) v.cells)
        table program src dst (initial c) (v.localCharge localWork assemblyRate+∑ i : Fin nodeChildren5.length, time c i.val) by
    exact ⟨splitRecordChildFamily fromRecord physical,
      splitRecordTreeBudget fromRecord localWork assemblyRate C (fun c => localBound (input c)) rate budget physical,physical⟩

  intro c v x u S words fresh
  obtain ⟨z,F,t,y,exec,paid,user,out,act⟩ := run c x u S words fresh
  refine ⟨z,F,t,y,exec,?_,user,out,act⟩
  intro js unique
  have bill := alignedNodeDirectoryBill (input c).node ⟨_,(input c).width⟩ ⟨_,(input c).rows⟩
    (time c) (price c) (idleCost c) (work c) (fun _ => overhead c)
    (fun i j => dispatch c (idleDirectoryIndex (i,j))) (fun _ => le_rfl)
    (fun i => by dsimp only [idleCost,overhead]; omega) (fun _ _ => le_rfl)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at bill
  have charged := paid js unique
  dsimp only [v]
  unfold CutoffNodeInput.localCharge
  dsimp only [work,overhead,V,W,CutoffNodeInput.cells] at bill charged ⊢
  omega

/-- Configurations in which every scheduled child has reached the cutoff. -/
abbrev TerminalNodeInput := {p : CutoffNodeInput // 42*(p.w+1) ≤ p.cutoff}

private theorem terminalChildren (c : TerminalNodeInput) (i : Fin nodeChildren5.length) :
    (scheduledChild prime c.val.node i).width ≤ c.val.cutoff := by
  change nodeChildren5[i.val]*(c.val.node.width/64) ≤ _
  rw [c.val.width,Nat.mul_div_cancel_left _ (by decide)]
  exact (Nat.mul_le_mul_right _ (nodeChildren5_bounds i).2).trans c.property

/-- The last active level supplies a fixed record machine with zero recursive allowances. -/
theorem terminalPackedTree [M8.Machine.Net] (U : Type) :
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q →
    ∃ (T : ℕ) (P : Type) (table : P → Pr P T Q prime U) (dst : Fin (142081+2) ↪ Fin T) (rate : ℝ),
      SplitRecordTreeFamily (Config := TerminalNodeInput) Subtype.val table dst rate (fun _ _ => 0) := by
  obtain ⟨pre,post,ts,states,ports,build⟩ := initializedPackedNode Unit U TerminalNodeInput
  refine ⟨states,?_⟩
  intro Q enough
  obtain ⟨N,rate,build⟩ := build enough
  obtain ⟨body,idle,_,_,work,assemble,_,run⟩ :=
    build (fun _ _ _ => .act .done) (fun _ _ => ()) (fun _ => .act .done) (fun _ => ())
  obtain ⟨position,_,execute⟩ := run Subtype.val
  obtain ⟨P,T,table,code,src,dst,seed,load,fromRecord,child,family,_⟩ :=
    execute (fun _ _ => 0) rate le_rfl (fun c n i active => False.elim ((terminalChildren c _).not_gt active))
      (fun c n j active => False.elim ((terminalChildren c _).not_gt active))
  exact ⟨T,P,table,dst,rate,family⟩

private theorem terminalBudget [M8.Machine.Net] (D rate : ℝ) (c : TerminalNodeInput)
    (active : c.val.cutoff < c.val.node.width) :
    let p := c.val
    cutoffTreeBudget D rate p.cutoff (p.depth-p.path.length) p.node = cutoffTreeBudget D rate p.cutoff 1 p.node := by
  intro p
  have remaining : 0 < p.depth-p.path.length := by
    have shrink : p.root.width*42^p.depth ≤ p.cutoff*64^p.depth := by
      rw [p.rootWidth]
      simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_right (64^p.depth) p.stop
    have := scheduledPath_length_lt prime p.root p.depth p.cutoff shrink p.path active
    omega
  obtain ⟨fuel,h⟩ := Nat.exists_eq_succ_of_ne_zero remaining.ne'
  rw [h,cutoffTreeBudget,cutoffTreeBudget,ite_eq_left active,ite_eq_left active]
  apply congrArg (_ + ·)
  apply Finset.sum_congr rfl
  intro k _
  have stop : ¬ p.cutoff < (scheduledChild prime p.node k).width := (terminalChildren c k).not_gt
  cases fuel <;> simp only [cutoffTreeBudget,ite_eq_right stop]

/-- Install the first active idle call above the terminal level. Its recursive
entry and its return to the physical owner tape are both supplied here. -/
theorem terminalIdleRecord [M8.Machine.Net] (U : Type) :
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q →
    ∃ (N : ℕ) (P : Type) (leafRate : ℝ), ∀ {T : ℕ}
      (i : Fin 9) (j : Fin idleCopies.length) (board : Fin 113 ↪ Fin T)
      (splitter : Fin intervalSplitTapes ↪ Fin T) (apart : ∀ r k, splitter r ≠ board k),
    let raw := (Fin.castLEEmb (by decide : 72 ≤ 113)).trans board
    let fields := idleRolePorts.trans board
    let src := raw 24
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    let embed := caller.trans (intervalExtend T N)
    ∃ minimum : ℝ, 0 ≤ minimum ∧
      ∃ table : Option (Empty ⊕ P) → Pr (Option (Empty ⊕ P)) (intervalHostSize T N) Q prime U,
      let work := idleCallerWork (((Fin.castAddEmb 35 (n := 78)).trans board).trans embed)
      ∃ (code : Pr (Option (Empty ⊕ P)) (intervalHostSize T N) Q prime U) (fixed base swaps : ℕ),
      ∀ D : ℝ, minimum ≤ D → ∀ (p : CutoffNodeInput) (blocks : ℕ), p.root.Positive →
      142080^(p.depth+1) ∣ p.root.rows → p.root.beforeH = blocks*prime^(64*p.root.width) →
      let child := scheduledChild prime p.node (idleDirectoryIndex (i,j))
      p.cutoff < child.width → 42*(child.width/64) ≤ p.cutoff →
      let budget := cutoffTreeBudget D leafRate p.cutoff 1 child
      let e := idleInterval i idleCopies[j.val].2
      let lane := phaseIntervalChild (e.1+1) (e.2+1) (p.w+1) p.idleWidth 64
      let wide := {lane with afterD := lane.afterD*142080}
      ∀ (word : Fin (volume prime wide) → ZMod 2) u S,
        RecordPayload (embed src) (fun _ => blank) 0 word S →
        IdleDispatchReady (raw.trans embed) p.w p.idleWidth p.root.width.size p.cutoff S →
        (∀ t ∈ work, S.L t = [] ∧ S.R t = []) →
        (∀ k, S.R (embed (fields k)) = (Routines.hdr (role p.node 142080) k).map bitSymbol) →
        ∃ z F n, Exec table code (mk u S) n (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F n (fixed*p.cells+
            (base+swaps*(@swapVolumeRate BinaryRadixEqualShared.supplierNet p.w))*(volume prime lane)+budget) ∧
          RecordPayload (embed src) (fun _ => blank) 0
            (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word) F ∧
          ∀ t, t ≠ embed src → F.L t = S.L t ∧ F.R t = S.R t := by
  obtain ⟨q,build⟩ := terminalPackedTree U
  let merge := 7+(CyclicRowCycle.states 142080+5)+4
  let swap := (@rowSwapBlock BinaryRadixEqualShared.supplierNet).states
  refine ⟨max q (max swap (merge+merge)),?_⟩
  intro Q fits
  obtain ⟨N,P,table,dst,leafRate,family⟩ := build ((Nat.le_max_left ..).trans fits)
  refine ⟨N,P,leafRate,?_⟩
  intro T i j board splitter apart raw fields src caller embed
  have room := (Nat.le_max_right ..).trans fits
  obtain ⟨minimum,nonneg,host,code,fixed,base,swaps,run⟩ := compiledIdleRecord family
    ((Nat.le_max_left ..).trans room) ((Nat.le_max_right ..).trans room) i j board splitter apart
  refine ⟨minimum,nonneg,host,code,fixed,base,swaps,?_⟩
  intro D enough p blocks positive rows label child active last budget e lane wide word u S payload ready fresh roles
  obtain ⟨c,node,root,path,cut,remaining,_,_,_,_,cells⟩ := activeIdleCutoffInput p blocks positive rows label i j active
  have live : c.cutoff < c.node.width := by simpa only [cut,node] using active
  have width : c.node.width/64 = c.w+1 := by rw [c.width,Nat.mul_div_cancel_left _ (by decide)]
  let x : TerminalNodeInput := ⟨c,by simpa only [← width,node,cut] using last⟩
  have result := run D enough p x node live (fun _ _ => Nat.zero_le _) word u S payload
    (by simpa only [x,root,cut] using ready) fresh roles
  have cost : cutoffTreeBudget D leafRate c.cutoff (c.depth-c.path.length) c.node = budget :=
    (terminalBudget D leafRate x live).trans (by simp only [x,cut,node,budget,child])
  simpa only [x,cost,← cells] using result

end IntegerMultBounds.MathlibTM2.M6.BitNode
