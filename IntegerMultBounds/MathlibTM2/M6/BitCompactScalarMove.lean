module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyOwnerFrame
public import IntegerMultBounds.MathlibTM2.M6.BitCutoffNode

/-! Run the scalar gates and inherited-coordinate MOVE at a selected phase position. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout Certificates.PR589
open Shared50ModularControl (prime)

private theorem scalarOnFan {k T Q V rate : ℕ} {P U : Type} (fan : Fin (k+2) ↪ Fin T)
    (body : P → Pr P T Q prime U) (code : Pr Empty (k+2) Q prime U)
    {x y : Fin k → Fin V → ZMod 2}
    (run : ∀ u S, HelperFan (Function.Embedding.refl _) x S →
      ∃ z F n, Exec Empty.elim code (mk u S) n (mk z F) ∧ CleanupBound S F n (rate*V) ∧
        z.user = u.user ∧ HelperFan (Function.Embedding.refl _) y F) :
    ∀ u S, HelperFan fan x S →
      ∃ z F n, Exec body (embProg fan Empty.elim code) (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F (n+tapeCharge cleanupWeight (frameSlots fan) F)
          (2*(rate*V)+tapeCharge cleanupWeight (frameSlots fan) S) ∧ HelperFan fan y F ∧
        ∀ j, (∀ i, fan i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro u S ready
  obtain ⟨v,D,n,exec,paid,user,out⟩ := run (embDn fan u) (embStk fan S) ready
  obtain ⟨z,F,placed,_,same,view,frame⟩ := exec_emb (body' := body) (ι := Empty.elim) fan.injective
    (fun f => nomatch f) exec u rfl S rfl
  rw [← view] at paid out
  have bound := CleanupBound.place fan frame paid
  refine ⟨z,F,n,placed,same.trans user,?_,out,frame⟩
  intro js nd
  have h := bound js nd
  have h' := bound (frameSlots fan) (frameSlots_nodup fan)
  change n+tapeCharge cleanupWeight _ F ≤ tapeCharge cleanupWeight _ S+rate*V at h'
  change n+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+rate*V at h
  change _+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
  omega

/-- Scalar gates, both basis conversions, and payload compaction have a single
linear local bill. The child runs in the parent's interval coordinates. -/
theorem compactScalarMove [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) (afterCopy : Bool)
    (j : Fin (selectedPhaseSchedule afterCopy).1.length) :
    let i := selectedPhaseIndex afterCopy j
    let edge := (Geometry.Moves.phaseEdges.filter positiveMove)[i.val]'i.isLt
    let lo := min (Geometry.Dimensions.value edge.1) (Geometry.Dimensions.value edge.2)
    let hi := max (Geometry.Dimensions.value edge.1) (Geometry.Dimensions.value edge.2)
    ∃ (T states : ℕ) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
      (fan : Fin (142081+2) ↪ Fin T) (basis : WorkerBasisLayout ports),
    basis.OwnerTapes fan ∧ ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (body : P → Pr P T Q prime U) (call childProc : P),
    let bank := scheduledRecordPorts ports
    body call = (body childProc).seq (compactOwner (bank 24) (bank 0) (bank 1)) →
    ∃ (code : Pr P T Q prime U) (rate : ℕ), ∀ (c : CutoffNodeInput) record,
      let child := scheduledChild prime c.node (phaseChildPositions.choose (n,p,i))
      let W := c.stageWidth
      let V := (prime^(c.w+1))^16*W
      let interval := phaseIntervalChild lo hi (c.w+1) W
      ∃ (position : Fin (volume prime child) ≃ Fin V) (size : volume prime interval = V),
        InheritedIntervalPositions child interval size position ∧ ∀ price,
        ScheduledChildExec c.node child c.w W ports record position body childProc price true →
        ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan fan x S →
        (∀ l, (∀ h, fan h ≠ l) → S.L l = (basis.seed c.w W record).L l ∧ S.R l = (basis.seed c.w W record).R l) →
        ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F (t+tapeCharge cleanupWeight (frameSlots fan) F)
            (price+rate*c.cells+tapeCharge cleanupWeight (frameSlots fan) S) ∧
          HelperFan fan (selectedMoveOutput (w := c.w+1) (W := W) n p afterCopy j x) F := by
  intro i edge lo hi
  let layout : Fin 661 ↪ Fin 142081 := ⟨ownerTape n p.1 p.2,ownerTape_injective ..⟩
  have mem := List.mem_filter.mp (List.getElem_mem (l := Geometry.Moves.phaseEdges.filter positiveMove) i.isLt)
  have checked := Geometry.Moves.phase_checked edge mem.1
  have positive : 0 < Geometry.moveRank edge.1 edge.2 := Nat.pos_of_ne_zero (bne_iff_ne.mp mem.2)
  obtain ⟨A,B',T,states,ports,fan,a,b,basis,owners,basisEq,apart,_,_,_,build⟩ :=
    allocatedPhaseMove_host true (layout (paidRegister i.val)) edge checked positive true
  obtain ⟨gateStates,compile⟩ := scalarOwnerLinear layout
  refine ⟨T,max states gateStates,ports,fan,basis,owners,?_⟩
  intro P U Q capacity body call childProc bank installed
  obtain ⟨base,swaps,move,run⟩ := build ((le_max_left ..).trans capacity) body call
  let schedule := selectedPhaseSchedule afterCopy
  let gates := schedule.1[j.val].1
  let suffix := if j.val+1 = schedule.1.length then schedule.2 else []
  obtain ⟨allowed,lastAllowed⟩ := selectedPhaseGates afterCopy j
  obtain ⟨preCode,preRate,enter⟩ := compile (U := U) ((le_max_right ..).trans capacity) gates allowed
  obtain ⟨last,lastRate,leave⟩ := compile (U := U) ((le_max_right ..).trans capacity) suffix lastAllowed
  refine ⟨(embProg fan Empty.elim preCode).seq (move.seq (embProg fan Empty.elim last)),
    2*preRate+26*base+2*lastRate+39,?_⟩
  intro c record child W V interval
  have align : c.B*prime^(64*((c.w+1)*64))*((prime^(c.w+1))^112*c.stageFactor) = W := by
    dsimp only [W,CutoffNodeInput.stageWidth]; ring
  have go := run c.node _ c.w c.B c.rowsPerStage (phaseChildPositions.choose_spec n p i).1 c.width c.rows c.label
  dsimp only at go
  dsimp only [CutoffNodeInput.stageFactor] at align
  rw [align] at go
  have pos : 0 < V := by
    rw [show V = c.cells from c.stageCells]
    exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos c.idlePositive (by decide))
  have posW : 0 < W := (Nat.pos_of_mul_pos_left pos)
  obtain ⟨position,coords,prep,work⟩ := go posW record (fun _ => blank) 0
  refine ⟨position,phaseIntervalChild_volume (phaseInterval_bounds checked positive).1.le (phaseInterval_bounds checked positive).2 (c.w+1) W,coords,?_⟩
  intro price worker x u S ready fresh
  obtain ⟨v,D,l,first,userA,billA,liveA,offA⟩ := scalarOnFan fan body preCode (enter pos x) u S ready
  obtain ⟨seed,init,kept⟩ := prep [] [] (fun z => by simp [readAt_nil_left,wordTape_nil]; rfl)
  let reserve := fun D : Stacks T prime => tapeCharge cleanupWeight (frameSlots fan) D
  let movePrice := price+16*V+23
  obtain ⟨z,G,m,y,exec,bill,user,out,_,read⟩ := work movePrice (by
    intro smaller q E word stored clean
    obtain ⟨z,F,t,y,exec,user,_,bound,rep,clean',_,_,frame,_,action⟩ :=
      compactScheduledCopy ports basis fan owners body childProc c.node child c.w W record position price
        worker smaller q E word stored clean
    refine ⟨z,F,t,y,by rw [installed]; exact exec,?_,user,rep,clean',fun l h => frame l (fun e => h _ e.symm) (.inl h),action⟩
    intro js nd
    have h := bound js nd
    change t+reserve F+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js E+(movePrice+reserve E)
    change t+tapeCharge cleanupWeight js F+reserve F ≤ tapeCharge cleanupWeight js E+reserve E+price+16*V+23 at h
    dsimp only [movePrice]
    omega) _ v D liveA ⟨seed,init,fun l h => by
      have off := offA l (apart l h)
      have start := fresh l (apart l h)
      rw [basisEq] at start
      exact ⟨off.1.trans (start.1.trans (kept l h).1),off.2.trans (start.2.trans (kept l h).2)⟩⟩
  have moved := moveOwnerEffect_of_exec layout _ i.val edge checked y read
  rw [moved] at out
  obtain ⟨q,F,t,finish,userB,billB,result,_⟩ := scalarOnFan fan body last (leave pos _) z G out
  refine ⟨q,F,_,first.seq (exec.seq finish),userB.trans (user.trans userA),?_,?_⟩
  · intro js nd
    have ha := billA js nd
    have hm := bill js nd
    have hb := billB js nd
    change l+reserve D+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+(2*(preRate*V)+reserve S) at ha
    change m+reserve G+tapeCharge cleanupWeight js G ≤ tapeCharge cleanupWeight js D+
      (movePrice+13*((base+0*swapVolumeRate c.w)*V)+13*(base*V)+reserve D) at hm
    change t+reserve F+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js G+(2*(lastRate*V)+reserve G) at hb
    change l+(m+t)+reserve F+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
      (price+_*c.cells+reserve S)
    rw [← c.stageCells]
    change _ ≤ _+(price+(2*preRate+26*base+2*lastRate+39)*V+reserve S)
    simp only [movePrice,Nat.zero_mul,Nat.add_zero,Nat.add_mul,Nat.mul_assoc] at hm ⊢
    omega
  · have facts := selectedPhaseIndex_spec afterCopy j
    dsimp only [selectedMoveOutput]
    rw [← facts.1,← facts.2]
    exact result

/-- Execute a selected scalar/MOVE block with its cutoff test and stopped worker installed. -/
theorem cutoffScalarMove [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) (afterCopy : Bool)
    (j : Fin (selectedPhaseSchedule afterCopy).1.length) :
    let i := selectedPhaseIndex afterCopy j
    let edge := (Geometry.Moves.phaseEdges.filter positiveMove)[i.val]'i.isLt
    let lo := min (Geometry.Dimensions.value edge.1) (Geometry.Dimensions.value edge.2)
    let hi := max (Geometry.Dimensions.value edge.1) (Geometry.Dimensions.value edge.2)
    ∃ (C : ℝ) (T states : ℕ) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
      (fan : Fin (142081+2) ↪ Fin T) (basis : WorkerBasisLayout ports),
    basis.OwnerTapes fan ∧ ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (fits : (stoppedIntervalMachine lo hi).1 ≤ Q)
      (large : P → Pr (Option (WorkerLabel P)) T Q prime U) (f : P),
    ∃ body : Option (WorkerLabel P) → Pr (Option (WorkerLabel P)) T Q prime U,
      (∀ g, body (some (.active g)) = large g) ∧
      ∃ (code : Pr (Option (WorkerLabel P)) T Q prime U) (rate : ℕ), ∀ c : CutoffNodeInput,
      let record := binSyms c.root.width.size c.cutoff
      let child := scheduledChild prime c.node (phaseChildPositions.choose (n,p,i))
      let W := c.stageWidth
      let V := (prime^(c.w+1))^16*W
      let interval := phaseIntervalChild lo hi (c.w+1) W
      ∃ (position : Fin (volume prime child) ≃ Fin V) (size : volume prime interval = V),
        InheritedIntervalPositions child interval size position ∧ ∀ (leafRate : ℝ) (recursiveTime : ℕ), C ≤ leafRate →
        let price := if c.cutoff < child.width then recursiveTime else
          ⌊(leafRate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊
        (c.cutoff < child.width → ScheduledChildExec c.node child c.w W ports record position body (some (.active f)) recursiveTime true) →
        ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan fan x S →
        (∀ l, (∀ h, fan h ≠ l) → S.L l = (basis.seed c.w W record).L l ∧ S.R l = (basis.seed c.w W record).R l) →
        ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F (t+tapeCharge cleanupWeight (frameSlots fan) F)
            (price+rate*c.cells+tapeCharge cleanupWeight (frameSlots fan) S) ∧
          HelperFan fan (selectedMoveOutput (w := c.w+1) (W := W) n p afterCopy j x) F := by
  intro i edge lo hi
  have mem := List.mem_filter.mp (List.getElem_mem (l := Geometry.Moves.phaseEdges.filter positiveMove) i.isLt)
  have checked := Geometry.Moves.phase_checked edge mem.1
  have positive : 0 < Geometry.moveRank edge.1 edge.2 := Nat.pos_of_ne_zero (bne_iff_ne.mp mem.2)
  obtain ⟨ordered,within⟩ := phaseInterval_bounds checked positive
  obtain ⟨C,dispatch⟩ := cutoffIntervalProgram ordered within
  obtain ⟨T,states,ports,fan,basis,owners,make⟩ := compactScalarMove n p afterCopy j
  refine ⟨C,T,states,ports,fan,basis,owners,?_⟩
  intro P U Q capacity fits large f
  let body := compactIntervalTable lo hi ports fits large f
  refine ⟨body,fun _ => rfl,?_⟩
  obtain ⟨code,rate,run⟩ := make capacity body none (some .entry) rfl
  refine ⟨code,rate+10000,?_⟩
  intro c record child W V interval
  obtain ⟨position,size,coords,step⟩ := run c record
  refine ⟨position,size,coords,?_⟩
  intro leafRate recursiveTime enough price active x u S ready fresh
  let k := phaseChildPositions.choose (n,p,i)
  have shape := (scheduledChild_measures prime c.node ⟨_,c.width⟩ ⟨_,c.rows⟩ k).1
  rw [(phaseChildPositions.choose_spec n p i).1,c.width] at shape
  have rank := phaseIntervalChild_width checked (c.w+1) W
  change (hi-lo)*(c.w+1) = Geometry.moveRank edge.1 edge.2*(c.w+1) at rank
  have width : child.width = (hi-lo)*(c.w+1) := by
    change child.width*64 = Geometry.moveRank edge.1 edge.2*(64*(c.w+1)) at shape
    rw [Nat.mul_left_comm, Nat.mul_comm 64] at shape
    omega
  have small (path : List (Fin nodeChildren5.length)) : (path.foldl (scheduledChild prime) c.root).width ≤ c.root.width := by
    have := directoryDigits_bound prime c.root path
    omega
  have cutFits := (c.active.trans (small c.path)).trans_lt (Nat.lt_size_self _)
  have room : child.width.size ≤ c.root.width.size := Nat.size_le_size (by
    simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil] using small (c.path++[k]))
  have cellsPos : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos (c.w+1)) 128)
    (Nat.mul_pos c.idlePositive (by decide : 0 < 142080))
  have pos : 0 < W := Nat.pos_of_mul_pos_left (c.stageCells.symm ▸ cellsPos)
  have worker := dispatch ports fits body (some .entry) (some (.active f)) (some .leaf) rfl rfl c.node child c.w W _ c.cutoff
    width cutFits room position coords pos leafRate recursiveTime enough active
  obtain ⟨z,F,t,exec,user,paid,out⟩ := step _ worker x u S ready fresh
  refine ⟨z,F,t,exec,user,workerCost.weaken (charged := true) paid ?_,out⟩
  apply Nat.add_le_add_right
  change 4*c.w+23*child.width+22*c.root.width.size+51+price+rate*c.cells ≤ _
  have childBound : child.width ≤ 8*(c.w+1) := width ▸ Nat.mul_le_mul_right _ ((Nat.sub_le hi lo).trans within)
  have load := c.remainderSetup_le 1
  rw [Nat.add_mul]
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
