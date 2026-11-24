module

public import IntegerMultBounds.MathlibTM2.M6.BitStageChartHeaders
public import IntegerMultBounds.MathlibTM2.M6.BitInitializedChartWorker

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout
open Shared50ModularControl (prime)

private theorem sweepRoles_of_borrowed (n : Fin 9) (w B K : ℕ) :
    let M := prime^w
    let W := B*prime^(64*(w*64))*K
    let V := M^16*(M^112*B*prime^(64*(w*64))*K)
    ∀ (size : M^128*W = V) (x y : Fin 142081 → Fin V → ZMod 2),
    (∀ (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w), borrowedStageRead n b t g y = (Piece.stage n).run (borrowedStageRead n b t g x)) →
    ∀ j : Fin W, sweepRoles n 0 j (sweepView (w := w) size y) = (Piece.stage n).run (sweepRoles n 0 j (sweepView size x)) := by
  intro M W V size x y effect j
  obtain ⟨b,g,t,rfl⟩ := borrowedSpectator_covers j
  have read (d : Fin 142081 → Fin V → ZMod 2) :
      sweepRoles n 0 (borrowedSpectator b g t) (sweepView size d) = borrowedStageRead n b t g d := by
    rw [borrowedStageRead_eq_sweepRoles]
    rfl
  exact (read _).trans ((effect b t g).trans (congrArg (Piece.stage n).run (read _).symm))

private theorem addChartCharge {T : ℕ} (S F : Stacks T prime) (m localFee kids : ℕ) (charge : ℝ)
    (bill : ∀ js : List (Fin T), js.Nodup → (m : ℝ)+tapeCharge cleanupWeight js F ≤
      tapeCharge cleanupWeight js S+(localFee+kids : ℕ)+charge) :
    CleanupBound S F m (localFee+⌈charge⌉₊+kids) := by
  intro js nd
  have h := bill js nd
  have le := Nat.le_ceil charge
  exact_mod_cast (show (m : ℝ)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
    ((localFee+⌈charge⌉₊+kids : ℕ) : ℝ) by push_cast at h ⊢; linarith only [h,le])

private theorem correctedStageCost_bound [M8.Machine.Net] (a b : ℕ) (rate C : ℝ) :
    let cost := fun (w V : ℕ) => a*V+b*LeafCore.coreCost V w+⌈rate*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)⌉₊+
      ⌈C*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊
    ∃ D : ℝ, ∀ w V : ℕ, 0 < w → 0 < V → (cost w V : ℝ) ≤ D*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau) := by
  intro cost
  obtain ⟨D,bound⟩ := packedStageCost_bound a b rate C
  refine ⟨D,fun w V hw hv => (Nat.cast_le.mpr ?_).trans (bound w V hw hv)⟩
  dsimp only [cost]
  generalize a*V = x
  generalize LeafCore.coreCost V w = y
  nlinarith only [Nat.zero_le (x*b),Nat.zero_le (b*y)]

/-- The corrected stage executes between the forward and return charts on flat owner addresses. -/
theorem flatDispatchedStage [M8.Machine.Net] (n : Fin 9) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let I := Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)
    let k := 142081+2
    ∃ (pre : StageRun → Fin l → MoveIndex) (post : StageRun → Fin r → MoveIndex),
    let child := fun i : I => invocationChildren n i.1 (pre i.1) (post i.1) i.2.1 i.2.2
    ∃ (ts : I → ℕ) (states : ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts i)),
    ∃ (leafRate : ℝ) (chartSpace returnSpace : ℕ), ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (large : ∀ i, P → Pr (WorkerLabel P) (ts i) Q prime U) (f : I → P),
    ∃ body : ∀ i, WorkerLabel P → Pr (WorkerLabel P) (ts i) Q prime U, (∀ i g, body i (.active g) = large i g) ∧
    ∃ (H : ℕ) (fan : Fin (k+1) ↪ Fin H) (space : ℕ)
      (table : I × WorkerLabel P → Pr (I × WorkerLabel P) (H+37) Q prime U),
    let inner := (Fin.castAddEmb 1).trans (fan.trans (Fin.castAddEmb 37))
    ∀ {T : ℕ} (mid : Fin (H+37) ↪ Fin T) (entry ret : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (caller : Fin 6 ↪ Fin T),
    (∀ i j, entry i ≠ mid j) → (∀ i j, ret i ≠ mid j) → (∀ i j, caller i ≠ mid j) →
    (∀ i j, entry i ≠ caller j) → (∀ i j, ret i ≠ caller j) → (∀ i j, ret i ≠ entry j) →
    let outer := mid.trans (Fin.castAddEmb (24+space))
    let host := fun f => embProg outer id (table f)
    let live := inner.trans outer
    ∀ {N : ℕ} (place : Fin (T+(24+space)) ↪ Fin N)
      (chart : Fin (rowSwapBlock.tapes+35+chartSpace) ↪ Fin N) (back : Fin returnSpace ↪ Fin N)
      (outerCaller : Fin 6 ↪ Fin N),
    (∀ i j, chart i ≠ place j) → (∀ i j, back i ≠ place j) → (∀ i j, back i ≠ chart j) →
    (∀ i j, outerCaller i ≠ place j) → (∀ i j, chart i ≠ outerCaller j) → (∀ i j, back i ≠ outerCaller j) →
    ∀ (archive : Fin (80+273) ↪ Fin N), (∀ i j, archive i ≠ place j) →
    (∀ i j, archive i ≠ outerCaller j) → (∀ i j, archive i ≠ chart j) → (∀ i j, archive i ≠ back j) →
    let installed := fun f => embProg place id (host f)
    ∃ code, ∃ (localCost : ℕ → ℕ → ℕ),
    (∃ D : ℝ, ∀ w V : ℕ, 0 < w → 0 < V → (localCost w V : ℝ) ≤
      D*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)) ∧ ∀ c : CutoffNodeInput,
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
    let core := (Fin.castAddEmb 37).trans outer
    let header := (Fin.natAddEmb H (m := 37)).trans outer
    let W := c.B*prime^(64*(w*64))*c.stageFactor
    let size : (prime^w)^128*W = V := (ordinaryCompact_width _ _).symm.trans (by simp [V,W,CutoffNodeInput.stageWidth,Nat.mul_assoc,w])
    ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan (live.trans place) x S →
      let D := embStk place S
      D.L (core (fan (Fin.last k))) = [] → D.R (core (fan (Fin.last k))) = binSyms c.root.width.size c.cutoff →
      (∀ j, (∀ i, fan i ≠ j) → D.L (core j) = [] ∧ D.R (core j) = []) →
      (∀ i, D.L (header i) = [] ∧ D.R (header i) =
        callerHeaderBank (fun j => (Routines.hdr c.node j).map (bitSymbol (a := prime))) i) →
      ParentArchiveInput c.node c.w (embStk archive S) →
      (∀ i, D.R ((caller i).castAdd _) = []) →
      (∀ i, i.val ≠ 24 → D.L ((entry i).castAdd _) = [] ∧ D.R ((entry i).castAdd _) = []) →
      (∀ i, i.val ≠ 24 → D.L ((ret i).castAdd _) = [] ∧ D.R ((ret i).castAdd _) = []) →
      (∀ j : Fin (24+space), D.L (j.natAdd T) = [] ∧ D.R (j.natAdd T) = []) →
      (∀ i, S.R (outerCaller i) = []) →
      (∀ i, S.L (chart i) = [] ∧ S.R (chart i) = []) → (∀ i, S.L (back i) = [] ∧ S.R (back i) = []) →
      ∃ z F t y, Exec installed code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (localCost w V+
          ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum) ∧
        HelperFan (live.trans place) y F ∧ ∀ j : Fin W,
          let address := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
          readRoles address y = (Piece.stage n).run (readRoles address x) := by
  intro l r I k
  obtain ⟨pre,post,ts,qs,ports,leafRate,build⟩ := dispatchedCorrectedStage n
  obtain ⟨a,b,cs,charts⟩ := initializedChartWorker n
  let setupQ := (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080)
  refine ⟨pre,post,ts,max (max qs cs) setupQ,ports,leafRate,a,b,?_⟩
  intro P U Q cap large f
  obtain ⟨body,active,H,fan,space,table,build⟩ := build ((le_max_left ..).trans ((le_max_left ..).trans cap)) large f
  refine ⟨body,active,H,fan,space,table,?_⟩
  intro inner T mid entry ret caller ea ra ca ec rc re outer host live N place chart back outerCaller
    chartOff backOff disjoint clockOff chartClock backClock archive archMid archCaller archChart archBack installed
  obtain ⟨worker,rate,base,leaf,stage⟩ := build mid entry ret caller ea ra ca ec rc re
  obtain ⟨C,code,run⟩ := charts host worker place live chart back outerCaller ((le_max_right ..).trans ((le_max_left ..).trans cap))
    chartOff backOff disjoint clockOff chartClock backClock
  let ext := Fin.castAddEmb (n := T) (24+space)
  let innerCaller := (caller.trans ext).trans place
  obtain ⟨setup,setupRate,prepare⟩ := parentStageChartCallers installed archive outerCaller innerCaller
    ((le_max_right ..).trans cap) (fun i j => (archCaller j i).symm)
    (fun i j => (archMid j _).symm) (fun i j => clockOff i _)
  let localCost := fun (w V : ℕ) => (setupRate+base)*V+leaf*LeafCore.coreCost V w+
    ⌈rate*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)⌉₊+⌈C*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊
  refine ⟨setup.seq code,localCost,correctedStageCost_bound _ _ _ _,?_⟩
  intro c w V desc
  obtain ⟨position,coords,execute⟩ := stage c
  refine ⟨position,coords,?_⟩
  intro budget childRate enough time recurse core header W size x u S ready D left cutoff vacant headers
    archiveInput innerEmpty entryFree retFree scratchFree outerEmpty chartFree backFree
  let kids := ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum
  let price := base*V+leaf*LeafCore.coreCost V w+⌈rate*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)⌉₊+kids
  have pos : 0 < W := Nat.mul_pos (c.label ▸ c.stagePositive.2.2.1)
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos c.stagePositive.1 c.stagePositive.2.1) c.stagePositive.2.2.2.1)
      c.stagePositive.2.2.2.2)
  obtain ⟨v,G,m,start,vu,setupCost,outerWords,innerWords,temps,frame⟩ := prepare c u S archiveInput outerEmpty innerEmpty
  have onMid j (outside : ∀ i : Fin 4, ext (caller (i.castAdd 2)) ≠ j) :=
    frame (place j) (fun i => archMid i _) (fun i => clockOff _ _) (fun i => place.injective.ne (outside i))
  have onWorker j := onMid (outer j) (fun i => ext.injective.ne (ca _ j))
  have low j (away : ∀ i, caller i ≠ j) := onMid (ext j) (fun i => ext.injective.ne (away _))
  have high (j : Fin (24+space)) := onMid (j.natAdd T) (fun i eq => by
    have h := congrArg Fin.val eq
    change (caller (i.castAdd 2)).val = T+j.val at h
    have := (caller (i.castAdd 2)).isLt
    omega)
  have readyG : HelperFan (live.trans place) x G := by
    intro i h
    have e := onWorker (inner i)
    simpa only [embStk,Function.comp_apply,live,Function.Embedding.trans_apply,e.1,e.2] using ready i h
  let initial := embStk place G
  obtain ⟨z,F,t,y,exec,user,bill,out,action⟩ := run c.w W pos size price initial (by
    intro rows v E liveE privateE
    have baseOff j (off : ∀ i, fan (i.castAdd 1) ≠ j) :=
      privateE (core j) (fun i eq => off i ((Fin.castAddEmb 37).injective (outer.injective eq)))
    have cut := baseOff (fan (Fin.last k))
      (fun i eq => ne_of_lt i.castSucc_lt_last (fan.injective eq))
    have hi j := privateE (header j) (fun i eq => by
      have val := congrArg Fin.val (outer.injective eq)
      change (fan (i.castAdd 1)).val = H+j.val at val
      have := (fan (i.castAdd 1)).isLt
      omega)
    have extOff j (away : ∀ i, j ≠ mid i) := privateE (j.castAdd (24+space)) (fun i eq =>
      away _ ((Fin.castAddEmb (24+space)).injective eq).symm)
    have keep i := (extOff (caller i) (ca i)).2
    have suffix : (prime^w)^112*W = c.stageWidth := by simp only [W,CutoffNodeInput.stageWidth,w,Nat.mul_assoc]
    have count := innerWords 1
    change G.R (innerCaller 1) = binSyms ((prime^w)^112*W).size ((prime^w)^112*W) at count
    rw [suffix] at count
    obtain ⟨z,F,t,y,exec,user,paid,out,effect⟩ := execute budget childRate enough recurse rows v E liveE
      (cut.1.trans ((onWorker _).1.trans left)) (cut.2.trans ((onWorker _).2.trans cutoff)) (fun j off => by
        have same := baseOff j (fun i => off (i.castAdd 1))
        exact ⟨same.1.trans ((onWorker _).1.trans (vacant j off).1),same.2.trans ((onWorker _).2.trans (vacant j off).2)⟩)
      (fun j => ⟨(hi j).1.trans ((onWorker _).1.trans (headers j).1),(hi j).2.trans ((onWorker _).2.trans (headers j).2)⟩)
      ((keep 0).trans (innerWords 0)) ((keep 1).trans count) ((keep 2).trans (innerWords 2)) ((keep 3).trans (innerWords 3))
      ((keep 4).trans (temps 0).2) ((keep 5).trans (temps 1).2) (fun j ne =>
        ⟨(extOff _ (ea j)).1.trans ((low (entry j) (fun i => (ec j i).symm)).1.trans (entryFree j ne).1),(extOff _ (ea j)).2.trans ((low (entry j) (fun i => (ec j i).symm)).2.trans (entryFree j ne).2)⟩)
      (fun j ne => ⟨(extOff _ (ra j)).1.trans ((low (ret j) (fun i => (rc j i).symm)).1.trans (retFree j ne).1),(extOff _ (ra j)).2.trans ((low (ret j) (fun i => (rc j i).symm)).2.trans (retFree j ne).2)⟩)
      (fun j => by
        have same := privateE (j.natAdd T) (fun i eq => by
          have h := congrArg Fin.val eq
          change (mid (inner i)).val = T+j.val at h
          have := (mid (inner i)).isLt
          omega)
        exact ⟨same.1.trans ((high j).1.trans (scratchFree j).1),same.2.trans ((high j).2.trans (scratchFree j).2)⟩)
    refine ⟨z,F,t,y,exec,paid,user,out,?_⟩
    exact sweepRoles_of_borrowed n w c.B c.stageFactor size rows y effect)

    x v G readyG (fun _ _ => ⟨rfl,rfl⟩) (outerWords 0) (outerWords 1) (outerWords 2) (outerWords 3)
    (temps 0).1 (temps 1).1 (fun j => by
      have e := frame (chart j) (fun i => archChart i j) (fun i => (chartClock j _).symm) (fun i => (chartOff j _).symm)
      exact ⟨e.1.trans (chartFree j).1,e.2.trans (chartFree j).2⟩) (fun j => by
      have e := frame (back j) (fun i => archBack i j) (fun i => (backClock j _).symm) (fun i => (backOff j _).symm)
      exact ⟨e.1.trans (backFree j).1,e.2.trans (backFree j).2⟩)
  refine ⟨z,F,m+t,y,start.seq exec,user.trans vu,?_,out,action⟩
  have stageCost := addChartCharge G F t (base*V+leaf*LeafCore.coreCost V w+
    ⌈rate*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)⌉₊) kids (C*V*(w : ℝ)^M8.Machine.BudgetBound.tau) bill
  have total := setupCost.seq stageCost
  change CleanupBound S F (m+t) (setupRate*V+_) at total
  dsimp only [localCost]
  rw [Nat.add_mul]
  simpa only [Nat.add_assoc] using total

end IntegerMultBounds.MathlibTM2.M6.BitNode
