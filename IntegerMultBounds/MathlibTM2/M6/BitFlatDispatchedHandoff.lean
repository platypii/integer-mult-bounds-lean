module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatDispatchedStage

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout SweepFile
open Shared50ModularControl (prime)

private theorem chartSlice_apart {p q i j N : ℕ} {hi : i+p ≤ N} {hj : j+q ≤ N}
    (order : i+p ≤ j) (x : Fin p) (y : Fin q) : chartSlice i hi x ≠ chartSlice j hj y := by
  intro eq
  have h := congrArg Fin.val eq
  change i+x.val = j+y.val at h
  omega

/-- Only the dispatched caller and the parent archive carry private input.
The materializer receives its own initially blank destination bank. -/
noncomputable def flatWorkerSeed {h N : ℕ} (caller : Fin h ↪ Fin N) (archive : Fin (80+273) ↪ Fin N)
    (initial : Stacks h prime) (c : CutoffNodeInput) : Stacks N prime :=
  let A := parentArchiveSeed c.node c.w
  let install (x : Fin h → List (Fin (prime+4))) (y : Fin (80+273) → List (Fin (prime+4))) :=
    Function.extend caller x (Function.extend archive y (fun _ => []))
  ⟨[],[],install initial.L A.L,install initial.R A.R⟩

private theorem flatWorkerSeed_read {h N : ℕ} (caller : Fin h ↪ Fin N) (archive : Fin (80+273) ↪ Fin N)
    (apart : ∀ i j, archive i ≠ caller j) (initial : Stacks h prime) (c : CutoffNodeInput) :
    let S := flatWorkerSeed caller archive initial c
    (∀ i, S.L (caller i) = initial.L i ∧ S.R (caller i) = initial.R i) ∧
    (∀ i, S.L (archive i) = (parentArchiveSeed c.node c.w).L i ∧ S.R (archive i) = (parentArchiveSeed c.node c.w).R i) ∧
    ∀ j, (∀ i, caller i ≠ j) → (∀ i, archive i ≠ j) → S.L j = [] ∧ S.R j = [] := by
  intro S
  refine ⟨fun i => ?_,fun i => ?_,fun j h g => ?_⟩
  · simp [S,flatWorkerSeed,caller.injective.extend_apply]
  · have away : ¬ ∃ j, caller j = archive i := fun ⟨j,eq⟩ => apart i j eq.symm
    simp [S,flatWorkerSeed,Function.extend,away]
  · simp [S,flatWorkerSeed,Function.extend,show ¬ ∃ i, caller i = j from fun ⟨i,eq⟩ => h i eq,
      show ¬ ∃ i, archive i = j from fun ⟨i,eq⟩ => g i eq]

/-- The cutoff followed by the six parent fields, modulus, unit and unary
atom clock. The same ten words initialize every sweep at this node. -/
noncomputable def sweepSeedWords (c : CutoffNodeInput) : Fin 10 → List (Fin (prime+4)) :=
  Fin.cons (binSyms c.root.width.size c.cutoff) (fun i => (parentArchiveSeed c.node c.w).R (parentArchivePorts i))

private theorem archiveSeedLoadCost (c : CutoffNodeInput) :
    seedLoadBill (fun i => (parentArchiveSeed c.node c.w).R (parentArchivePorts i))+31 ≤
      (133*142080+65)*c.cells := by
  let M := prime^(c.w+1)
  have mass : M ≤ c.cells := (Nat.le_self_pow (by decide : 128 ≠ 0) M).trans
    (Nat.le_mul_of_pos_right _ (Nat.mul_pos c.idlePositive (by decide)))
  have radix : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have size : M.size ≤ c.cells := (Nat.size_le.mpr Nat.lt_two_pow_self).trans mass
  have clock : c.w+1 ≤ c.cells := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le.trans mass
  have pos := radix.trans_le mass
  have volumePos : 0 < volume prime c.node := c.cells_share ▸ Nat.mul_pos pos (by decide)
  have bill := descriptorSeedBill c.node volumePos
  rw [← c.cells_share] at bill
  rw [parentArchiveSeed_bill]
  change _+8*(M.size+1+c.w)+18+31 ≤ _
  omega

private theorem flatWorkerSeed_loader {k H N : ℕ} (fan : Fin (k+1) ↪ Fin H)
    (caller : Fin (H+37) ↪ Fin N) (archive : Fin (80+273) ↪ Fin N) (apart : ∀ i j, archive i ≠ caller j) :
    let initial := fun c : CutoffNodeInput => callerSeed fan (binSyms c.root.width.size c.cutoff)
      (callerHeaderBank (fun i => (Routines.hdr c.node i).map (bitSymbol (a := prime))))
    LoadsPackedSeed sweepSeedWords CutoffNodeInput.cells (fun c => flatWorkerSeed caller archive (initial c) c) := by
  intro initial
  obtain ⟨rate,load⟩ := stageCallerLoader fan
  refine ⟨rate+(133*142080+65),?_⟩
  intro P U t Q body bank source outside
  let fields : Fin 7 → Fin t := Fin.cons (source 0) (fun i : Fin 6 => source ((i.castAdd 3).succ))
  obtain ⟨a,start⟩ := load body (caller.trans bank) fields (by
    intro i j
    induction j using Fin.cases <;> exact outside _ _)
  let A := archive.trans bank
  let src := fun i : Fin 9 => source i.succ
  have regs i : [src i,A (parentArchivePorts i),A 0,A 1].Nodup := by
    have zero := (by decide : ∀ i, parentArchivePorts i ≠ 0) i
    have one := (by decide : ∀ i, parentArchivePorts i ≠ 1) i
    have ext j : src i ≠ A j := (outside _ _).symm
    simp [List.nodup_cons,ext,A.injective.eq_iff,zero,one]
  obtain ⟨b,finish⟩ := loadParentArchiveSeed body A src (A 0) (A 1) (fun i j => outside _ _) regs
  refine ⟨a.seq b,?_⟩
  intro c u S headers vacant
  have field i : S.R (fields i) = Fin.cons (α := fun _ : Fin 7 => List (Fin (prime+4))) (binSyms (A := prime) c.root.width.size c.cutoff)
      (fun j => (Routines.hdr c.node j).map bitSymbol) i := by
    induction i using Fin.cases with
    | zero => exact headers 0
    | succ j =>
      have eq := headers ((j.castAdd 3).succ)
      simpa only [sweepSeedWords,Fin.cons_succ,parentArchiveSeed_words,Fin.addCases_left,fields] using eq
  obtain ⟨v,D,n,exec,user,paid,set,off⟩ := start c u S field (fun i => vacant _)
  have ar j := off (A j) (fun i => bank.injective.ne (apart j i).symm)
  obtain ⟨z,F,m,run,last,bill,stored,frame⟩ := finish c.node c.w v D
    (fun i => (off (src i) (fun j => outside _ _)).2.trans (headers i.succ))
    (fun j => ⟨(ar j).1.trans (vacant _).1,(ar j).2.trans (vacant _).2⟩)
    ((ar 0).2.trans (vacant _).2) ((ar 1).2.trans (vacant _).2)
  obtain ⟨mid,arch,blank⟩ := flatWorkerSeed_read caller archive apart (initial c) c
  refine ⟨z,F,n+m,exec.seq run,last.trans user,?_,?_,?_⟩
  · intro js nd
    apply ((paid.seq bill) js nd).trans
    apply Nat.add_le_add_left
    rw [Nat.add_mul]
    exact Nat.add_le_add_left (archiveSeedLoadCost c) _
  · intro j
    by_cases hit : ∃ i, caller i = j
    · obtain ⟨i,rfl⟩ := hit
      have kept := frame _ (fun l => bank.injective.ne (apart l i))
      exact ⟨kept.1.trans ((set i).1.trans (mid i).1.symm),kept.2.trans ((set i).2.trans (mid i).2.symm)⟩
    by_cases found : ∃ i, archive i = j
    · obtain ⟨i,rfl⟩ := found
      exact ⟨(stored i).1.trans (arch i).1.symm,(stored i).2.trans (arch i).2.symm⟩
    have ca i : caller i ≠ j := fun eq => hit ⟨i,eq⟩
    have aa i : archive i ≠ j := fun eq => found ⟨i,eq⟩
    have first := off (bank j) (fun i => bank.injective.ne (ca i))
    have second := frame (bank j) (fun i => bank.injective.ne (aa i))
    have e := blank j ca aa
    exact ⟨second.1.trans (first.1.trans ((vacant j).1.trans e.1.symm)),
      second.2.trans (first.2.trans ((vacant j).2.trans e.2.symm))⟩
  · intro j away
    have l := off j (fun i => away _)
    have r := frame j (fun i => away _)
    exact ⟨r.1.trans l.1,r.2.trans l.2⟩

private theorem parentInput_congr {node w} {A B : Stacks (80+273) prime} (left : A.L = B.L) (right : A.R = B.R)
    (ready : ParentArchiveInput node w A) : ParentArchiveInput node w B := by
  cases A
  cases B
  dsimp only at left right
  subst_vars
  exact ready

private theorem materializedStageCost [M8.Machine.Net] {cost : ℕ → ℕ → ℕ} (C : ℝ)
    (bound : ∀ w V : ℕ, 0 < w → 0 < V → (cost w V : ℝ) ≤ C*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)) :
    ∃ D : ℝ, ∀ w V : ℕ, 0 < w → 0 < V → ((cost w V+(142081*(10*V+10)+1) : ℕ) : ℝ) ≤
      D*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau) := by
  refine ⟨C+142081*20+1,?_⟩
  intro w V hw hv
  have power : 1 ≤ (w : ℝ)^M8.Machine.BudgetBound.tau := Real.one_le_rpow (by exact_mod_cast hw)
    M8.Machine.BudgetBound.exponent_range.1.le
  have scale := le_mul_of_one_le_right (Nat.cast_nonneg V (α := ℝ)) power
  have positive : (1 : ℝ) ≤ V := by exact_mod_cast hv
  push_cast
  linarith only [scale,positive,bound w V hw hv]

theorem flatDispatchedHandoff [M8.Machine.Net] (n : Fin 9) :
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
    ∃ seed : CutoffNodeInput → Stacks T prime, LoadsPackedSeed sweepSeedWords CutoffNodeInput.cells seed ∧
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
    PackedPieceHandoffWithCharge cleanupWeight V (fun x y => ∀ j : Fin W,
      let address := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
      readRoles address y = (Piece.stage n).run (readRoles address x)) host code src dst (seed c)
      (localCost w V+((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum) := by
  classical
  intro l r I k
  obtain ⟨pre,post,ts,states,ports,leafRate,a,b,build⟩ := flatDispatchedStage n
  refine ⟨pre,post,ts,states,ports,leafRate,?_⟩
  intro P U Q cap large f
  obtain ⟨body,active,H,fan,space,table,stage⟩ := build cap large f
  let J := rowSwapBlock.tapes+35
  let T := H+37+J+J+6
  let mid : Fin (H+37) ↪ Fin T := chartSlice 0 (by dsimp [T]; omega)
  let entry : Fin J ↪ Fin T := chartSlice (H+37) (by dsimp [T]; omega)
  let ret : Fin J ↪ Fin T := chartSlice (H+37+J) (by dsimp [T]; omega)
  let caller : Fin 6 ↪ Fin T := chartSlice (H+37+J+J) (by dsimp [T]; omega)
  let outer := mid.trans (Fin.castAddEmb (24+space))
  let L := T+(24+space)
  let N := L+(J+a)+b+6+(80+273)
  let place : Fin L ↪ Fin N := chartSlice 0 (by dsimp [N]; omega)
  let chart : Fin (J+a) ↪ Fin N := chartSlice L (by dsimp [N]; omega)
  let back : Fin b ↪ Fin N := chartSlice (L+(J+a)) (by dsimp [N]; omega)
  let ext : Fin 6 ↪ Fin N := chartSlice (L+(J+a)+b) (by dsimp [N]; omega)
  let archive : Fin (80+273) ↪ Fin N := chartSlice (L+(J+a)+b+6) (by dsimp [N]; omega)
  have ea i j : entry i ≠ mid j := (chartSlice_apart (by omega) j i).symm
  have ra i j : ret i ≠ mid j := (chartSlice_apart (by omega) j i).symm
  have ca i j : caller i ≠ mid j := (chartSlice_apart (by omega) j i).symm
  have cp i j : chart i ≠ place j := (chartSlice_apart (by omega) j i).symm
  have bp i j : back i ≠ place j := (chartSlice_apart (by omega) j i).symm
  have ep i j : ext i ≠ place j := (chartSlice_apart (by omega) j i).symm
  have ap i j : archive i ≠ place j := (chartSlice_apart (by omega) j i).symm
  have ac i j : archive i ≠ chart j := (chartSlice_apart (by omega) j i).symm
  have ab i j : archive i ≠ back j := (chartSlice_apart (by omega) j i).symm
  have ae i j : archive i ≠ ext j := (chartSlice_apart (by omega) j i).symm
  obtain ⟨worker,cost,⟨C,bound⟩,run⟩ := stage mid entry ret caller ea ra ca
    (fun i j => chartSlice_apart (by omega) i j) (fun i j => chartSlice_apart (by omega) i j)
    (fun i j => (chartSlice_apart (by omega) j i).symm) place chart back ext cp bp
    (fun i j => (chartSlice_apart (by omega) j i).symm) ep (fun i j => chartSlice_apart (by omega) i j)
    (fun i j => chartSlice_apart (by omega) i j) archive ap ae ac ab
  let inner := (Fin.castAddEmb 1 (n := k)).trans (fan.trans (Fin.castAddEmb 37))
  let data := outer.trans place
  let live := inner.trans data
  let host := fun f => embProg place id (embProg outer id (table f))
  let initial := fun c : CutoffNodeInput => callerSeed fan (binSyms c.root.width.size c.cutoff)
    (callerHeaderBank (fun i => (Routines.hdr c.node i).map (bitSymbol (a := prime))))
  let seed := fun c => flatWorkerSeed data archive (initial c) c
  obtain ⟨code,pack⟩ := flatWordStageWithSeedCharge live host worker
  refine ⟨body,active,_,live.trans (Exit.chart 0 N),returnedFan live,(fun f => embProg (Exit.chart 0 N) id (host f)),code,
    (fun w V => cost w V+(142081*(10*V+10)+1)),fun c => flatStageSeed (seed c),
    (flatWorkerSeed_loader fan data archive (fun i j => ap i _)).flatStage,materializedStageCost C bound,?_⟩
  intro c w V desc
  obtain ⟨position,coords,execute⟩ := run c
  refine ⟨position,coords,?_⟩
  intro budget rate enough time recurse W size
  let kids := ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum
  have price : cost w V+(142081*(10*V+10)+1)+kids = cost w V+kids+(142081*(10*V+10)+1) := by omega
  rw [price]
  apply pack (seed c)
  intro x u S words fresh
  obtain ⟨dataRead,archiveRead,other⟩ := flatWorkerSeed_read data archive (fun i j => ap i _) (initial c) c
  have privateData j (away : ∀ i, inner i ≠ j) := fresh (data j) (fun i => data.injective.ne (away i))
  have privateArchive j := fresh (archive j) (fun i => (ap j _).symm)
  have blank j (offData : ∀ i, data i ≠ j) (offArchive : ∀ i, archive i ≠ j) := by
    have e := fresh j (fun i => offData (inner i))
    exact And.intro (e.1.trans (other j offData offArchive).1) (e.2.trans (other j offData offArchive).2)
  have base j (off : ∀ i : Fin k, fan (i.castAdd 1) ≠ j) :=
    privateData (j.castAdd 37) (fun i eq => off i ((Fin.castAddEmb 37).injective eq))
  have cut := base (fan (Fin.last k)) (fun i eq => ne_of_lt i.castSucc_lt_last (fan.injective eq))
  have extWords (j : Fin 37) := privateData (j.natAdd H) (fun i eq => by
    have h := congrArg Fin.val eq
    change (fan (i.castAdd 1)).val = H+j.val at h
    have := (fan (i.castAdd 1)).isLt
    omega)
  have low j (off : ∀ i, mid i ≠ j) := blank (place (j.castAdd (24+space)))
    (fun i => place.injective.ne ((Fin.castAddEmb (24+space)).injective.ne (off i))) (fun i => ap i _)
  have high (j : Fin (24+space)) := blank (place (j.natAdd T)) (fun i eq => by
    have h := congrArg Fin.val (place.injective eq)
    change (mid i).val = T+j.val at h
    have := (mid i).isLt
    omega) (fun i => ap i _)
  have arL : (embStk archive S).L = (parentArchiveSeed c.node c.w).L :=
    funext fun i => (privateArchive i).1.trans (archiveRead i).1
  have arR : (embStk archive S).R = (parentArchiveSeed c.node c.w).R :=
    funext fun i => (privateArchive i).2.trans (archiveRead i).2
  have readyArchive : ParentArchiveInput c.node c.w (embStk archive S) :=
    parentInput_congr arL.symm arR.symm (parentArchiveSeed_ready c.node c.w)
  obtain ⟨z,F,t,y,exec,user,paid,out,action⟩ := execute budget rate enough recurse x u S words.helperFan
    (cut.1.trans (dataRead _).1) (by
      have h := cut.2.trans (dataRead _).2
      change S.R (data ((fan (Fin.last k)).castAdd 37)) = _
      simpa only [k,initial,callerSeed,Fin.append_left,Function.update_self] using h)
    (fun j off => by
      have e := base j (fun i => off (i.castAdd 1))
      have g := dataRead (j.castAdd 37)
      exact ⟨e.1.trans g.1,by
        change S.R (data (j.castAdd 37)) = []
        simpa only [initial,callerSeed,Fin.append_left,Function.update_of_ne (off _).symm] using e.2.trans g.2⟩)
    (fun j => by
      have e := extWords j
      have g := dataRead (j.natAdd H)
      exact ⟨e.1.trans g.1,by
        change S.R (data (j.natAdd H)) = _
        simpa only [initial,callerSeed,Fin.append_right] using e.2.trans g.2⟩)
    readyArchive (fun i => (low _ (fun j => (ca i j).symm)).2)
    (fun i _ => low _ (fun j => (ea i j).symm)) (fun i _ => low _ (fun j => (ra i j).symm)) high
    (fun i => (blank _ (fun j => (ep i _).symm) (fun j => ae j i)).2)
    (fun i => blank _ (fun j => (cp i _).symm) (fun j => ac j i))
    (fun i => blank _ (fun j => (bp i _).symm) (fun j => ab j i))
  exact ⟨z,F,t,y,exec,paid,user,out,action⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
