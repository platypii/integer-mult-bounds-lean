module

public import IntegerMultBounds.MathlibTM2.M6.BitCutoffStage
public import IntegerMultBounds.MathlibTM2.M6.BitAlignedNodeBill
public import IntegerMultBounds.MathlibTM2.M6.BitIdleDispatchSeed

/-! Assemble the cutoff stages and idle remainders in the same packed word order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Certificates.PR589 IntervalDescriptor RecursiveInterchangeLayout
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Runtime data shared by the nine stage and remainder pairs at an active node. -/
structure CutoffNodeInput where
  root : Descriptor
  path : List (Fin nodeChildren5.length)
  depth : ℕ
  b : ℕ
  cutoff : ℕ
  w : ℕ
  groups : ℕ
  B : ℕ
  levels : 0 < depth
  base : 0 < b
  rootWidth : root.width = 64^depth*b
  stop : 42^depth*b ≤ cutoff
  active : cutoff ≤ (path.foldl (scheduledChild prime) root).width
  width : (path.foldl (scheduledChild prime) root).width = 64*(w+1)
  rows : (path.foldl (scheduledChild prime) root).rows = 142080*(142080*groups)
  label : (path.foldl (scheduledChild prime) root).beforeH = B*prime^(64*((w+1)*64))
  positive : ({path.foldl (scheduledChild prime) root with rows := groups} : Descriptor).Positive

namespace CutoffNodeInput
noncomputable abbrev node (c : CutoffNodeInput) := c.path.foldl (scheduledChild prime) c.root
def rowsPerStage (c : CutoffNodeInput) := 142080*c.groups
noncomputable def idleWidth (c : CutoffNodeInput) :=
  c.node.beforeRows*c.groups*c.node.beforeH*c.node.between*c.node.afterD
noncomputable def stageFactor (c : CutoffNodeInput) :=
  c.node.beforeRows*c.rowsPerStage*c.node.between*c.node.afterD
noncomputable def stageWidth (c : CutoffNodeInput) :=
  ((prime^(c.w+1))^112*c.B)*prime^(64*((c.w+1)*64))*c.stageFactor
noncomputable def cells (c : CutoffNodeInput) := (prime^(c.w+1))^128*(c.idleWidth*142080)

theorem idlePositive (c : CutoffNodeInput) : 0 < c.idleWidth :=
  Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos c.positive.1 c.positive.2.1) c.positive.2.2.1)
    c.positive.2.2.2.1) c.positive.2.2.2.2

theorem stagePositive (c : CutoffNodeInput) :
    ({c.node with rows := c.rowsPerStage} : Descriptor).Positive :=
  ⟨c.positive.1,Nat.mul_pos (by decide) c.positive.2.1,c.positive.2.2⟩

theorem stageTail (c : CutoffNodeInput) :
    c.B*prime^(64*((c.w+1)*64))*c.stageFactor = c.idleWidth*142080 := by
  unfold idleWidth stageFactor rowsPerStage
  rw [← c.label]
  ring

theorem stageCells (c : CutoffNodeInput) : (prime^(c.w+1))^16*c.stageWidth = c.cells := by
  rw [cells,← c.stageTail,← ordinaryCompact_width]
  simp [stageWidth,Nat.mul_assoc]

theorem cells_share (c : CutoffNodeInput) : c.cells*142080 = volume prime c.node := by
  unfold cells idleWidth volume
  rw [c.rows,c.width,← pow_mul]
  rw [show (c.w+1)*128 = 64*(c.w+1)+64*(c.w+1) by omega,pow_add]
  ring

noncomputable def localCharge (c : CutoffNodeInput) (work : Fin 9 → ℕ → ℕ → ℕ) (assemble : ℕ) : ℕ :=
  (∑ n, work n c.w c.cells)+9*(1+(142081*(10*c.cells+10)+1))+5*volume prime c.node+assemble*c.cells+2

/-- The nine local stage bounds and the linear assembly cost share a uniform
coefficient. The scale is expressed in the parent's volume and width. -/
theorem localCharge_bound [M8.Machine.Net] (work : Fin 9 → ℕ → ℕ → ℕ) (assemble : ℕ)
    (localBound : ∀ n, ∃ D : ℝ, ∀ w V : ℕ, 0 < V →
      (work n w V : ℝ) ≤ D*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)) :
    ∃ C : ℝ, ∀ c : CutoffNodeInput, (c.localCharge work assemble : ℝ) ≤
      C*((volume prime c.node : ℝ)*(c.node.width : ℝ)^M8.Machine.BudgetBound.tau) := by
  classical
  choose D bound using localBound
  refine ⟨(∑ n, |D n|)+9*(2+142081*20)+5+assemble+2,?_⟩
  intro c
  have hc : 0 < c.cells := by
    have := c.idlePositive
    have := Shared50ModularControl.prime_prime.pos
    unfold cells
    positivity
  have share := c.cells_share
  have leVol : (c.cells : ℝ) ≤ volume prime c.node := by exact_mod_cast (by omega : c.cells ≤ volume prime c.node)
  let scale := (volume prime c.node : ℝ)*(c.node.width : ℝ)^M8.Machine.BudgetBound.tau
  have width : c.w+1 ≤ c.node.width := by rw [c.width]; omega
  have one : 1 ≤ (c.node.width : ℝ)^M8.Machine.BudgetBound.tau :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ c.node.width)) M8.Machine.BudgetBound.exponent_range.1.le
  have vol : (volume prime c.node : ℝ) ≤ scale := le_mul_of_one_le_right (by positivity) one
  have cellsLe := leVol.trans vol
  have unit : 1 ≤ scale := (show (1 : ℝ) ≤ c.cells by exact_mod_cast hc).trans cellsLe
  have stages : (∑ n, (work n c.w c.cells : ℝ)) ≤ (∑ n, |D n|)*scale := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro n _
    apply (bound n c.w c.cells hc).trans
    apply mul_le_mul (le_abs_self _) _ (by positivity) (abs_nonneg _)
    exact mul_le_mul leVol (Real.rpow_le_rpow (by positivity) (by exact_mod_cast width)
      M8.Machine.BudgetBound.exponent_range.1.le) (by positivity) (by positivity)
  unfold localCharge
  push_cast
  change _ ≤ _*scale
  linarith only [stages,cellsLe,unit,vol,mul_le_mul_of_nonneg_left cellsLe (Nat.cast_nonneg assemble : (0:ℝ) ≤ assemble)]

end CutoffNodeInput

private theorem stageCast {P U : Type} {T Q w W V Z price : ℕ} (n : Fin 9)
    (tailEq : W = Z) (size : (prime^w)^128*W = V) (work : ℕ → ℕ)
    {body : P → Pr P T Q prime U} {code src dst seed}
    (run : PackedPieceHandoffWithCharge cleanupWeight V (fun x y => ∀ j : Fin W,
      let addr := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
      readRoles addr y = (Piece.stage n).run (readRoles addr x)) body code src dst seed (work V+price)) :
    PackedPieceHandoffWithCharge cleanupWeight ((prime^w)^128*Z) (fun x y => ∀ j : Fin Z,
      let addr := fun z => flatWindowEquiv w Z (windowState w z,j)
      readRoles addr y = (Piece.stage n).run (readRoles addr x)) body code src dst seed (work ((prime^w)^128*Z)+price) := by
  subst Z V
  exact run

/-- A single program transposes the packed words over the whole family of
active nodes. Only recursive executions on above-cutoff children are supplied. -/
def CutoffNodeExecution [M8.Machine.Net] (P U Config : Type) : Prop :=
    let l := (phaseMoveBlocks (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)).1.length
    let r := (phaseMoveBlocks (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter)).1.length
    let count := invocationCounts l r
    ∃ (pre : Fin 9 → StageRun → Fin l → MoveIndex) (post : Fin 9 → StageRun → Fin r → MoveIndex),
    (∀ n p i, (pre n p i).val = i.val) ∧ (∀ n p i, (post n p i).val = l+i.val) ∧
    let child := fun n p => invocationChildren n p (pre n p) (post n p)
    ∃ (ts : Fin 9 → StageRun → ∀ j, Fin (count j) → ℕ)
      (ports : ∀ n p j i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts n p j i))
      (states : ℕ), ∀ {Q : ℕ}, states ≤ Q →
    ∃ (N : ℕ) (leafRate : ℝ), ∀
      (large : ∀ n p j i, P → Pr (WorkerLabel P) (ts n p j i) Q prime U)
      (entry : Fin 9 → StageRun → ∀ j, Fin (count j) → P)
      (idleLarge : P → Pr (Unit ⊕ P) (72+N) Q prime U) (idleEntry : Fin 9 → P),
    ∃ (body : ∀ n p j i, WorkerLabel P → Pr (WorkerLabel P) (ts n p j i) Q prime U)
      (idleBody : Unit ⊕ P → Pr (Unit ⊕ P) (72+N) Q prime U),
    (∀ n p j i g, body n p j i (.active g) = large n p j i g) ∧
    (∀ g, idleBody (.inr g) = idleLarge g) ∧
    ∃ (localWork : Fin 9 → ℕ → ℕ → ℕ) (assemblyRate : ℕ),
    (∃ C : ℝ, ∀ v : CutoffNodeInput, (v.localCharge localWork assemblyRate : ℝ) ≤
      C*((volume prime v.node : ℝ)*(v.node.width : ℝ)^M8.Machine.BudgetBound.tau)) ∧
    ∀ (input : Config → CutoffNodeInput),
    let d := fun c n p j i => scheduledChild prime (input c).node (child n p j i)
    ∃ position : ∀ c n p j i, Fin (volume prime (d c n p j i)) ≃ Fin ((prime^((input c).w+1))^16*(input c).stageWidth),
    (∀ c n p j i, invocationCoordinates j ((input c).w+1) (input c).stageWidth (position c n p j i)) ∧
    ∀ (budget : Config → ℕ → ℕ) (rate : ℝ), leafRate ≤ rate →
    (∀ c n p j i, let v := input c
      let k := child n p j i
      let h := d c n p j i
      v.cutoff < h.width → h.width < v.node.width →
      if j = 1 then ScheduledChildExec v.node h v.w v.stageWidth (ports n p j i)
        (binSyms v.root.width.size v.cutoff) (position c n p j i) (body n p j i) (.active (entry n p j i)) (budget c k.val) true
      else MoveOnBankExec v.node h v.w v.stageWidth (movePrefix.trans (ports n p j i))
        (binSyms v.root.width.size v.cutoff) (position c n p j i) (body n p j i)
        (large n p j i (entry n p j i)) (budget c k.val) true) →
    (∀ c n (j : Fin idleCopies.length), let v := input c
      let k := idleDirectoryIndex (n,j)
      let e := idleInterval n idleCopies[j.val].2
      v.cutoff < (scheduledChild prime v.node k).width →
      IntervalWorkerExec idleBody (.inr (idleEntry n)) (phaseIntervalChild (e.1+1) (e.2+1) (v.w+1) v.idleWidth 64)
        (v.w+1) v.idleWidth (budget c k.val)) →
    ∃ (R : Type) (T : ℕ) (host : R → Pr R T Q prime U) (code : Pr R T Q prime U)
      (src dst : Fin (142081+2) ↪ Fin T) (seed : Config → Stacks T prime),
    ∀ (c : Config), let v := input c
      PackedPieceHandoffWithCharge cleanupWeight v.cells (packedChildOutput (v.w+1) v.cells)
        host code src dst (seed c) (v.localCharge localWork assemblyRate+
          ∑ k : Fin nodeChildren5.length, stageBranchTime v.node v.cutoff rate (budget c) k.val)

theorem selectedCutoffNode [M8.Machine.Net] (P U Config : Type) : CutoffNodeExecution P U Config := by
  classical
  unfold CutoffNodeExecution
  intro l r count
  have stages := selectedCutoffStage P U
  dsimp only at stages
  choose pre post first last ts ports states rates build using stages
  obtain ⟨q,assemble⟩ := assembledFlatNodeFamily (U := U) (Config := Config)
  let merge := 7+(CyclicRowCycle.states 142080+5)+4
  refine ⟨pre,post,first,last,ts,ports,max (Finset.univ.sup states) (max q (max columnCapacity (merge+merge))),?_⟩
  intro Q cap
  have room := (le_max_right _ _).trans cap
  have idleRoom := (le_max_right _ _).trans room
  obtain ⟨cost,N,leaf,_,idle⟩ := dispatchedRemainder (U := U) ((le_max_left _ _).trans idleRoom) ((le_max_right _ _).trans idleRoom)
  refine ⟨N,max cost (Finset.univ.sup' Finset.univ_nonempty rates),?_⟩
  intro large entry idleLarge idleEntry
  let idleBody : Unit ⊕ P → Pr (Unit ⊕ P) (72+N) Q prime U :=
    Sum.elim (fun f => embProg (Function.Embedding.refl _) Sum.inl (leaf f)) idleLarge
  choose body active tapes src dst hosts code localWork localBound sweep using fun n =>
    build n ((Finset.le_sup (Finset.mem_univ n)).trans ((le_max_left _ _).trans cap)) (large n) (entry n)
  obtain ⟨assemblyRate,join⟩ := assemble ((le_max_left _ _).trans room)
  refine ⟨body,idleBody,active,fun _ => rfl,localWork,assemblyRate,CutoffNodeInput.localCharge_bound _ _ localBound,?_⟩
  intro input d
  choose positions coords runSweep using fun c n => sweep n (input c).node (input c).w (input c).B
    (input c).rowsPerStage (input c).width (input c).rows (input c).label (input c).stagePositive
  refine ⟨positions,coords,?_⟩
  intro budget rate enough stageRec idleRec
  let time := fun c => stageBranchTime (input c).node (input c).cutoff rate (budget c)
  let work := fun c n => localWork n (input c).w (input c).cells
  let stagePrice := fun c n => work c n+((List.range' (stageChildStart n)
    (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map (time c)).sum
  let dispatch := fun c (k : Fin nodeChildren5.length) =>
    let v := input c
    let h := scheduledChild prime v.node k
    2*volume prime h + if v.cutoff < h.width then budget c k.val else
      ⌊cost*(h.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime h⌋₊
  let extra := fun c => 1+(142081*(10*(input c).cells+10)+1)
  let remainder := fun c (n : Fin 9) => (∑ j : Fin idleCopies.length, dispatch c (idleDirectoryIndex (n,j)))+extra c
  have positive c : 0 < (input c).cells := by
    have hp := Shared50ModularControl.prime_prime.pos
    have h := (input c).idlePositive
    unfold CutoffNodeInput.cells
    positivity
  obtain ⟨R,T,host,program,src',dst',seed,exec⟩ := join (fun c => (input c).w+1) (fun c => (input c).idleWidth*142080)
    (fun c => (input c).cells) (fun _ => rfl) positive (fun _ => Equiv.refl _) stagePrice remainder (by
      intro n
      have stage c := runSweep c n (input c).root (input c).path (input c).depth (input c).b (input c).cutoff
        (budget c) rate ((Finset.le_sup' rates (Finset.mem_univ n)).trans ((le_max_right _ _).trans enough)) rfl
        (input c).levels (input c).base (input c).rootWidth (input c).stop (input c).active (stageRec c n)
      choose initial run using stage
      refine ⟨_,tapes n,hosts n,code n,src n,dst n,initial,?_⟩
      intro c
      exact stageCast n (input c).stageTail _ (localWork n (input c).w) (run c)) (by
      intro n
      obtain ⟨H,S,table,program,src,dst,step⟩ := idle idleBody Sum.inl (fun _ => rfl) n (.inr (idleEntry n))
      have prepared c := step (input c).root (input c).path (input c).depth (input c).b (input c).cutoff
        (input c).w (input c).groups (input c).levels (input c).base (input c).rootWidth (input c).stop
        (input c).active (input c).width (input c).rows (input c).idlePositive (fun k => budget c k.val) (idleRec c n)
      choose initial run using prepared
      refine ⟨S,H,table,program,src,dst,initial,?_⟩
      intro c
      have h := run c
      rw [Nat.add_assoc _ 1] at h
      exact h)
  refine ⟨R,T,host,program,src',dst',seed,?_⟩
  intro c v x u S words fresh
  obtain ⟨z,F,t,y,step,paid,user,out,sem⟩ := exec c x u S words fresh
  refine ⟨z,F,t,y,step,?_,user,out,sem⟩
  intro js unique
  have calls n j : dispatch c (idleDirectoryIndex (n,j)) ≤ 2*volume prime (scheduledChild prime (input c).node (idleDirectoryIndex (n,j)))+
      time c (idleDirectoryIndex (n,j)).val := by
    let k := idleDirectoryIndex (n,j)
    change dispatch c k ≤ 2*volume prime (scheduledChild prime (input c).node k)+time c k.val
    simp only [dispatch,time,stageBranchTime,dite_eq_left k.isLt]
    apply Nat.add_le_add_left
    split
    · rfl
    · apply Nat.floor_mono
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans enough) (by positivity)) (by positivity)
  have bill := alignedNodeDirectoryBill (input c).node ⟨_,(input c).width⟩ ⟨_,(input c).rows⟩ (time c)
    (stagePrice c) (remainder c) (work c) (fun _ => extra c) (fun n j => dispatch c (idleDirectoryIndex (n,j)))
    (fun _ => le_rfl) (fun _ => (Nat.add_comm _ _).le) calls
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at bill
  have h := paid js unique
  change _ ≤ _+((∑ n, work c n)+9*extra c+5*volume prime (input c).node+assemblyRate*(input c).cells+2+∑ k : Fin nodeChildren5.length, time c k.val)
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
