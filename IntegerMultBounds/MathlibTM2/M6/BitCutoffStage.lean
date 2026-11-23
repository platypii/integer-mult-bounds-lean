module

public import IntegerMultBounds.MathlibTM2.M6.BitCutoffInvocation
public import IntegerMultBounds.MathlibTM2.M6.BitChargedChartWorker

/-! Run the selected cutoff invocations together on the stage owner bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host
open Certificates.PR589 RecursiveInterchangeLayout M8.RevMachine
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- The stopped or recursive budget at a scheduled index of an active node. -/
noncomputable def stageBranchTime [M8.Machine.Net] (node : Descriptor) (cutoff : ℕ) (rate : ℝ)
    (budget : ℕ → ℕ) (i : ℕ) : ℕ :=
  if h : i < nodeChildren5.length then
    let d := scheduledChild prime node ⟨i,h⟩
    if cutoff < d.width then budget i else ⌊rate*(d.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime d⌋₊
  else 0

/-- One fixed stage program runs all selected invocations. Its charged bill
contains the contiguous stage child directory plus local work. -/
theorem selectedCutoffStage [M8.Machine.Net] (P U : Type) (n : Fin 9) :
    let l := (phaseMoveBlocks (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)).1.length
    let r := (phaseMoveBlocks (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter)).1.length
    let count := invocationCounts l r
    ∃ (pre : StageRun → Fin l → MoveIndex) (post : StageRun → Fin r → MoveIndex),
    (∀ p i, (pre p i).val = i.val) ∧ (∀ p i, (post p i).val = l+i.val) ∧
    let child := fun p => invocationChildren n p (pre p) (post p)
    ∃ (ts : StageRun → ∀ j, Fin (count j) → ℕ)
      (ports : ∀ p j i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts p j i))
      (states : ℕ) (leafRate : ℝ), ∀ {Q : ℕ}, states ≤ Q →
    ∀ (large : ∀ p j i, P → Pr (WorkerLabel P) (ts p j i) Q prime U)
      (f : StageRun → ∀ j, Fin (count j) → P),
    ∃ body : ∀ p j i, WorkerLabel P → Pr (WorkerLabel P) (ts p j i) Q prime U,
    (∀ p j i g, body p j i (.active g) = large p j i g) ∧
    ∃ (T : ℕ) (src dst : Fin (142081+2) ↪ Fin T)
      (host : ((_ : StageRun) × (Σ j, Fin (count j) × WorkerLabel P)) → Pr ((_ : StageRun) × (Σ j, Fin (count j) × WorkerLabel P)) T Q prime U)
      (code : Pr ((_ : StageRun) × (Σ j, Fin (count j) × WorkerLabel P)) T Q prime U)
      (localWork : ℕ → ℕ → ℕ),
    (∃ D : ℝ, ∀ w V : ℕ, 0 < V → (localWork w V : ℝ) ≤ D*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)) ∧
    ∀ (node : Descriptor) (w B rows : ℕ), node.width = 64*(w+1) → node.rows = 142080*rows →
    node.beforeH = B*prime^(64*((w+1)*64)) →
    let K := node.beforeRows*rows*node.between*node.afterD
    let W := ((prime^(w+1))^112*B)*prime^(64*((w+1)*64))*K
    let V := (prime^(w+1))^16*W
    let desc := fun p j i => scheduledChild prime node (child p j i)
    ({node with rows := rows} : Descriptor).Positive →
    ∃ position : ∀ p j i, Fin (volume prime (desc p j i)) ≃ Fin V,
    (∀ p j i, invocationCoordinates j (w+1) W (position p j i)) ∧
    ∀ (root : Descriptor) (path : List (Fin nodeChildren5.length)) (depth b cutoff : ℕ)
      (budget : ℕ → ℕ) (rate : ℝ), leafRate ≤ rate →
    node = path.foldl (scheduledChild prime) root → 0 < depth → 0 < b →
    root.width = 64^depth*b → 42^depth*b ≤ cutoff → cutoff ≤ node.width →
    let L := root.width.size
    (∀ p j i, let d := desc p j i
      cutoff < d.width → d.width < node.width →
      if j = 1 then ScheduledChildExec node d w W (ports p j i) (binSyms L cutoff) (position p j i)
        (body p j i) (.active (f p j i)) (budget (child p j i).val) true
      else MoveOnBankExec node d w W (movePrefix.trans (ports p j i)) (binSyms L cutoff) (position p j i)
        (body p j i) (large p j i (f p j i)) (budget (child p j i).val) true) →
    let tailWidth := B*prime^(64*((w+1)*64))*K
    let size : (prime^(w+1))^128*tailWidth = V :=
      (ordinaryCompact_width _ _).symm.trans (by simp [V,W,tailWidth,Nat.mul_assoc])
    ∃ seed, PackedPieceHandoffWithCharge cleanupWeight V (fun x y => ∀ j : Fin tailWidth,
      let address := fun z => (flatWindowEquiv (w+1) tailWidth (windowState (w+1) z,j)).cast size
      readRoles address y = (Piece.stage n).run (readRoles address x)) host code src dst seed
      (localWork w V+((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map
        (stageBranchTime node cutoff rate budget)).sum) := by
  classical
  intro l r count
  have inv := selectedCutoffInvocation P U n
  dsimp only at inv
  choose pre post first last ts ports states rates build using inv
  let headers := (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080)
  obtain ⟨C,base,extra,chartStates,chart⟩ := borrowedFlatHandoffWithCharge
  refine ⟨pre,post,first,last,ts,ports,max (Finset.univ.sup states) (max (max columnCapacity headers) chartStates),
    Finset.univ.sup' Finset.univ_nonempty rates,?_⟩
  intro Q cap large f
  choose body active tapes fans cuts hosts calls a b c costs step using fun p =>
    build p ((Finset.le_sup (Finset.mem_univ p)).trans ((le_max_left _ _).trans cap)) (large p) (f p)
  obtain ⟨T,fan,banks,assemble⟩ := parentArchiveSweepWithCharge n tapes fans
  have room := (le_max_right _ _).trans cap
  have archiveRoom := (le_max_left _ _).trans room
  obtain ⟨setup,runRate,compile⟩ := assemble ((le_max_left _ _).trans archiveRoom) ((le_max_right _ _).trans archiveRoom) hosts
  obtain ⟨program,run⟩ := compile calls
  let work := fun w V p => (a p+b p*swapVolumeRate w)*V+c p
  let scale := fun (w V : ℕ) => (V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  let total := fun w V => setup*V+⌈runRate*scale w V⌉₊+(stageRuns.map (work w V)).sum
  let owner := (Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)
  let stage := Fin.natAddEmb 80 (m := T+273+LeafCore.small)
  let table := fun label : (p : StageRun) × (Σ j, Fin (count j) × WorkerLabel P) =>
    embProg stage id (embProg owner id (embProg (banks label.1) (Sigma.mk (β := fun _ : StageRun => Σ j, Fin (count j) × WorkerLabel P) label.1) (hosts label.1 label.2)))
  let liveFan := (fan.trans owner).trans stage
  obtain ⟨_,host,code,src,dst,pack⟩ := chart n liveFan table program ((le_max_right _ _).trans room)
  let correction := fun w V => 13*((base*V+17760*(2*LeafCore.coreCost V (w+1)+14))*(extra+5)+12)
    +⌈C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau⌉₊+(142081*(10*V+10)+1)
  refine ⟨body,active,_,src,dst,host,code,(fun w V => total w V+correction w V),?_,?_⟩
  · choose coeff bound using costs
    let factor := 13*((base+17760*(2 * |LeafCore.C|+14))*(extra+5:ℕ)+12)+|C|+1+(142081*20+1)
    refine ⟨setup+|runRate|+1+(stageRuns.map coeff).sum+factor,?_⟩
    intro w V hv
    have one : 1 ≤ ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau :=
      Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w) M8.Machine.BudgetBound.exponent_range.1.le
    have vol : (V : ℝ) ≤ scale w V := le_mul_of_one_le_right (by positivity) one
    have hs : 1 ≤ scale w V := (show (1 : ℝ) ≤ V by exact_mod_cast hv).trans vol
    have ceilBound : (⌈runRate*scale w V⌉₊ : ℝ) ≤ |runRate| *scale w V+1 := by
      have m := Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_abs_self runRate) (zero_le_one.trans hs))
      exact (Nat.cast_le.mpr m).trans (Nat.ceil_lt_add_one (mul_nonneg (abs_nonneg _) (zero_le_one.trans hs))).le
    have sumBound (ps : List StageRun) : ((ps.map (work w V)).sum : ℝ) ≤ (ps.map coeff).sum*scale w V := by
      induction ps with
      | nil => simp
      | cons p ps ih =>
        simp only [List.map_cons,List.sum_cons,Nat.cast_add,add_mul]
        exact add_le_add (bound p w V hv) ih
    have sweep : (total w V : ℝ) ≤ (setup+|runRate|+1+(stageRuns.map coeff).sum)*scale w V := by
      dsimp only [total]
      rw [Nat.cast_add,Nat.cast_add,Nat.cast_mul]
      linarith only [mul_le_mul_of_nonneg_left vol (Nat.cast_nonneg setup : (0 : ℝ) ≤ setup),ceilBound,hs,sumBound stageRuns]
    have core := RevBudget.coreCost_le V (w+1) (L := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)
      (by rw [max_eq_right (by omega : 1 ≤ w+1)])
    have coreBound : (LeafCore.coreCost V (w+1) : ℝ) ≤ |LeafCore.C| * scale w V := by simpa only [scale,mul_assoc] using core
    have rounded : (⌈C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau⌉₊ : ℝ) ≤ (|C|+1)*scale w V := by
      rw [mul_assoc]
      have up := Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_abs_self C) (zero_le_one.trans hs))
      have h := (Nat.cast_le.mpr up : (⌈C*scale w V⌉₊ : ℝ) ≤ _).trans
        (Nat.ceil_lt_add_one (mul_nonneg (abs_nonneg C) (zero_le_one.trans hs))).le
      linarith only [h,hs]
    have chartBound : (correction w V : ℝ) ≤ factor*scale w V := by
      dsimp only [correction,factor]
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      have inner : (base:ℝ)*V+17760*(2*(LeafCore.coreCost V (w+1):ℝ)+14) ≤
          (base+17760*(2 * |LeafCore.C|+14))*scale w V := by
        linarith only [mul_le_mul_of_nonneg_left vol (Nat.cast_nonneg base : (0:ℝ) ≤ base),coreBound,hs]
      simp only [Nat.cast_add,Nat.cast_one] at rounded ⊢
      linarith only [mul_le_mul_of_nonneg_right inner (show (0:ℝ) ≤ extra+5 by positivity),rounded,vol,hs]
    rw [Nat.cast_add,add_mul]
    exact add_le_add sweep chartBound
  intro node w B rows width split label K W V desc pos
  have hb : 0 < B := Nat.pos_of_mul_pos_right (label ▸ pos.2.2.1)
  have hk : 0 < K := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos pos.1 pos.2.1) pos.2.2.2.1) pos.2.2.2.2
  have hp := Shared50ModularControl.prime_prime.pos
  have positive : 0 < W := by dsimp only [W]; positivity
  choose positions coords supply using fun p => step p node w B rows width split label positive
  refine ⟨positions,coords,?_⟩
  intro root path depth b cutoff budget rate enough atNode levels basePos rootWidth stop activeNode L recurse
  have parentLe : node.width ≤ root.width := by
    have h := directoryDigits_bound prime root path
    rw [← atNode] at h
    omega
  have digits := Nat.size_le_size parentLe
  have fits : cutoff < 2^L := (activeNode.trans parentLe).trans_lt (Nat.lt_size_self _)
  have short : L ≤ cutoff := by
    have space := alignedRootWidth_le root depth b cutoff levels basePos rootWidth stop
    have positiveWidth : 0 < root.width := rootWidth ▸ Nat.mul_pos (pow_pos (by decide) _) basePos
    exact Nat.size_le.mpr (by omega)
  have exactPrice : cutoffInvocationTime node L cutoff rate budget = stageBranchTime node cutoff rate budget := by
    funext i
    simp only [cutoffInvocationTime,stageBranchTime]
    split <;> simp [Nat.sub_eq_zero_of_le (short.trans activeNode : L ≤ node.width)]

  obtain ⟨seed,execute⟩ := run node w B rows width split label pos (work w V) (cutoffInvocationTime node L cutoff rate budget) (by
    intro p shared
    obtain ⟨seed,view,_,exec⟩ := supply p L cutoff shared
    have invoke := exec budget rate ((Finset.le_sup' rates (Finset.mem_univ p)).trans enough) fits digits (recurse p)
    exact ⟨seed,view,fun x u S live fresh => invoke x u S fresh live⟩)
  let children := ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map
    (cutoffInvocationTime node L cutoff rate budget)).sum
  obtain ⟨initial,packed⟩ := pack (w := w+1) (B := B) (K := K) (total w V+children) seed (Nat.succ_pos _) hb hk (by
    intro x u S live fresh
    obtain ⟨z,F,t,y,exec,paid,user,out,sem⟩ := execute x u S live fresh
    refine ⟨z,F,t,y,exec,?_,user,out,sem⟩
    intro js unique
    have combine (t f s a b c d : ℕ) (bill : (t : ℝ)+f ≤ s+(a : ℝ)+((b+c+d : ℕ) : ℝ)) :
        t+f ≤ s+(a+b+c+d) := by
      have h : t+f ≤ s+a+(b+c+d) := by exact_mod_cast bill
      omega
    exact combine _ _ _ _ _ _ _ (paid js unique))
  refine ⟨initial,?_⟩
  convert packed using 1
  dsimp only [correction,children,V,W]
  rw [exactPrice]
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
