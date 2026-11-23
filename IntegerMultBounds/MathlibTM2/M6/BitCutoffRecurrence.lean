module

public import IntegerMultBounds.MathlibTM2.M6.BitCutoffNode
public import IntegerMultBounds.MathlibTM2.M6.BitFlatSweepHandoff

/-! Descend from an aligned PR589 root with one budget for each actual path. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 RecursiveInterchangeLayout
open Shared50ModularControl (prime)
open Stack Host Cover.Fallback M8.RevMachine IntervalDescriptor
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
open Layer.SelectedMoments (bitSaving)

/-- Alignment reserved at the root suffices to instantiate the packed node
at any path where the dispatcher takes its active branch. -/
theorem activeCutoffNodeInput (root : Descriptor) (depth b cutoff blocks : ℕ)
    (positive : root.Positive) (levels : 0 < depth) (base : 0 < b)
    (width : root.width = 64^depth*b) (rows : 142080^(depth+1) ∣ root.rows)
    (label : root.beforeH = blocks*prime^(64*root.width)) (stop : 42^depth*b ≤ cutoff)
    (path : List (Fin nodeChildren5.length)) (active : cutoff < (path.foldl (scheduledChild prime) root).width) :
    ∃ v : CutoffNodeInput, v.root = root ∧ v.path = path ∧ v.depth = depth ∧ v.b = b ∧ v.cutoff = cutoff := by
  have shrink : root.width*42^depth ≤ cutoff*64^depth := by
    rw [width]
    simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_right (64^depth) stop
  obtain ⟨w,groups,B,shape,split,labels,_,_,pos⟩ := activeFlatDimensions root depth cutoff blocks positive
    (width ▸ Nat.mul_pos (pow_pos (by decide) _) base) ⟨_,width⟩ rows label shrink path active
  exact ⟨⟨root,path,depth,b,cutoff,w,groups,B,levels,base,width,stop,active.le,shape,split,labels,
    pos.1,Nat.pos_of_mul_pos_left pos.2.1,pos.2.2⟩,rfl,rfl,rfl,rfl,rfl⟩

/-- The local and stopped prices have the same width scale. Only an active
node pays its own local work and descends to the scheduled children. -/
noncomputable def cutoffTreeBudget [M8.Machine.Net] (localRate leafRate : ℝ) (cutoff : ℕ) :
    ℕ → Descriptor → ℕ
  | 0, v => ⌊leafRate*(v.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime v⌋₊
  | fuel+1, v => if cutoff < v.width then
      ⌊localRate*((volume prime v : ℝ)*(v.width : ℝ)^M8.Machine.BudgetBound.tau)⌋₊ +
        ∑ k : Fin nodeChildren5.length, cutoffTreeBudget localRate leafRate cutoff fuel (scheduledChild prime v k)
    else ⌊leafRate*(v.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime v⌋₊

private theorem stopped_treeBudget [M8.Machine.Net] (D rate : ℝ) (cutoff fuel : ℕ) (v : Descriptor)
    (stop : v.width ≤ cutoff) : cutoffTreeBudget D rate cutoff fuel v =
    ⌊rate*(v.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime v⌋₊ := by
  cases fuel <;> simp [cutoffTreeBudget,Nat.not_lt_of_ge stop]

/-- The exact node bill fits the tree budget when each active worker receives
its child's budget. Stopped children already have that price in the tree. -/
theorem cutoffNodeCharge_le [M8.Machine.Net] (v : CutoffNodeInput) (work : Fin 9 → ℕ → ℕ → ℕ)
    (assemble : ℕ) (D rate : ℝ) (fuel : ℕ) (active : v.cutoff < v.node.width)
    (reserve : ℕ := 0)
    (localBound : ((v.localCharge work assemble+reserve : ℕ) : ℝ) ≤ D*((volume prime v.node : ℝ)*(v.node.width : ℝ)^M8.Machine.BudgetBound.tau)) :
    let next := fun i => if h : i < nodeChildren5.length then
      cutoffTreeBudget D rate v.cutoff fuel (scheduledChild prime v.node ⟨i,h⟩) else 0
    (v.localCharge work assemble+reserve) + ∑ k : Fin nodeChildren5.length, stageBranchTime v.node v.cutoff rate next k.val ≤
      cutoffTreeBudget D rate v.cutoff (fuel+1) v.node := by
  intro next
  rw [cutoffTreeBudget,ite_eq_left active]
  apply Nat.add_le_add (Nat.le_floor localBound)
  apply Finset.sum_le_sum
  intro k _
  simp only [stageBranchTime,next,dite_eq_left k.isLt]
  split
  · rfl
  · rename_i stopped
    exact (stopped_treeBudget D rate v.cutoff fuel _ (Nat.le_of_not_gt stopped)).symm.le

/-- The scheduled PR589 moment bounds the same integral budget used by the
packed node, including the stopped price at the bottom of every path. -/
theorem cutoffTreeBudget_closed [M8.Machine.Net] (root : Descriptor) (depth cutoff : ℕ) (D rate lam : ℝ)
    (hd : 0 ≤ D) (hr : 0 ≤ rate) (hτ : M8.Machine.BudgetBound.tau ≤ lam)
    (gap : 1-bitSaving < lam) (hu : 1 ≤ cutoff) (positive : 0 < volume prime root)
    (width : 64^depth ∣ root.width) (rows : 142080^depth ∣ root.rows)
    (stop : root.width*42^depth ≤ cutoff*64^depth) :
    (cutoffTreeBudget D rate cutoff depth root : ℝ) ≤
      (2*D/(1-((42 : ℝ)/64)^(lam-(1-bitSaving)))*(root.width : ℝ)^lam+
       rate*(root.width : ℝ)^(1-bitSaving)*(cutoff : ℝ)^(1-(1-bitSaving)))*volume prime root := by
  let layout := fun path : List (Fin nodeChildren5.length) => path.foldl (scheduledChild prime) root
  let descend := fun (path : List (Fin nodeChildren5.length)) i => path++[i]
  let steps := fun path => cutoffTreeBudget D rate cutoff (depth-path.length) (layout path)
  have child (path i) : layout (descend path i) = scheduledChild prime (layout path) i := by
    simp [layout,descend]
  have leaf (path) (h : (layout path).width ≤ cutoff) :
      (steps path : ℝ) ≤ rate*(layout path).width*volume prime (layout path) := by
    dsimp only [steps]
    rw [stopped_treeBudget _ _ _ _ _ h]
    have power : ((layout path).width : ℝ)^M8.Machine.BudgetBound.tau ≤ (layout path).width := by
      by_cases zero : (layout path).width = 0
      · simp [zero,Real.zero_rpow M8.Machine.BudgetBound.exponent_range.1.ne']
      · exact Real.rpow_le_self_of_one_le (by exact_mod_cast (by omega : 1 ≤ (layout path).width))
          M8.Machine.BudgetBound.exponent_range.2.le
    exact (Nat.floor_le (by positivity)).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left power hr) (by positivity))
  have bound := five_root_closed prime layout descend steps [] depth cutoff
    (τ := M8.Machine.BudgetBound.tau) (lam := lam) (K := 1) (C₀ := rate) (C₁ := D)
    M8.Machine.BudgetBound.exponent_range.1.le hτ gap le_rfl hr hd hu width rows stop positive (leaf [])
    (fun path _ _ _ _ i _ => leaf (descend path i))
    (fun path _ _ _ _ i => by rw [child]; exact ⟨rfl,rfl,rfl⟩) (by
      intro path active _ _ _
      have short := scheduledPath_length_lt prime root depth cutoff stop path active
      have fuel : depth-path.length = (depth-(path.length+1))+1 := by omega
      dsimp only [steps]
      rw [fuel,cutoffTreeBudget,ite_eq_left active]
      simp only [child,descend,List.length_append,List.length_cons,List.length_nil,Nat.zero_add,Nat.cast_add,one_mul]
      apply add_le_add_left
      have localCost := Nat.floor_le (a := D*((volume prime (layout path) : ℝ)*((layout path).width : ℝ)^M8.Machine.BudgetBound.tau)) (by positivity)
      nlinarith only [localCost,mul_nonneg hd (Nat.cast_nonneg (volume prime (layout path)) : (0:ℝ) ≤ volume prime (layout path))])
  simpa only [steps,layout,List.length_nil,Nat.sub_zero,List.foldl_nil,Real.one_rpow,mul_one] using bound

/-- The physical node contract with the child allowances fixed by the
recurrence, uniformly over all active inputs of one procedure table. -/
def CutoffTreeExecution [M8.Machine.Net] (P U Config : Type) (entryRate : ℝ := 0) : Prop :=
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
    ∃ D : ℝ, 0 ≤ D ∧ entryRate ≤ D ∧ ∀ (input : Config → CutoffNodeInput), (∀ c, (input c).cutoff < (input c).node.width) →
    let d := fun c n p j i => scheduledChild prime (input c).node (child n p j i)
    ∃ position : ∀ c n p j i, Fin (volume prime (d c n p j i)) ≃ Fin ((prime^((input c).w+1))^16*(input c).stageWidth),
    (∀ c n p j i, invocationCoordinates j ((input c).w+1) (input c).stageWidth (position c n p j i)) ∧
    ∀ rate : ℝ, leafRate ≤ rate →
    let budget := fun c (k : Fin nodeChildren5.length) => let v := input c
      cutoffTreeBudget D rate v.cutoff (v.depth-(v.path.length+1)) (scheduledChild prime v.node k)
    (∀ c n p j i, let v := input c
      let k := child n p j i
      let h := d c n p j i
      v.cutoff < h.width → h.width < v.node.width →
      if j = 1 then ScheduledChildExec v.node h v.w v.stageWidth (ports n p j i)
        (binSyms v.root.width.size v.cutoff) (position c n p j i) (body n p j i) (.active (entry n p j i)) (budget c k) true
      else MoveOnBankExec v.node h v.w v.stageWidth (movePrefix.trans (ports n p j i))
        (binSyms v.root.width.size v.cutoff) (position c n p j i) (body n p j i)
        (large n p j i (entry n p j i)) (budget c k) true) →
    (∀ c n (j : Fin idleCopies.length), let v := input c
      let k := idleDirectoryIndex (n,j)
      let e := idleInterval n idleCopies[j.val].2
      v.cutoff < (scheduledChild prime v.node k).width →
      IntervalWorkerExec idleBody (.inr (idleEntry n)) (phaseIntervalChild (e.1+1) (e.2+1) (v.w+1) v.idleWidth 64)
        (v.w+1) v.idleWidth (budget c k) (binSyms v.root.width.size v.cutoff)) →
    ∃ (R : Type) (T : ℕ) (host : R → Pr R T Q prime U) (code : Pr R T Q prime U)
      (src dst : Fin (142081+2) ↪ Fin T) (seed : Config → Stacks T prime),
    ∀ (c : Config), let v := input c
      PackedPieceHandoffWithCharge cleanupWeight v.cells (packedChildOutput (v.w+1) v.cells)
        host code src dst (seed c) (cutoffTreeBudget D rate v.cutoff (v.depth-v.path.length) v.node -
          ⌊entryRate*((volume prime v.node : ℝ)*(v.node.width : ℝ)^M8.Machine.BudgetBound.tau)⌋₊)

theorem selectedCutoffTree [M8.Machine.Net] (P U Config : Type) (entryRate : ℝ := 0) :
    CutoffTreeExecution P U Config entryRate := by
  classical
  unfold CutoffTreeExecution
  intro l r count
  obtain ⟨pre,post,first,last,ts,ports,states,build⟩ := selectedCutoffNode P U Config
  refine ⟨pre,post,first,last,ts,ports,states,?_⟩
  intro Q cap
  obtain ⟨N,leaf,install⟩ := build cap
  refine ⟨N,max 0 leaf,?_⟩
  intro large entry idleLarge idleEntry
  obtain ⟨body,idle,installed,labels,work,assemble,⟨C,localBound⟩,run⟩ := install large entry idleLarge idleEntry
  let D := max 0 C + max 0 entryRate
  refine ⟨body,idle,installed,labels,D,add_nonneg (le_max_left ..) (le_max_left ..),
    (le_max_right 0 entryRate).trans (le_add_of_nonneg_left (le_max_left ..)),?_⟩
  intro input active d
  obtain ⟨positions,geometry,call⟩ := run input
  refine ⟨positions,geometry,?_⟩
  intro rate enough budget stages intervals
  let next := fun c i => if h : i < nodeChildren5.length then budget c ⟨i,h⟩ else 0
  obtain ⟨R,T,host,code,src,dst,seed,execute⟩ := call next rate ((le_max_right _ _).trans enough)
    (fun c n p j i => by simpa only [next,dite_eq_left (invocationChildren n p (pre n p) (post n p) j i).isLt] using stages c n p j i)
    (fun c n j => by simpa only [next,dite_eq_left (idleDirectoryIndex (n,j)).isLt] using intervals c n j)
  refine ⟨R,T,host,code,src,dst,seed,?_⟩
  intro c v x u S words fresh
  obtain ⟨z,F,t,y,exec,paid,user,out,read⟩ := execute c x u S words fresh
  refine ⟨z,F,t,y,exec,?_,user,out,read⟩
  intro js unique
  have shrink : v.root.width*42^v.depth ≤ v.cutoff*64^v.depth := by
    rw [v.rootWidth]
    simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_right (64^v.depth) v.stop
  have short := scheduledPath_length_lt prime v.root v.depth v.cutoff shrink v.path (active c)
  have fuel : v.depth-v.path.length = (v.depth-(v.path.length+1))+1 := by omega
  rw [fuel]
  let scale := (volume prime v.node : ℝ)*(v.node.width : ℝ)^M8.Machine.BudgetBound.tau
  have hs : 0 ≤ scale := by dsimp [scale]; positivity
  have allowance : (⌊entryRate*scale⌋₊ : ℝ) ≤ max 0 entryRate*scale := by
    have h := Nat.floor_mono (mul_le_mul_of_nonneg_right (le_max_right 0 entryRate) hs)
    exact (Nat.cast_le.mpr h).trans (Nat.floor_le (mul_nonneg (le_max_left ..) hs))
  have combined : ((v.localCharge work assemble+⌊entryRate*scale⌋₊ : ℕ) : ℝ) ≤ D*scale := by
    rw [Nat.cast_add]
    unfold D
    rw [add_mul]
    exact add_le_add ((localBound v).trans (mul_le_mul_of_nonneg_right (le_max_right ..) hs)) allowance
  let remaining := v.depth-(v.path.length+1)
  let children := ∑ k : Fin nodeChildren5.length, stageBranchTime v.node v.cutoff rate (next c) k.val
  let total := cutoffTreeBudget D rate v.cutoff (remaining+1) v.node
  have charged := cutoffNodeCharge_le v work assemble D rate remaining (active c) _ combined
  have core := paid js unique
  change _ ≤ tapeCharge cleanupWeight js S+(v.localCharge work assemble+children) at core
  change (v.localCharge work assemble+⌊entryRate*scale⌋₊)+children ≤ total at charged
  change _ ≤ tapeCharge cleanupWeight js S+(total-⌊entryRate*scale⌋₊)
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
