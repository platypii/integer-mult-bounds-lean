module

public import IntegerMultBounds.MathlibTM2.M6.BitCutoffRecurrence
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIntervalRecord

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 RecursiveInterchangeLayout
open Shared50ModularControl (prime)
open Stack Host Cover.Fallback M8.RevMachine IntervalDescriptor

/-- Descending to a live idle entry supplies exactly one packed word per role
of the interval worker. Its remaining depth is the fuel used in the parent's sum. -/
theorem activeIdleCutoffInput (v : CutoffNodeInput) (blocks : ℕ) (positive : v.root.Positive)
    (rows : 142080^(v.depth+1) ∣ v.root.rows)
    (label : v.root.beforeH = blocks*prime^(64*v.root.width))
    (i : Fin 9) (j : Fin idleCopies.length) :
    let k := idleDirectoryIndex (i,j)
    let e := idleInterval i idleCopies[j.val].2
    let lane := phaseIntervalChild (e.1+1) (e.2+1) (v.w+1) v.idleWidth 64
    v.cutoff < (scheduledChild prime v.node k).width →
    ∃ c : CutoffNodeInput, c.node = scheduledChild prime v.node k ∧
      c.root = v.root ∧ c.path = v.path++[k] ∧ c.cutoff = v.cutoff ∧
      c.depth-c.path.length = v.depth-(v.path.length+1) ∧
      c.path.length < c.depth ∧ v.w+1 ≤ c.node.width ∧
      lane.width = 64*(c.w+1) ∧ volume prime lane = c.cells := by
  intro k e lane active
  have next : (v.path++[k]).foldl (scheduledChild prime) v.root = scheduledChild prime v.node k := by
    simp [CutoffNodeInput.node,List.foldl_append]
  obtain ⟨c,root,path,depth,_,cutoff⟩ := activeCutoffNodeInput v.root v.depth v.b v.cutoff blocks
    positive v.levels v.base v.rootWidth rows label v.stop _ (next ▸ active)
  have node : c.node = scheduledChild prime v.node k := by
    simpa only [CutoffNodeInput.node,root,path] using next
  have measures := alignedIntervalMeasures v.node (v.w+1) v.groups v.idleWidth (Nat.succ_pos _)
    v.width v.rows rfl i idleCopies[j.val]
  simp only [idleCopyIndex_at] at measures
  have shrink : v.root.width*42^v.depth ≤ v.cutoff*64^v.depth := by
    rw [v.rootWidth]
    simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_right (64^v.depth) v.stop
  have short := scheduledPath_length_lt prime v.root v.depth v.cutoff shrink _ (next ▸ active)
  have lower : v.w+1 ≤ c.node.width := by
    rw [node]
    change v.w+1 ≤ nodeChildren5[k.val]*(v.node.width/64)
    rw [v.width,Nat.mul_div_cancel_left _ (by decide)]
    exact Nat.le_mul_of_pos_left _ (nodeChildren5_bounds k).1
  refine ⟨c,node,root,path,cutoff,by simp [depth,path],by simpa only [depth,path] using short,lower,measures.1.trans (node ▸ c.width),?_⟩
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 142080)
    (measures.2.2.trans ((congrArg (volume prime) node).symm.trans c.cells_share.symm))

/-- Pay the interval wrapper and the packed node's own work from a single
local allowance. All grandchildren keep the same tree rate at every depth. -/
theorem idleCutoffBudget (U : Type) (push setup passes privateCount : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (lo hi w W : ℕ), lo ≤ hi → hi ≤ 64 → 0 < W →
      let V := (prime^(w+1))^128*W
      ∀ (child : Descriptor) (cutoff fuel price : ℕ) (D rate : ℝ),
      cutoff < child.width → w+1 ≤ child.width → V ≤ volume prime child →
      C ≤ D → price ≤ cutoffTreeBudget D rate cutoff (fuel+1) child -
        ⌊C*((volume prime child : ℝ)*(child.width : ℝ)^M8.Machine.BudgetBound.tau)⌋₊ →
      flatIntervalCost U lo hi w W 64 V push setup passes privateCount price ≤
        cutoffTreeBudget D rate cutoff (fuel+1) child := by
  obtain ⟨C,pos,bound⟩ := flatIntervalCost_cutoff U push setup passes privateCount
  refine ⟨C,pos,?_⟩
  intro lo hi w W ordered fits hW V child cutoff fuel price D rate active width mass enough packed
  let scale := (volume prime child : ℝ)*(child.width : ℝ)^M8.Machine.BudgetBound.tau
  let wrapper := C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have time := bound lo hi ordered fits w W hW price
  change flatIntervalCost U lo hi w W 64 V push setup passes privateCount price ≤ price+⌊wrapper⌋₊ at time
  have wrapperBound : wrapper ≤ C*scale := by
    dsimp only [wrapper,scale]
    rw [← mul_assoc]
    gcongr
    exact M8.Machine.BudgetBound.exponent_range.1.le
  have fitsBudget : ⌊C*scale⌋₊ ≤ cutoffTreeBudget D rate cutoff (fuel+1) child := by
    rw [cutoffTreeBudget,ite_eq_left active]
    exact (Nat.floor_mono (mul_le_mul_of_nonneg_right enough (by dsimp [scale]; positivity))).trans
      (Nat.le_add_right ..)
  have covered := Nat.floor_mono wrapperBound
  change price ≤ cutoffTreeBudget D rate cutoff (fuel+1) child-⌊C*scale⌋₊ at packed
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
