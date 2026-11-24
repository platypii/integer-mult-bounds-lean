module

public import IntegerMultBounds.MathlibTM2.M6.BitCompiledParentCost
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitCompactBandParent

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- The compact sweeps and the active idle wrappers share one local coefficient.
The assembly rate may include the linear cost of loading the parent record. -/
theorem compactParentLocalBound (stage : Fin 9 → ℝ) (init fixed base swaps : Fin 9 → ℕ) (assemble : ℕ) :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ A : ℝ, ∀ p : CutoffNodeInput,
      (((∑ i, ⌊stage i*((p.node.width : ℝ)^M8.Machine.BudgetBound.tau*p.cells)⌋₊)+
        compiledParentLocal p (fun _ _ _ => 0) init fixed base swaps assemble : ℕ) : ℝ) ≤
      A*((volume prime p.node : ℝ)*(p.node.width : ℝ)^M8.Machine.BudgetBound.tau) := by
  intro inst
  obtain ⟨B,localBound⟩ := compiledParentLocal_bound (fun _ _ _ => 0) init fixed base swaps assemble
    (fun _ => ⟨0,by simp⟩)
  refine ⟨(∑ i, max 0 (stage i))+B,?_⟩
  intro p
  let power := (p.node.width : ℝ)^M8.Machine.BudgetBound.tau
  let scale := (volume prime p.node : ℝ)*power
  have share : p.cells ≤ volume prime p.node := p.cells_share ▸ Nat.le_mul_of_pos_right _ (by decide)
  have each (i : Fin 9) : (⌊stage i*(power*p.cells)⌋₊ : ℝ) ≤ max 0 (stage i)*scale := by
    have size : power*p.cells ≤ scale := by
      rw [mul_comm power]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr share) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have pos : 0 ≤ power*p.cells := by dsimp [power]; positivity
    exact (Nat.cast_le.mpr (Nat.floor_mono (mul_le_mul (le_max_right ..) size pos (le_max_left ..)))).trans
      (Nat.floor_le (mul_nonneg (le_max_left ..) (pos.trans size)))
  rw [Nat.cast_add,Nat.cast_sum,add_mul,Finset.sum_mul]
  exact add_le_add (Finset.sum_le_sum (fun i _ => each i)) (localBound p)

/-- Bound the exact parent execution bill by one unfolding of the cutoff tree.
Only remainder calls draw on child budgets; the sweep work is already paid locally. -/
theorem compactParentTreeBound (stage leaf : Fin 9 → ℝ) (init fixed base swaps : Fin 9 → ℕ)
    (assemble : ℕ) (childRate : ℝ) :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ A R : ℝ, ∀ D, A ≤ D → ∀ (p : CutoffNodeInput) (fuel : ℕ), p.cutoff < p.node.width →
      let child i j := scheduledChild prime p.node (idleDirectoryIndex (i,j))
      let branch i j := if p.cutoff < (child i j).width then
        idleRecordOverhead p (fixed i) (base i) (swaps i)+cutoffTreeBudget D childRate p.cutoff fuel (child i j)
        else ⌊leaf i*((child i j).width : ℝ)^M8.Machine.BudgetBound.tau*volume prime (child i j)⌋₊
      (∑ i, ⌊stage i*((p.node.width : ℝ)^M8.Machine.BudgetBound.tau*p.cells)⌋₊)+
        (∑ i, (init i*p.cells+(735*p.cells+(∑ j, branch i j)+1)+(142081*(10*p.cells+10)+1)))+
        assemble*p.cells+2 ≤ cutoffTreeBudget D R p.cutoff (fuel+1) p.node := by
  intro inst
  obtain ⟨A,localBound⟩ := compactParentLocalBound stage init fixed base swaps assemble
  obtain ⟨L,large⟩ := Finite.exists_le leaf
  let R := max L childRate
  refine ⟨A,R,?_⟩
  intro D enough p fuel active child branch
  let budget j := cutoffTreeBudget D R p.cutoff fuel (scheduledChild prime p.node j)
  let fee i (w : ℕ) := if p.cutoff < w then idleRecordOverhead p (fixed i) (base i) (swaps i) else 0
  have each i j : branch i j ≤ fee i (child i j).width+budget (idleDirectoryIndex (i,j)) := by
    dsimp only [branch,fee,budget]
    split
    · exact Nat.add_le_add_left (cutoffTreeBudget_leaf_mono D (le_max_right ..) _ _ _) _
    · rename_i stopped
      have eq : cutoffTreeBudget D R p.cutoff fuel (child i j) =
          ⌊R*((child i j).width : ℝ)^M8.Machine.BudgetBound.tau*volume prime (child i j)⌋₊ := by
        cases fuel <;> simp [cutoffTreeBudget,stopped]
      change _ ≤ 0+cutoffTreeBudget D R p.cutoff fuel (child i j)
      rw [Nat.zero_add,eq]
      exact Nat.floor_mono (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        ((large i).trans (le_max_left ..)) (by positivity)) (by positivity))
  have window i := Finset.sum_le_sum (s := Finset.univ) (fun j _ => each i j)
  simp only [Finset.sum_add_distrib] at window
  let localFee i := init i*p.cells+735*p.cells+1+(142081*(10*p.cells+10)+1)+
    160*((remainderRanks i).map (fun r => fee i (r*(p.w+1)))).sum
  have combined := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    (show init i*p.cells+(735*p.cells+(∑ j, branch i j)+1)+(142081*(10*p.cells+10)+1) ≤
      localFee i+∑ j, budget (idleDirectoryIndex (i,j)) by
      have h := window i
      change _ ≤ (∑ j, fee i (scheduledChild prime p.node (idleDirectoryIndex (i,j))).width)+_ at h
      rw [idleWindowWidthSum] at h
      dsimp only [localFee]
      omega))
  have directory := flatIdleParentCost localFee budget
  have localBill := (localBound p).trans (mul_le_mul_of_nonneg_right enough (by positivity))
  have fit := Nat.le_floor localBill
  simp only [compiledParentLocal,Finset.sum_const_zero,Nat.zero_add] at fit
  change (∑ i, _)+( (∑ i, localFee i)+assemble*p.cells+2) ≤ _ at fit
  rw [cutoffTreeBudget,ite_eq_left active]
  change _ ≤ _+∑ j, budget j
  omega

/-- One recursive budget covers the packed parent execution at every active
aligned node in the stopping band. The record loader is retained for installation. -/
theorem budgetedCompactBandParent {U Config : Type} :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ minimum leafRate : ℝ, ∀ D, minimum ≤ D →
    ∀ (input : Config → CutoffNodeInput) (blocks : Config → ℕ),
      (∀ c, 7*((input c).w+1) ≤ (input c).cutoff) →
      (∀ c, (input c).root.Positive) → (∀ c, 142080^((input c).depth+1) ∣ (input c).root.rows) →
      (∀ c, (input c).root.beforeH = blocks c*prime^(64*(input c).root.width)) →
      (∀ c, (input c).cutoff < (input c).node.width) →
      ∃ (P : Type) (T : ℕ) (host : P → Pr P T Q prime U), ∃ code src dst, ∃ seed : Config → Stacks T prime,
        LoadsPackedSeed (nodeSeedWords ∘ input) (CutoffNodeInput.cells ∘ input) seed ∧
        ∀ c, let p := input c
        PackedPieceHandoffWithReserve cleanupWeight (fun l r => ∑ j, cleanupWeight (l j) (r j)) p.cells
          (packedChildOutput (p.w+1) p.cells) host code src dst (seed c)
          (cutoffTreeBudget D leafRate p.cutoff (p.depth-p.path.length) p.node) := by
  intro inst
  obtain ⟨q,build⟩ := compactBandParentExecution (U := U) (Config := Config)
  refine ⟨q,?_⟩
  intro Q capacity
  obtain ⟨bridge,stage,init,fixed,base,swaps,childRate,minimum,leaf,run⟩ := build capacity
  obtain ⟨A,R,bound⟩ := compactParentTreeBound stage leaf init fixed base swaps bridge childRate
  refine ⟨max minimum A,R,?_⟩
  intro D enough input blocks band root rows label active
  obtain ⟨P,T,host,code,src,dst,seed,loader,execute⟩ := run D ((le_max_left ..).trans enough)
    input blocks band root rows label M8.Machine.BudgetBound.tau M8.Machine.BudgetBound.exponent_range.1.le
  refine ⟨P,T,host,code,src,dst,seed,loader,?_⟩
  intro c p x u S words fresh
  obtain ⟨z,F,m,y,exec,bill,user,out,act⟩ := execute c x u S words fresh
  refine ⟨z,F,m,y,exec,?_,user,out,act⟩
  intro js nd
  have price := bound D ((le_max_right ..).trans enough) p (p.depth-(p.path.length+1)) (active c)
  rw [p.remainingDepth_eq (active c)]
  apply (bill js nd).trans
  apply Nat.add_le_add_left
  apply Nat.add_le_add_right
  simpa only [sub_self,Real.rpow_zero,mul_one] using price

/-- Load and run the stopping-band parent from a recursive caller's descriptor,
cutoff and row length. Its two live counters carry their cleanup reserve across
the entire entry; the tree allowance includes the loader and split-owner copy. -/
theorem compactBandRecordEntry {U Config : Type} :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q →
    ∀ (input : Config → CutoffNodeInput) (blocks : Config → ℕ),
      (∀ c, 7*((input c).w+1) ≤ (input c).cutoff) →
      (∀ c, (input c).root.Positive) → (∀ c, 142080^((input c).depth+1) ∣ (input c).root.rows) →
      (∀ c, (input c).root.beforeH = blocks c*prime^(64*(input c).root.width)) →
      (∀ c, (input c).cutoff < (input c).node.width) →
      ∃ (N : ℕ) (P : Type) (body : P → Pr P N Q prime U) (dst : Fin (142081+2) ↪ Fin N)
        (minimum leafRate : ℝ), ∀ {T : ℕ} (live : Fin (142080+2) ↪ Fin T) (record : Fin 34 ↪ Fin T),
        (∀ i j, 8 ≤ j.val → record j ≠ live i) →
        let H := 142082+T+N
        ∃ (bank : Fin N ↪ Fin H) (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U)
          (program : Pr (Empty ⊕ P) H Q prime U),
          (∀ f, host (.inr f) = embProg bank Sum.inr (body f)) ∧ ChildBankFrame live bank ∧
          ∀ D, minimum ≤ D → ∀ x, let p := input x
          SplitRecordChildExecWithReserve p live record dst bank host program
            (cutoffTreeBudget D leafRate p.cutoff (p.depth-p.path.length) p.node)
            (fun l r => ∑ i, cleanupWeight (l i) (r i)) ∧
          InstalledRecordChildExecWithReserve p live record dst bank host program
            (cutoffTreeBudget D leafRate p.cutoff (p.depth-p.path.length) p.node)
            (fun l r => ∑ i, cleanupWeight (l i) (r i)) := by
  intro inst
  obtain ⟨q,build⟩ := budgetedCompactBandParent (U := U) (Config := Config)
  refine ⟨q,?_⟩
  intro Q capacity input blocks band root rows label active
  obtain ⟨A,R,parent⟩ := build capacity
  obtain ⟨P,N,body,code,src,dst,seed,load,exec⟩ := parent A le_rfl input blocks band root rows label active
  obtain ⟨entry,install⟩ := runRecordChildWithReserve (LoadsPackedSeed.fromNodeRecord load)
  refine ⟨N,P,body,dst,max 0 A+((entry+21 : ℕ) : ℝ),R,?_⟩
  intro T live record apart H
  obtain ⟨bank,host,program,installed,frame,run⟩ := install body code src dst live record apart
  refine ⟨bank,host,program,installed,frame,?_⟩
  intro D enough x p
  let price := cutoffTreeBudget A R p.cutoff (p.depth-p.path.length) p.node
  have execute := run x price _ (exec x)
  have fits := cutoffRecordEntry_le p entry price A D R (active x) enough le_rfl
  refine ⟨?_,SplitRecordChildExecWithReserve.call execute fits⟩
  intro data u S fan fields cut length scratch bridge vacant
  obtain ⟨z,F,m,y,ran,user,paid,out⟩ := execute data u S fan fields cut length scratch bridge vacant
  refine ⟨z,F,m,y,ran,user,?_,out⟩
  intro js nd
  exact (paid js nd).trans (Nat.add_le_add_right (Nat.add_le_add_left ((Nat.le_add_right _ 2).trans fits) _) _)

end IntegerMultBounds.MathlibTM2.M6.BitNode
