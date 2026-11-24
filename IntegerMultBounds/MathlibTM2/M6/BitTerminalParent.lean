module

public import IntegerMultBounds.MathlibTM2.M6.BitInitializedPackedNode

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

private theorem allChildrenStopped (p : CutoffNodeInput)
    (stop : ∀ k : Fin nodeChildren5.length, ¬ p.cutoff < (scheduledChild prime p.node k).width) :
    42*(p.w+1) ≤ p.cutoff := by
  have member : 42 ∈ nodeChildren5 := nodeChildren5_realizes.mem_iff.mpr (by
    apply List.mem_flatMap.mpr
    exact ⟨(42,5*288),List.mem_map.mpr ⟨(42,288),by decide,rfl⟩,List.mem_replicate.mpr ⟨by decide,rfl⟩⟩)
  obtain ⟨k,h,rank⟩ := List.mem_iff_getElem.mp member
  have bound := Nat.le_of_not_gt (stop ⟨k,h⟩)
  change nodeChildren5[k]*(p.node.width/64) ≤ p.cutoff at bound
  simpa only [rank,p.width,Nat.mul_div_cancel_left _ (by decide : 0 < 64)] using bound

/-- Use the terminal table wherever the dispatcher proves that no grandchild needs
an active entry. Its tape and state counts stay fixed over all such calls. -/
private theorem terminalTable [M8.Machine.Net] {P U : Type} {N Q : ℕ}
    {table : P → Pr P N Q prime U} {dst : Fin (142081+2) ↪ Fin N} {rate : ℝ}
    (family : SplitRecordTreeFamily (Config := TerminalNodeInput) Subtype.val table dst rate (fun _ _ => 0)) :
    RecordTreeFamily (Config := {p : CutoffNodeInput // p.cutoff < p.node.width}) Subtype.val
      table dst rate (fun _ _ _ => False) := by
  obtain ⟨minimum,positive,install⟩ := family
  refine ⟨minimum,positive,?_⟩
  intro T live record disjoint H
  obtain ⟨bank,host,program,placed,frame,exec⟩ := install live record disjoint
  refine ⟨bank,host,program,placed,frame,?_⟩
  intro D enough x p active fuel stopped
  let c : TerminalNodeInput := ⟨p,allChildrenStopped p stopped⟩
  exact exec D enough c active (fun _ _ => Nat.zero_le _)

/-- Execute a complete parent with active terminal children. Its caller supplies
only root alignment and cutoff inequalities, including at the rank-42 calls. -/
theorem terminalChildParent [M8.Machine.Net] (U Config : Type) :
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q →
    ∃ (work : Fin 9 → ℕ → ℕ → ℕ) (init fixed base swaps : Fin 9 → ℕ) (assemble : ℕ)
      (minimum childRate leafRate : ℝ),
    ∀ D, minimum ≤ D → ∀ (input : Config → CutoffNodeInput) (blocks : Config → ℕ),
    (∀ c, (input c).root.Positive) → (∀ c, 142080^((input c).depth+1) ∣ (input c).root.rows) →
    (∀ c, (input c).root.beforeH = blocks c*prime^(64*(input c).root.width)) →
    (∀ c, 7*((input c).w+1) ≤ (input c).cutoff) →
    (∀ c, 42*(42*((input c).w+1)/64) ≤ (input c).cutoff) →
    let budget := fun c (i : ℕ) => let p := input c
      if h : i < nodeChildren5.length then cutoffTreeBudget D childRate p.cutoff
        (p.depth-(p.path.length+1)) (scheduledChild prime p.node ⟨i,h⟩) else 0
    let price := fun c => let p := input c
      compiledParentCharge p work init fixed base swaps assemble (stageBranchTime p.node p.cutoff leafRate (budget c))
    PackedParentRun U Q input price ∧
    (∃ (T : ℕ) (P : Type) (body : P → Pr P T Q prime U) (dst : Fin (142081+2) ↪ Fin T),
      SplitRecordChildFamily input body dst price) ∧
    ∀ c, let p := input c
      p.cutoff < p.node.width →
      (compiledParentLocal p work init fixed base swaps assemble : ℝ) ≤
        D*((volume prime p.node : ℝ)*(p.node.width : ℝ)^M8.Machine.BudgetBound.tau) →
      price c ≤ cutoffTreeBudget D (max childRate leafRate) p.cutoff (min (p.depth-(p.path.length+1)+1) 2) p.node := by
  obtain ⟨q,terminal⟩ := terminalPackedTree U
  obtain ⟨pre,post,ts,s,ports,parent⟩ := compiledPackedParent Unit U Config
  refine ⟨max q s,?_⟩
  intro Q room
  obtain ⟨N,R,tree,dst,childRate,family⟩ := terminal ((Nat.le_max_left ..).trans room)
  obtain ⟨leafRate,build⟩ := parent ((Nat.le_max_right ..).trans room) (terminalTable family)
  obtain ⟨body,active,work,bound,init,fixed,base,swaps,minimum,leaf,assemble,nonneg,pos,run⟩ :=
    build (fun _ _ _ => .act .done) (fun _ _ => ())
  refine ⟨work,init,fixed,base,swaps,assemble,minimum,childRate,leafRate,?_⟩
  intro D enough input blocks positive rows label band terminalWidth budget price
  have width (c : Config) (k : Fin nodeChildren5.length) :
      (scheduledChild prime (input c).node k).width ≤ 42*((input c).w+1) := by
    change nodeChildren5[k.val]*((input c).node.width/64) ≤ _
    rw [(input c).width,Nat.mul_div_cancel_left _ (by decide)]
    exact Nat.mul_le_mul_right _ (nodeChildren5_bounds k).2
  have stop (c : Config) (i k : Fin nodeChildren5.length) :
      (scheduledChild prime (scheduledChild prime (input c).node i) k).width ≤ (input c).cutoff :=
    ((Nat.mul_le_mul_right _ (nodeChildren5_bounds k).2).trans
      (Nat.mul_le_mul_left 42 (Nat.div_le_div_right (c := 64) (width c i)))).trans (terminalWidth c)
  obtain ⟨position,coords,execute⟩ := run D enough input blocks positive rows label (by
    intro c i j p active x root path cut k d live
    exact (stop c (idleDirectoryIndex (i,j)) k).not_gt live)
  obtain ⟨physical,charged⟩ := execute leafRate le_rfl (fun c _ _ h => False.elim ((band c).not_gt h))
  refine ⟨physical,?_,?_⟩
  · obtain ⟨P,T,body,code,src,dst,seed,load,exec⟩ := physical
    exact ⟨T,P,body,dst,splitRecordChildFamily (LoadsPackedSeed.fromNodeRecord load) exec⟩
  intro c p active localBound
  apply (charged c active localBound).1.trans_eq
  apply cutoffTreeBudget_prune
  intro path len
  obtain ⟨i,k,rfl⟩ := List.length_eq_two.mp len
  exact stop c i k

end IntegerMultBounds.MathlibTM2.M6.BitNode
