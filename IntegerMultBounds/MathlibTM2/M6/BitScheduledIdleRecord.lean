module

public import IntegerMultBounds.MathlibTM2.M6.BitCompiledIdleRecord
public import IntegerMultBounds.MathlibTM2.M6.BitCutoffIdleChild

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout IntervalDescriptor

noncomputable def idleRecordOverhead (p : CutoffNodeInput) (fixed base swaps : ℕ) : ℕ :=
  fixed*p.cells + (base+swaps*(@swapVolumeRate BinaryRadixEqualShared.supplierNet p.w))*
    ((prime^(p.w+1))^128*p.idleWidth)

/-- Sum any rank-dependent charge over the physical entries, including
the cutoff test at the actual child width. -/
theorem idleWindowWidthSum (p : CutoffNodeInput) (i : Fin 9) (price : ℕ → ℕ) :
    (∑ j : Fin idleCopies.length, price (scheduledChild prime p.node (idleDirectoryIndex (i,j))).width) =
      160*((remainderRanks i).map (fun r => price (r*(p.w+1)))).sum := by
  let f := fun (k : (Fin 32 × Fin 5) × Fin 222) => let e := idleInterval i k.2
                     price ((e.2-e.1)*(p.w+1))
  have same (j : Fin idleCopies.length) :
      price (scheduledChild prime p.node (idleDirectoryIndex (i,j))).width = f idleCopies[j.val] := by
    change price (nodeChildren5.get (idleDirectoryIndex (i,j))*(p.node.width/64)) = _
    rw [p.width,Nat.mul_div_cancel_left _ (by decide),idleDirectoryIndex_rank]
  simp_rw [same]
  rw [← List.sum_ofFn]
  have listed : List.ofFn (fun j : Fin idleCopies.length => f idleCopies[j.val]) = idleCopies.map f := by
    conv_rhs => rw [← List.ofFn_getElem (xs := idleCopies),List.map_ofFn]
    rfl
  rw [listed]
  have ranks := congrArg (fun xs : List ℕ => (xs.map (fun r => price (r*(p.w+1)))).sum) (idleCopies_ranks i)
  simpa only [f,List.map_map,Function.comp_def,Piece.children,sum_runs] using ranks

/-- A whole window pays the width-dependent part on one quarter of the
parent's cells. Recursive allowances can be added occurrence by occurrence. -/
theorem idleWindowOverhead (p : CutoffNodeInput) (fixed base swaps : ℕ) :
    4*(∑ _j : Fin idleCopies.length, idleRecordOverhead p fixed base swaps) =
      (142080*fixed+base+swaps*(@swapVolumeRate BinaryRadixEqualShared.supplierNet p.w))*p.cells := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,idleCopies_length,nsmul_eq_mul,
    idleRecordOverhead,CutoffNodeInput.cells]
  ring

/-- Charge the active wrappers at the ranks that actually exceed the cutoff.
Each occurrence keeps its own recursive or stopped allowance. -/
theorem scheduledIdleWindowBill (p : CutoffNodeInput) (i : Fin 9) (fixed base swaps : ℕ)
    (bill branch : Fin idleCopies.length → ℕ)
    (each : ∀ j, bill j ≤ branch j + if p.cutoff <
      (scheduledChild prime p.node (idleDirectoryIndex (i,j))).width
      then idleRecordOverhead p fixed base swaps else 0) :
    (∑ j, bill j) ≤ (∑ j, branch j) + 160*((remainderRanks i).map (fun r =>
      if p.cutoff < r*(p.w+1) then idleRecordOverhead p fixed base swaps else 0)).sum ∧
    4*(∑ j, bill j) ≤ 4*(∑ j, branch j) +
      (142080*fixed+base+swaps*(@swapVolumeRate BinaryRadixEqualShared.supplierNet p.w))*p.cells := by
  let charge := fun width => if p.cutoff < width then idleRecordOverhead p fixed base swaps else 0
  let width := fun j => (scheduledChild prime p.node (idleDirectoryIndex (i,j))).width
  have total : (∑ j, bill j) ≤ (∑ j, branch j) + ∑ j, charge (width j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => each j)
  refine ⟨total.trans_eq (congrArg ((∑ j, branch j)+·) (idleWindowWidthSum p i charge)),?_⟩
  have localBound : (∑ j, charge (width j)) ≤ ∑ _j : Fin idleCopies.length, idleRecordOverhead p fixed base swaps :=
    Finset.sum_le_sum (fun j _ => by dsimp [charge]; split <;> simp)
  have bound := Nat.mul_le_mul_left 4 (total.trans (Nat.add_le_add_left localBound _))
  rwa [Nat.mul_add,idleWindowOverhead] at bound

/-- Execution contract in parent coordinates at an active directory entry. -/
def ScheduledIdleRecordRun [M8.Machine.Net] {A U : Type} {H Q : ℕ}
    (table : A → Pr A H Q prime U) (code : Pr A H Q prime U)
    (raw : Fin 72 ↪ Fin H) (fields : Fin 6 ↪ Fin H) (work : List (Fin H))
    (i : Fin 9) (j : Fin idleCopies.length) (D leafRate : ℝ)
    (childBudget : {c : CutoffNodeInput // c.cutoff < c.node.width} → ℕ → ℕ)
    (fixed base swaps : ℕ) : Prop :=
    ∀ (p : CutoffNodeInput) blocks, p.root.Positive → 142080^(p.depth+1) ∣ p.root.rows →
      p.root.beforeH = blocks*prime^(64*p.root.width) →
      let index := idleDirectoryIndex (i,j)
      let child := scheduledChild prime p.node index
      let fuel := p.depth-(p.path.length+1)
      p.cutoff < child.width →
      (∀ (x : {c : CutoffNodeInput // c.cutoff < c.node.width}), x.val.root = p.root → x.val.path = p.path++[index] → x.val.cutoff = p.cutoff →
        ∀ k : Fin nodeChildren5.length, let d := scheduledChild prime child k
        p.cutoff < d.width → childBudget x k.val ≤ cutoffTreeBudget D leafRate p.cutoff (fuel-1) d) →
      ∀ (word : Fin p.cells → ZMod 2) u S,
        RecordPayload (raw 24) (fun _ => blank) 0 word S →
        IdleDispatchReady raw p.w p.idleWidth p.root.width.size p.cutoff S →
        (∀ t ∈ work, S.L t = [] ∧ S.R t = []) →
        (∀ k, S.R (fields k) = (Routines.hdr (role p.node 142080) k).map bitSymbol) →
        ∃ z F n changed, Exec table code (mk u S) n (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F n (idleRecordOverhead p fixed base swaps+cutoffTreeBudget D leafRate p.cutoff fuel child) ∧
          RecordPayload (raw 24) (fun _ => blank) 0 changed F ∧
          parentIntervalRead i idleCopies[j.val].2 (p.w+1) (p.idleWidth*142080) word changed ∧
          ∀ t, t ≠ raw 24 → F.L t = S.L t ∧ F.R t = S.R t

/-- An active occurrence consumes the parent's dispatch seed and returns its
word in parent order. Charge its recursive call at the next path depth. -/
theorem scheduledIdleRecord [M8.Machine.Net] {P U : Type} {N T Q : ℕ}
    {body : P → Pr P N Q prime U} {dst : Fin (142081+2) ↪ Fin N} {leafRate : ℝ}
    {childBudget : {c : CutoffNodeInput // c.cutoff < c.node.width} → ℕ → ℕ}
    (family : SplitRecordTreeFamily Subtype.val body dst leafRate childBudget)
    (swapCap : (@rowSwapBlock BinaryRadixEqualShared.supplierNet).states ≤ Q)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (i : Fin 9) (j : Fin idleCopies.length) (board : Fin 113 ↪ Fin T)
    (splitter : Fin intervalSplitTapes ↪ Fin T) (apart : ∀ r k, splitter r ≠ board k) :
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    let embed := caller.trans (intervalExtend T N)
    let raw := ((Fin.castLEEmb (by decide : 72 ≤ 113)).trans board).trans embed
    let fields := (idleRolePorts.trans board).trans embed
    let work := idleCallerWork (((Fin.castAddEmb 35 (n := 78)).trans board).trans embed)
    ∃ minimum : ℝ, 0 ≤ minimum ∧
      ∃ (table : Option (Empty ⊕ P) → Pr (Option (Empty ⊕ P)) (intervalHostSize T N) Q prime U)
        (code : Pr (Option (Empty ⊕ P)) (intervalHostSize T N) Q prime U) (fixed base swaps : ℕ),
      ∀ D : ℝ, minimum ≤ D → ScheduledIdleRecordRun table code raw fields work i j D leafRate childBudget fixed base swaps := by
  intro caller embed raw fields work
  obtain ⟨minimum,positive,build⟩ := compiledIdleRecord family swapCap capacity i j board splitter apart
  refine ⟨minimum,positive,?_⟩
  obtain ⟨table,code,fixed,base,swaps,run⟩ := build
  refine ⟨table,code,fixed,base,swaps,?_⟩
  intro D enough p blocks rootPos rows label index child fuel active children word u S payload ready fresh roles
  obtain ⟨c,node,root,path,cut,remaining,_,_,_,_,cells⟩ := activeIdleCutoffInput p blocks rootPos rows label i j active
  have live : c.cutoff < c.node.width := by simpa only [cut,node] using active
  let x : {c : CutoffNodeInput // c.cutoff < c.node.width} := ⟨c,live⟩
  let e := idleInterval i idleCopies[j.val].2
  let lane := phaseIntervalChild (e.1+1) (e.2+1) (p.w+1) p.idleWidth 64
  let wide := {lane with afterD := lane.afterD*142080}
  have bounds := idleBounds i idleCopies[j.val].2
  have shape : wide = phaseIntervalChild (e.1+1) (e.2+1) (p.w+1) (p.idleWidth*142080) 64 := by
    simp only [wide,lane,phaseIntervalChild,Nat.mul_assoc]
  have size : volume prime wide = p.cells := (congrArg (volume prime) shape).trans
    (intervalChild_volume (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2) _ _)
  have grandchildren (k : Fin nodeChildren5.length) := children x root path cut k
  have depth : c.depth-(c.path.length+1) = fuel-1 := by
    rw [← Nat.sub_sub,remaining]
  obtain ⟨z,F,n,exec,user,paid,record,off⟩ := run D enough p x node live (fun k => by
    simpa only [x,cut,node,depth,child,index] using grandchildren k)
    (fun k => word (k.cast size)) u S (recordPayload_castInput size _ _ _ payload)
    (by simpa only [x,root,cut] using ready) fresh roles
  let y := Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) (fun k => word (k.cast size))
  refine ⟨z,F,n,fun k => y (k.cast size.symm),exec,user,?_,recordPayload_castInput size.symm _ _ y record,?_,off⟩
  · have mass : volume prime lane = (prime^(p.w+1))^128*p.idleWidth :=
      intervalChild_volume (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2) _ _
    change volume prime lane = c.cells at cells
    simpa only [idleRecordOverhead,x,← cells,mass,cut,remaining,node,child,index,fuel] using paid
  · exact parentReadOfPhysicalTranspose i idleCopies[j.val].2 _ _ wide shape size word y rfl

/-- Choose all entries in a window before selecting the recurrence
coefficient. The three uniform rates also price every active subwindow. -/
theorem scheduledIdleWindowRecords [M8.Machine.Net] {P U : Type} {N T Q : ℕ}
    {body : P → Pr P N Q prime U} {dst : Fin (142081+2) ↪ Fin N} {leafRate : ℝ}
    {childBudget : {c : CutoffNodeInput // c.cutoff < c.node.width} → ℕ → ℕ}
    (family : SplitRecordTreeFamily Subtype.val body dst leafRate childBudget)
    (swapCap : (@rowSwapBlock BinaryRadixEqualShared.supplierNet).states ≤ Q)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (i : Fin 9) (board : Fin idleCopies.length → Fin 113 ↪ Fin T)
    (splitter : Fin idleCopies.length → Fin intervalSplitTapes ↪ Fin T)
    (apart : ∀ j r k, splitter j r ≠ board j k) :
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    let embed := caller.trans (intervalExtend T N)
    let raw j := ((Fin.castLEEmb (by decide : 72 ≤ 113)).trans (board j)).trans embed
    let fields j := (idleRolePorts.trans (board j)).trans embed
    let work j := idleCallerWork (((Fin.castAddEmb 35 (n := 78)).trans (board j)).trans embed)
    let A := Option (Empty ⊕ P)
    ∃ (minimum : ℝ) (table : Fin idleCopies.length → A → Pr A (intervalHostSize T N) Q prime U)
      (code : Fin idleCopies.length → Pr A (intervalHostSize T N) Q prime U) (fixed base swaps : ℕ),
      0 ≤ minimum ∧ ∀ D : ℝ, minimum ≤ D → ∀ j,
      ScheduledIdleRecordRun (table j) (code j) (raw j) (fields j) (work j) i j D leafRate childBudget fixed base swaps := by
  classical
  intro caller embed raw fields work A
  choose minimum nonneg table code fixed base swaps run using fun j =>
    scheduledIdleRecord family swapCap capacity i j (board j) (splitter j) (apart j)
  refine ⟨∑ j, minimum j,table,code,Finset.univ.sup fixed,Finset.univ.sup base,Finset.univ.sup swaps,
    Finset.sum_nonneg (fun j _ => nonneg j),?_⟩
  intro D enough j p blocks positive rows label index child fuel active children word u S payload ready fresh roles
  have threshold := (Finset.single_le_sum (fun j _ => nonneg j) (Finset.mem_univ j)).trans enough
  obtain ⟨z,F,n,y,exec,user,paid,out,read,frame⟩ := run j D threshold p blocks positive rows label active
    children word u S payload ready fresh roles
  refine ⟨z,F,n,y,exec,user,?_,out,read,frame⟩
  have localBound : idleRecordOverhead p (fixed j) (base j) (swaps j) ≤
      idleRecordOverhead p (Finset.univ.sup fixed) (Finset.univ.sup base) (Finset.univ.sup swaps) := by
    unfold idleRecordOverhead
    gcongr <;> exact Finset.le_sup (Finset.mem_univ j)
  intro js distinct
  exact (paid js distinct).trans (Nat.add_le_add_left (Nat.add_le_add_right localBound _) _)

end IntegerMultBounds.MathlibTM2.M6.BitNode
