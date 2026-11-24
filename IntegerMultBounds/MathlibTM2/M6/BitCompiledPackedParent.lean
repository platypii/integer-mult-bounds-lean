module

public import IntegerMultBounds.MathlibTM2.M6.BitSeededIdleParent

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open IntervalDescriptor
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

/-- Charged execution on a loadable parent seed. -/
def PackedParentRun (U : Type) (Q : ℕ) {Config : Type} (input : Config → CutoffNodeInput)
    (price : Config → ℕ) : Prop :=
    ∃ (A : Type) (T : ℕ) (host : A → Pr A T Q prime U), ∃ (code : Pr A T Q prime U) (src dst : Fin (142081+2) ↪ Fin T) (seed : Config → Stacks T prime), LoadsPackedSeed (nodeSeedWords ∘ input) (CutoffNodeInput.cells ∘ input) seed ∧
      ∀ (c : Config), let p := input c
      PackedPieceHandoffWithCharge cleanupWeight p.cells (packedChildOutput (p.w+1) p.cells)
        host code src dst (seed c) (price c)

/-- After removing ranks at most seven, only nine owners in window six remain. -/
private theorem largeRemainders (i : Fin 9) :
    ((remainderRanks i).filter (7 < ·)) = if i = 6 then List.replicate 9 42 else [] := by
  rw [remainderRanks_eq.1 i i.isLt]
  revert i
  decide +kernel

/-- In the cutoff band the only possible active idle calls are the nine rank-42
owners per replica and class. Above the band every idle call is stopped. -/
theorem idleWindowCutoffCharge (p : CutoffNodeInput) (i : Fin 9) (charge : ℕ)
    (small : 7*(p.w+1) ≤ p.cutoff) :
    160*((remainderRanks i).map (fun r => if p.cutoff < r*(p.w+1) then charge else 0)).sum =
      if i = 6 ∧ p.cutoff < 42*(p.w+1) then 1440*charge else 0 := by
  let price := fun r => if p.cutoff < r*(p.w+1) then charge else 0
  have discard (rs : List ℕ) : (rs.map price).sum = ((rs.filter (7 < ·)).map price).sum := by
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      by_cases large : 7 < r
      · simp [large,ih]
      · have stop := (Nat.mul_le_mul_right (p.w+1) (Nat.le_of_not_gt large)).trans small
        have zero : price r = 0 := ite_eq_right (Nat.not_lt_of_ge stop)
        simp [large,zero,ih]
  change 160*((remainderRanks i).map price).sum = _
  rw [discard,largeRemainders]
  by_cases h : i = 6 <;> by_cases active : p.cutoff < 42*(p.w+1) <;>
    simp [h,active,price]
  omega

/-- Work at the parent, including all window wrappers and the final tape assembly. -/
noncomputable def compiledParentLocal (p : CutoffNodeInput) (work : Fin 9 → ℕ → ℕ → ℕ)
    (init fixed base swaps : Fin 9 → ℕ) (assemble : ℕ) : ℕ :=
  (∑ i, work i (p.w+1) p.cells) +
    (∑ i, (init i*p.cells+735*p.cells+1+(142081*(10*p.cells+10)+1) +
      160*((remainderRanks i).map (fun r => if p.cutoff < r*(p.w+1) then
        idleRecordOverhead p (fixed i) (base i) (swaps i) else 0)).sum)) +
    assemble*p.cells+2

/-- Near the cutoff, the complete parent pays at most one window's active
routing tariff. Its coefficient counts exactly the live owners. -/
theorem compiledParentLocal_cutoff (p : CutoffNodeInput) (work : Fin 9 → ℕ → ℕ → ℕ)
    (init fixed base swaps : Fin 9 → ℕ) (assemble : ℕ) (small : 7*(p.w+1) ≤ p.cutoff) :
    compiledParentLocal p work init fixed base swaps assemble =
      (∑ i, work i (p.w+1) p.cells) +
      (∑ i, (init i*p.cells+735*p.cells+1+(142081*(10*p.cells+10)+1))) +
      (if p.cutoff < 42*(p.w+1) then 1440*idleRecordOverhead p (fixed 6) (base 6) (swaps 6) else 0) +
      assemble*p.cells+2 := by
  unfold compiledParentLocal
  simp_rw [idleWindowCutoffCharge p _ _ small]
  rw [Finset.sum_add_distrib]
  by_cases active : p.cutoff < 42*(p.w+1) <;> simp [active,Nat.add_assoc]

noncomputable def compiledParentCharge [M8.Machine.Net] (p : CutoffNodeInput)
    (work : Fin 9 → ℕ → ℕ → ℕ) (init fixed base swaps : Fin 9 → ℕ) (assemble : ℕ)
    (time : ℕ → ℕ) : ℕ :=
  compiledParentLocal p work init fixed base swaps assemble + ∑ i : Fin nodeChildren5.length, time i.val

private theorem phaseChildRank_le (n : Fin 9) (run : StageRun) (j : MoveIndex) :
    nodeChildren5[(phaseChildPositions.choose (n,run,j)).val] ≤ 7 := by
  rw [(phaseChildPositions.choose_spec n run j).1]
  let edges := Geometry.Moves.phaseEdges.filter positiveMove
  let e := edges[j.val]
  have edge := List.mem_filter.mp (List.getElem_mem (l := edges) (n := j.val) j.isLt)
  have mem : Geometry.moveRank e.1 e.2 ∈ Geometry.Moves.phaseEdges.map (fun p => Geometry.moveRank p.1 p.2) :=
    List.mem_map.mpr ⟨e,edge.1,rfl⟩
  rw [Geometry.Moves.phase_ranks] at mem
  have paid := BitOccurrences.phase_perm.mem_iff.mp (List.mem_filter.mpr ⟨mem,by simpa [positiveMove,e] using edge.2⟩)
  exact (show ∀ r ∈ Layer.SelectedMoments.expand BitOccurrences.phaseHist, r ≤ 7 by decide +kernel) _ paid

/-- Every sweep invocation stops once seven atoms fit under the cutoff. -/
theorem sweepChildWidth_le (p : CutoffNodeInput) (n : Fin 9) (run : StageRun) {l r : ℕ}
    (pre : Fin l → MoveIndex) (post : Fin r → MoveIndex) (j : Fin 3)
    (k : Fin (invocationCounts l r j)) :
    (scheduledChild prime p.node (invocationChildren n run pre post j k)).width ≤ 7*(p.w+1) := by
  change nodeChildren5[_]*(p.node.width/64) ≤ _
  rw [p.width,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
  apply Nat.mul_le_mul_right
  fin_cases j
  · exact phaseChildRank_le n run (pre k)
  · exact (copyChildPosition_rank n run.1 run.2 k).le
  · exact phaseChildRank_le n run (post k)

/-- Execute every sweep and remainder of a parent using their scheduled child calls. -/
theorem compiledPackedParent [M8.Machine.Net] (P U Config : Type) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let I := Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)
    ∃ (pre : Fin 9 → StageRun → Fin l → MoveIndex) (post : Fin 9 → StageRun → Fin r → MoveIndex),
    let sweepChild := fun (n : Fin 9) (i : I) => invocationChildren n i.1 (pre n i.1) (post n i.1) i.2.1 i.2.2
    ∃ (ts : Fin 9 → I → ℕ) (states : ℕ) (ports : ∀ n i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts n i)),
    ∀ {Q : ℕ}, states ≤ Q →
    ∀ {R : Type} {N : ℕ} {tree : R → Pr R N Q prime U} {dst : Fin (142081+2) ↪ Fin N} {leafRate : ℝ}
      {permits : {c : CutoffNodeInput // c.cutoff < c.node.width} → ℕ → ℕ → Prop},
    RecordTreeFamily Subtype.val tree dst leafRate permits →
    ∃ sweepRate : ℝ, ∀ (large : ∀ n i, P → Pr (WorkerLabel P) (ts n i) Q prime U) (f : Fin 9 → I → P),
    ∃ body : ∀ n i, WorkerLabel P → Pr (WorkerLabel P) (ts n i) Q prime U,
    (∀ n i g, body n i (.active g) = large n i g) ∧
    ∃ work : Fin 9 → ℕ → ℕ → ℕ,
    (∀ n, ∃ C : ℝ, ∀ w V : ℕ, 0 < w → 0 < V → (work n w V : ℝ) ≤
      C*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)) ∧
    ∃ (init fixed base swaps : Fin 9 → ℕ) (minimum : ℝ) (leaf : Fin 9 → ℝ) (assemble : ℕ),
    0 ≤ minimum ∧ (∀ i, 0 ≤ leaf i) ∧ ∀ D, minimum ≤ D →
    ∀ (input : Config → CutoffNodeInput) (blocks : Config → ℕ),
    (∀ c, (input c).root.Positive) → (∀ c, 142080^((input c).depth+1) ∣ (input c).root.rows) →
    (∀ c, (input c).root.beforeH = blocks c*prime^(64*(input c).root.width)) →
    let child := fun (c : Config) (i : Fin 9) (j : Fin idleCopies.length) => scheduledChild prime (input c).node (idleDirectoryIndex (i,j))
    let fuel := fun (c : Config) => (input c).depth-((input c).path.length+1)
    (∀ c i j, let p := input c; p.cutoff < (child c i j).width →
      ∀ (x : {v : CutoffNodeInput // v.cutoff < v.node.width}),
        x.val.root = p.root → x.val.path = p.path++[idleDirectoryIndex (i,j)] → x.val.cutoff = p.cutoff →
        ∀ k : Fin nodeChildren5.length, let d := scheduledChild prime (child c i j) k
        p.cutoff < d.width → permits x k.val (cutoffTreeBudget D leafRate p.cutoff (fuel c-1) d)) →
    let desc := fun (c : Config) (n : Fin 9) (i : I) => scheduledChild prime (input c).node (sweepChild n i)
    ∃ position : ∀ c n i, Fin (volume prime (desc c n i)) ≃ Fin ((prime^((input c).w+1))^16*(input c).stageWidth),
    (∀ c n i, invocationCoordinates i.2.1 ((input c).w+1) (input c).stageWidth (position c n i)) ∧
    ∀ rate : ℝ, sweepRate ≤ rate →
    let budget := fun c (i : ℕ) => if h : i < nodeChildren5.length then
      cutoffTreeBudget D leafRate (input c).cutoff (fuel c) (scheduledChild prime (input c).node ⟨i,h⟩) else 0
    let time := fun (c : Config) => stageBranchTime (input c).node (input c).cutoff rate (budget c)
    (∀ c n i, let v := input c
      v.cutoff < 7*(v.w+1) → v.cutoff < (desc c n i).width →
      if i.2.1 = 1 then ScheduledChildExec v.node (desc c n i) v.w v.stageWidth (ports n i) (binSyms v.root.width.size v.cutoff)
        (position c n i) (body n i) (.active (f n i)) (budget c (sweepChild n i).val) true
      else MoveOnBankExec v.node (desc c n i) v.w v.stageWidth (movePrefix.trans (ports n i)) (binSyms v.root.width.size v.cutoff)
        (position c n i) (body n i) (large n i (f n i)) (budget c (sweepChild n i).val) true) →
    let price := fun c => compiledParentCharge (input c) work init fixed base swaps assemble (time c)
    PackedParentRun U Q input price ∧
    ∀ c, let p := input c
      p.cutoff < p.node.width →
      (compiledParentLocal p work init fixed base swaps assemble : ℝ) ≤
        D*((volume prime p.node : ℝ)*(p.node.width : ℝ)^M8.Machine.BudgetBound.tau) →
      price c ≤ cutoffTreeBudget D (max leafRate rate) p.cutoff (fuel c+1) p.node ∧
      (7*(p.w+1) ≤ p.cutoff →
        price c ≤ cutoffBandBudget D (max leafRate rate) p.cutoff (min (fuel c+1) 6) p.node) := by
  classical
  intro l r I
  have stages := flatDispatchedHandoff
  dsimp only at stages
  choose pre post ts states ports rates build using stages
  obtain ⟨q,parent⟩ := assembledIdleParent (U := U) (Config := Config)
  refine ⟨pre,post,ts,max (Finset.univ.sup states) q,ports,?_⟩
  intro Q capacity R N tree dst leafRate permits family
  obtain ⟨init,fixed,base,swaps,minimum,leaf,assemble,nonneg,pos,join⟩ :=
    parent ((Nat.le_max_right ..).trans capacity) family
  refine ⟨max (Finset.univ.sup' Finset.univ_nonempty rates) (Finset.univ.sup' Finset.univ_nonempty leaf),?_⟩
  intro large f
  choose body active tapes src out host code work seed load bound step using fun n => build n
    ((Finset.le_sup (Finset.mem_univ n)).trans ((Nat.le_max_left ..).trans capacity)) (large n) (f n)
  refine ⟨body,active,work,bound,init,fixed,base,swaps,minimum,leaf,assemble,nonneg,pos,?_⟩
  intro D enough input blocks root rows label child fuel children desc
  choose position coords runs using fun c n => step n (input c)
  refine ⟨position,coords,?_⟩
  intro rate rateBound budget time recurse price
  constructor
  rotate_left
  · intro c p active localBound
    have bound := cutoffDirectoryCharge_le p _ D leafRate rate _ (fuel c) active
      (le_max_left _ _) (le_max_right _ _) localBound
    exact ⟨bound,fun band => bound.trans_eq (cutoffTreeBudget_band _ _ _ p band)⟩
  let branch : Config → Fin 9 → Fin idleCopies.length → ℕ := fun (c : Config) (i : Fin 9) (j : Fin idleCopies.length) => let p := input c; if p.cutoff < (child c i j).width then
      idleRecordOverhead p (fixed i) (base i) (swaps i)+cutoffTreeBudget D leafRate p.cutoff (fuel c) (child c i j)
      else ⌊leaf i*((child c i j).width : ℝ)^M8.Machine.BudgetBound.tau*volume prime (child c i j)⌋₊
  let idleCost : Config → Fin 9 → ℕ := fun (c : Config) (i : Fin 9) => let V := (input c).cells
                              init i*V+(735*V+(∑ j, branch c i j)+1)+(142081*(10*V+10)+1)
  let sweepCost : Config → Fin 9 → ℕ := fun (c : Config) (n : Fin 9) => work n ((input c).w+1) (input c).cells+((List.range' (stageChildStart n)
      (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map (time c)).sum
  obtain ⟨A,T,host,program,src,dst,initial,load,physical⟩ := join D enough input blocks root rows label children sweepCost (by
    intro n
    refine ⟨_,tapes n,host n,code n,src n,out n,_,nodeSweepLoader input (load n),?_⟩
    intro c
    have run := runs c n (budget c) rate ((Finset.le_sup' rates (Finset.mem_univ n)).trans ((le_max_left _ _).trans rateBound)) (fun i active =>
      recurse c n i (active.trans_le (sweepChildWidth_le _ _ _ _ _ _ _)) active)
    exact stageCast n (input c).stageTail _ (work n ((input c).w+1)) run)
  refine ⟨A,T,host,program,src,dst,initial,load,?_⟩
  intro c p x u S words fresh
  obtain ⟨z,F,t,y,exec,paid,user,out,effect⟩ := physical c x u S words fresh
  refine ⟨z,F,t,y,exec,?_,user,out,effect⟩
  intro js distinct
  apply (paid js distinct).trans
  apply Nat.add_le_add_left
  let overhead := fun (i : Fin 9) (w : ℕ) => if p.cutoff < w then
    idleRecordOverhead p (fixed i) (base i) (swaps i) else 0
  have each (i : Fin 9) (j : Fin idleCopies.length) :
      branch c i j ≤ overhead i (child c i j).width + time c (idleDirectoryIndex (i,j)).val := by
    let k := idleDirectoryIndex (i,j)
    change _ ≤ overhead i (scheduledChild prime p.node k).width + stageBranchTime p.node p.cutoff rate (budget c) k.val
    simp only [stageBranchTime,dite_eq_left k.isLt]
    by_cases active : p.cutoff < (scheduledChild prime p.node k).width
    · simp only [branch,child,p,k,active,ite_eq_left,budget,dite_eq_left,Fin.is_lt,overhead] at *
      rfl
    · have leafBound := (Finset.le_sup' leaf (Finset.mem_univ i)).trans ((le_max_right _ _).trans rateBound)
      have h := Nat.floor_mono (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right leafBound (Real.rpow_nonneg (Nat.cast_nonneg (scheduledChild prime p.node k).width) M8.Machine.BudgetBound.tau))
        (Nat.cast_nonneg (volume prime (scheduledChild prime p.node k))))
      dsimp only [p,k] at active
      simp only [branch,child,p,k,ite_eq_right active]
      exact h.trans (Nat.le_add_left _ _)
  have windows := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => each i j))
  simp only [Finset.sum_add_distrib] at windows
  have partition := nodeChildDirectoryBill (time c)
  dsimp only [price,sweepCost,idleCost,compiledParentCharge,compiledParentLocal]
  simp only [Finset.sum_add_distrib]
  simp only [child,idleWindowWidthSum] at windows
  dsimp only [overhead,p,branch,child,fuel] at windows
  omega


end IntegerMultBounds.MathlibTM2.M6.BitNode
