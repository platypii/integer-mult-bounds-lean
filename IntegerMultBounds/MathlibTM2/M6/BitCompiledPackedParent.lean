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

noncomputable def packedParentPrice {Config : Type} (input : Config → CutoffNodeInput)
    (sweep idle : Config → Fin 9 → ℕ) (assemble : ℕ) (c : Config) : ℕ :=
  (∑ i, sweep c i)+(∑ i, idle c i)+assemble*(input c).cells+2

/-- Execute every sweep and remainder of a parent using their scheduled child calls. -/
theorem compiledPackedParent [M8.Machine.Net] (P U Config R : Type) {N : ℕ} :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let I := Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)
    ∃ (pre : Fin 9 → StageRun → Fin l → MoveIndex) (post : Fin 9 → StageRun → Fin r → MoveIndex),
    let sweepChild := fun (n : Fin 9) (i : I) => invocationChildren n i.1 (pre n i.1) (post n i.1) i.2.1 i.2.2
    ∃ (ts : Fin 9 → I → ℕ) (states : ℕ) (ports : ∀ n i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts n i)),
    ∀ {Q : ℕ}, states ≤ Q →
    ∀ {tree : R → Pr R N Q prime U} {dst : Fin (142081+2) ↪ Fin N} {leafRate : ℝ}
      {childBudget : {c : CutoffNodeInput // c.cutoff < c.node.width} → ℕ → ℕ},
    SplitRecordTreeFamily Subtype.val tree dst leafRate childBudget →
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
        p.cutoff < d.width → childBudget x k.val ≤ cutoffTreeBudget D leafRate p.cutoff (fuel c-1) d) →
    let branch : Config → Fin 9 → Fin idleCopies.length → ℕ := fun (c : Config) (i : Fin 9) (j : Fin idleCopies.length) => let p := input c; if p.cutoff < (child c i j).width then
      idleRecordOverhead p (fixed i) (base i) (swaps i)+cutoffTreeBudget D leafRate p.cutoff (fuel c) (child c i j)
      else ⌊leaf i*((child c i j).width : ℝ)^M8.Machine.BudgetBound.tau*volume prime (child c i j)⌋₊
    let idleCost : Config → Fin 9 → ℕ := fun (c : Config) (i : Fin 9) => let V := (input c).cells
                              init i*V+(735*V+(∑ j, branch c i j)+1)+(142081*(10*V+10)+1)
    let desc := fun (c : Config) (n : Fin 9) (i : I) => scheduledChild prime (input c).node (sweepChild n i)
    ∃ position : ∀ c n i, Fin (volume prime (desc c n i)) ≃ Fin ((prime^((input c).w+1))^16*(input c).stageWidth),
    (∀ c n i, invocationCoordinates i.2.1 ((input c).w+1) (input c).stageWidth (position c n i)) ∧
    ∀ (budget : Config → ℕ → ℕ) (rate : ℝ), sweepRate ≤ rate →
    let time := fun (c : Config) => stageBranchTime (input c).node (input c).cutoff rate (budget c)
    (∀ c n i, let v := input c
      v.cutoff < (desc c n i).width →
      if i.2.1 = 1 then ScheduledChildExec v.node (desc c n i) v.w v.stageWidth (ports n i) (binSyms v.root.width.size v.cutoff)
        (position c n i) (body n i) (.active (f n i)) (budget c (sweepChild n i).val) true
      else MoveOnBankExec v.node (desc c n i) v.w v.stageWidth (movePrefix.trans (ports n i)) (binSyms v.root.width.size v.cutoff)
        (position c n i) (body n i) (large n i (f n i)) (budget c (sweepChild n i).val) true) →
    let sweepCost : Config → Fin 9 → ℕ := fun (c : Config) (n : Fin 9) => work n ((input c).w+1) (input c).cells+((List.range' (stageChildStart n)
      (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map (time c)).sum
    PackedParentRun U Q input (packedParentPrice input sweepCost idleCost assemble) := by
  classical
  intro l r I
  have stages := flatDispatchedHandoff
  dsimp only at stages
  choose pre post ts states ports rates build using stages
  obtain ⟨q,parent⟩ := assembledIdleParent (P := R) (U := U) (Config := Config) (N := N)
  refine ⟨pre,post,ts,max (Finset.univ.sup states) q,ports,?_⟩
  intro Q capacity tree dst leafRate childBudget family
  obtain ⟨init,fixed,base,swaps,minimum,leaf,assemble,nonneg,pos,join⟩ :=
    parent ((Nat.le_max_right ..).trans capacity) family
  refine ⟨Finset.univ.sup' Finset.univ_nonempty rates,?_⟩
  intro large f
  choose body active tapes src out host code work seed load bound step using fun n => build n
    ((Finset.le_sup (Finset.mem_univ n)).trans ((Nat.le_max_left ..).trans capacity)) (large n) (f n)
  refine ⟨body,active,work,bound,init,fixed,base,swaps,minimum,leaf,assemble,nonneg,pos,?_⟩
  intro D enough input blocks root rows label child fuel children branch idleCost desc
  choose position coords runs using fun c n => step n (input c)
  refine ⟨position,coords,?_⟩
  intro budget rate rateBound time recurse sweepCost
  apply join D enough input blocks root rows label children sweepCost
  intro n
  refine ⟨_,tapes n,host n,code n,src n,out n,_,nodeSweepLoader input (load n),?_⟩
  intro c
  have run := runs c n (budget c) rate ((Finset.le_sup' rates (Finset.mem_univ n)).trans rateBound) (recurse c n)
  exact stageCast n (input c).stageTail _ (work n ((input c).w+1)) run

end IntegerMultBounds.MathlibTM2.M6.BitNode
