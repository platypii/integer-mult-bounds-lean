module

public import IntegerMultBounds.MathlibTM2.M6.BitInitializedChartWorker

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

/-- The initialized outer charts surround the actual restored stage. Recursive
budgets enter once, through the selected stage's list of paid children. -/
theorem preparedPackedStage [M8.Machine.Net] (n : Fin 9) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let I := Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)
    let k := 142081+2
    ∃ (pre : StageRun → Fin l → MoveIndex) (post : StageRun → Fin r → MoveIndex),
    let child := fun i : I => invocationChildren n i.1 (pre i.1) (post i.1) i.2.1 i.2.2
    ∃ (ts : I → ℕ) (states : ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts i)),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (body : ∀ i, P → Pr P (ts i) Q prime U) (f : I → P),
    ∃ (H T : ℕ) (place : Fin H ↪ Fin T) (fan : Fin k ↪ Fin H) (caller : Fin 6 ↪ Fin T)
      (host : I × P → Pr (I × P) T Q prime U) (code : Pr (I × P) T Q prime U) (localCost : ℕ → ℕ → ℕ),
    (∃ D : ℝ, ∀ w V : ℕ, 0 < w → 0 < V → (localCost w V : ℝ) ≤
      D*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)) ∧ ∀ c : CutoffNodeInput,
    let w := c.w+1
    let V := (prime^w)^16*c.stageWidth
    let desc := fun i => scheduledChild prime c.node (child i)
    let record := fun i : I => invocationWorkerRecord i.2.1 (desc i) c.root.width.size c.cutoff
    ∃ position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V,
    (∀ i, invocationCoordinates i.2.1 w c.stageWidth (position i)) ∧
    ∀ time : ℕ → ℕ, (∀ i, ScheduledChildExec c.node (desc i) c.w c.stageWidth (ports i) (record i)
      (position i) (body i) (f i) (time (child i).val) true) →
    let W := c.B*prime^(64*(w*64))*c.stageFactor
    let size : (prime^w)^128*W = V :=
      (ordinaryCompact_width _ _).symm.trans (by simp [V,W,CutoffNodeInput.stageWidth,Nat.mul_assoc,w])
    ∃ seed : Stacks H prime, ∀ x u S, HelperFan (fan.trans place) x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L (place j) = seed.L j ∧ S.R (place j) = seed.R j) →
      S.R (caller 0) = binSyms (prime^w).size (prime^w) → S.R (caller 1) = binSyms W.size W →
      S.R (caller 2) = binSyms 1 1 → S.R (caller 3) = binSyms w.size w →
      S.R (caller 4) = [] → S.R (caller 5) = [] →
      (∀ j, (∀ i, place i ≠ j) → (∀ i, caller i ≠ j) → S.L j = [] ∧ S.R j = []) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (localCost w V+((List.range' (stageChildStart n)
          (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum) ∧
        HelperFan (fan.trans place) y F ∧ ∀ j : Fin W,
          let address := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
          readRoles address y = (Piece.stage n).run (readRoles address x) := by
  intro l r I k
  obtain ⟨pre,post,ts,states,ports,_,_,_,build⟩ := initializedRestoredStage n
  obtain ⟨base,tapes,chartStates,chart⟩ := initializedBorrowedChartWorker n
  refine ⟨pre,post,ts,max states chartStates,ports,?_⟩
  intro P U Q cap body f
  obtain ⟨T,owners,_,_,_,host,worker,rate,stage⟩ := build ((Nat.le_max_left ..).trans cap) body f
  let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)).trans (Fin.natAddEmb 80)
  let fan := owners.trans owner
  let data := (Fin.castAddEmb 1 (n := k)).trans fan
  obtain ⟨H,R,mid,place,caller,C,code,execute⟩ := chart data host worker ((Nat.le_max_right ..).trans cap)
  let overhead := fun w V => 13*((base*V+17760*(2*LeafCore.coreCost V w+14))*(tapes+5)+12)
  let localCost := fun (w V : ℕ) => overhead w V+⌈rate*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)⌉₊+
    ⌈C*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊
  refine ⟨H,R,place,data.trans mid,caller,(fun f => embProg place id (embProg mid id (host f))),code,localCost,?_,?_⟩
  · obtain ⟨D,bound⟩ := packedStageCost_bound base tapes rate C
    refine ⟨D,fun w V hw hv => ?_⟩
    exact (Nat.cast_le.mpr (Nat.le_add_right (localCost w V) _)).trans (bound w V hw hv)
  intro c w V desc record
  obtain ⟨position,_,coords,prepare⟩ := stage c
  refine ⟨position,coords,?_⟩
  intro time recurse W size
  let word := binSyms (A := prime) c.root.width.size c.cutoff
  let shared : Stacks (k+1) prime := ⟨[],[],fun _ => [],fun _ => word⟩
  obtain ⟨stock,_,view,run⟩ := prepare shared
  let initial := stageSetupSeed LeafCore.small stock c
  let kids := ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum
  let fee := rate*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)
  have hb : 0 < c.B := Nat.pos_of_mul_pos_right (c.label ▸ c.stagePositive.2.2.1)
  have hk : 0 < c.stageFactor := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos c.stagePositive.1 c.stagePositive.2.1)
    c.stagePositive.2.2.2.1) c.stagePositive.2.2.2.2
  obtain ⟨seed,charted⟩ := execute c.w c.B c.stageFactor hb hk (⌈fee⌉₊+kids) initial (by
      intro x u S live fresh
      have cut := (fresh (fan (Fin.last k)) (fun i eq => ne_of_lt i.castSucc_lt_last (fan.injective eq))).2
      have saved := congrArg (fun D : Stacks (k+1) prime => D.R (Fin.last k)) view
      obtain ⟨z,F,t,y,exec,bill,user,out,done⟩ := run time recurse x u S live (cut.trans saved)
        (fun j off => fresh j (fun i => off (i.castAdd 1)))
      refine ⟨z,F,t,y,exec,?_,user,out,done⟩
      intro js nd
      have paid := bill js nd
      rw [← c.stageCells] at paid
      change (t : ℝ)+_ ≤ _+fee+(kids : ℝ) at paid
      exact_mod_cast (show (t : ℝ)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
        (((⌈fee⌉₊+kids : ℕ) : ℝ)) by push_cast; linarith only [paid,Nat.le_ceil fee]))
  refine ⟨seed,?_⟩
  intro x u S live fresh modulus spectators unit prec tmp saved vacant
  obtain ⟨z,F,t,y,exec,user,bill,out,done⟩ := charted x u S live fresh modulus spectators unit prec tmp saved vacant
  refine ⟨z,F,t,y,exec,user,?_,out,done⟩
  intro js nd
  have paid := bill js nd
  change (t : ℝ)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
    ((overhead w V+(⌈fee⌉₊+kids) : ℕ) : ℝ)+C*V*(w : ℝ)^M8.Machine.BudgetBound.tau at paid
  change t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+(localCost w V+kids)
  have round := Nat.le_ceil (C*V*(w : ℝ)^M8.Machine.BudgetBound.tau)
  have h : t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
      (overhead w V+(⌈fee⌉₊+kids)+⌈C*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊) := by
    exact_mod_cast (by push_cast at paid ⊢; linarith only [paid,round] :
      (t : ℝ)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
      ((overhead w V+(⌈fee⌉₊+kids)+⌈C*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊ : ℕ) : ℝ))
  have eq : localCost w V+kids = overhead w V+(⌈fee⌉₊+kids)+⌈C*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊ := by
    dsimp only [localCost,fee]
    ac_rfl
  rw [eq]
  exact h

end IntegerMultBounds.MathlibTM2.M6.BitNode
