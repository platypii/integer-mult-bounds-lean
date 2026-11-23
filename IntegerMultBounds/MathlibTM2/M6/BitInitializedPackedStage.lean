module

public import IntegerMultBounds.MathlibTM2.M6.BitInitializedRestoredStage
public import IntegerMultBounds.MathlibTM2.M6.BitChargedChartWorker

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

/-- The packed stage returns the selected word on every spectator row. Its
local cost is independent of the recursive budgets. -/
theorem initializedPackedStage [M8.Machine.Net] (n : Fin 9) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let I := Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)
    let k := 142081+2
    ∃ (pre : StageRun → Fin l → MoveIndex) (post : StageRun → Fin r → MoveIndex),
    let child := fun i : I => invocationChildren n i.1 (pre i.1) (post i.1) i.2.1 i.2.2
    ∃ (ts : I → ℕ) (states : ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts i)),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (body : ∀ i, P → Pr P (ts i) Q prime U) (f : I → P),
    ∃ (T : ℕ) (src dst : Fin k ↪ Fin T) (host : I × P → Pr (I × P) T Q prime U)
      (code : Pr (I × P) T Q prime U) (localCost : ℕ → ℕ → ℕ),
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
    ∃ seed, PackedPieceHandoffWithCharge cleanupWeight V (fun x y => ∀ j : Fin W,
      let address := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
      readRoles address y = (Piece.stage n).run (readRoles address x)) host code src dst seed
      (localCost w V+((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum) := by
  intro l r I k
  obtain ⟨pre,post,ts,states,ports,build⟩ := initializedRestoredStage n
  obtain ⟨C,base,tapes,chartStates,chart⟩ := borrowedFlatHandoffWithCharge
  refine ⟨pre,post,ts,max states chartStates,ports,?_⟩
  intro P U Q cap body f
  obtain ⟨T,owners,_,_,host,worker,rate,stage⟩ := build ((Nat.le_max_left ..).trans cap) body f
  let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)).trans (Fin.natAddEmb 80)
  let fan := owners.trans owner
  let data := (Fin.castAddEmb 1 (n := k)).trans fan
  obtain ⟨H,outer,code,src,dst,pack⟩ := chart n data host worker ((Nat.le_max_right ..).trans cap)
  let overhead := fun w V => 13*((base*V+17760*(2*LeafCore.coreCost V w+14))*(tapes+5)+12)
  let localCost := fun (w V : ℕ) => overhead w V+⌈rate*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)⌉₊+
    ⌈C*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊+(142081*(10*V+10)+1)
  refine ⟨H,src,dst,outer,code,localCost,?_,?_⟩
  · obtain ⟨D,bound⟩ := stageSetupCost_bound base tapes
    refine ⟨13*D+|rate|+|C|+142081*20+3,?_⟩
    intro w V hw hv
    let power := (w : ℝ)^M8.Machine.BudgetBound.tau
    let scale := (V : ℝ)*power
    have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast hw) M8.Machine.BudgetBound.exponent_range.1.le
    have vol : (V : ℝ) ≤ scale := le_mul_of_one_le_right (Nat.cast_nonneg _) one
    have unit : 1 ≤ scale := (show (1 : ℝ) ≤ V by exact_mod_cast hv).trans vol
    have ceil (a : ℝ) : (⌈a*scale⌉₊ : ℝ) ≤ |a| *scale+1 := by
      apply (Nat.cast_le.mpr (Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_abs_self a) (zero_le_one.trans unit)))).trans
      exact (Nat.ceil_lt_add_one (mul_nonneg (abs_nonneg _) (zero_le_one.trans unit))).le
    have small : overhead w V ≤ 13*stageSetupCost base tapes V w := by
      apply Nat.mul_le_mul_left
      unfold stageSetupCost
      omega
    have h : (overhead w V : ℝ) ≤ 13*(D*scale) := by
      have setup := bound V w hv hw
      rw [mul_assoc] at setup
      exact (Nat.cast_le.mpr small).trans (by push_cast; exact mul_le_mul_of_nonneg_left setup (by norm_num))
    dsimp only [localCost]
    rw [mul_assoc C]
    change ((overhead w V+⌈rate*scale⌉₊+⌈C*scale⌉₊+(142081*(10*V+10)+1) : ℕ) : ℝ) ≤ _*scale
    push_cast
    linarith only [h,ceil rate,ceil C,vol,unit]
  intro c w V desc record
  obtain ⟨position,_,_,coords,prepare⟩ := stage c
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
  obtain ⟨seed,handoff⟩ := pack (w := w) (B := c.B) (K := c.stageFactor) (⌈fee⌉₊+kids) initial
    (Nat.succ_pos _) hb hk (by
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
  have price : localCost w V+kids = overhead w V+(⌈fee⌉₊+kids)+
      ⌈C*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊+(142081*(10*V+10)+1) := by
    dsimp only [localCost,fee]
    omega
  rw [price]
  exact handoff

end IntegerMultBounds.MathlibTM2.M6.BitNode
