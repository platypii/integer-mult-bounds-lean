module

public import IntegerMultBounds.MathlibTM2.M6.BitInitializedPackedStage
import IntegerMultBounds.MathlibTM2.M6.BitStageCallerLayout

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

private def callerSeed {k H : ℕ} (fan : Fin (k+1) ↪ Fin H) (cutoff : List (Fin (prime+4)))
    (external : Fin 37 → List (Fin (prime+4))) : Stacks (H+37) prime :=
  ⟨[],[],fun _ => [],Fin.append (Function.update (fun _ => []) (fan (Fin.last k)) cutoff) external⟩

private theorem callerSeed_ready {k H : ℕ} (fan : Fin (k+1) ↪ Fin H) (cutoff : List (Fin (prime+4)))
    (external : Fin 37 → List (Fin (prime+4))) (S : Stacks (H+37) prime) :
    let place := Fin.castAddEmb 37 (n := H)
    let data := (Fin.castAddEmb 1 (n := k)).trans fan
    PrivateTapes (data.trans place) (callerSeed fan cutoff external) S →
    (∀ i : Fin 37, S.R (i.natAdd H) = external i) ∧
    (∀ j, (∀ i, fan i ≠ j) → S.L (place j) = [] ∧ S.R (place j) = []) ∧
    S.R (place (fan (Fin.last k))) = cutoff := by
  intro place data fresh
  refine ⟨?_,?_,?_⟩
  · intro i
    have h := fresh (i.natAdd H) (fun j eq => by
      have val := congrArg Fin.val eq
      change (data j).val = H+i.val at val
      have := (data j).isLt
      omega)
    simpa only [callerSeed,Fin.append_right] using h.2
  · intro j off
    have h := fresh (place j) (fun i => place.injective.ne (off (i.castAdd 1)))
    simpa only [callerSeed,place,Fin.coe_castAddEmb,Fin.append_left,Function.update_of_ne (off _).symm] using h
  · have h := fresh (place (fan (Fin.last k))) (fun i eq =>
      ne_of_lt i.castSucc_lt_last (fan.injective (place.injective eq)))
    simpa only [callerSeed,place,Fin.coe_castAddEmb,Fin.append_left,Function.update_self] using h.2

private theorem helperFan_trans {k V H M : ℕ} (fan : Fin (k+2) ↪ Fin H) (place : Fin H ↪ Fin M)
    (x : Fin k → Fin V → ZMod 2) (S : Stacks M prime) :
    HelperFan (fan.trans place) x S ↔ HelperFan fan x (embStk place S) := Iff.rfl

/-- Install stopped-leaf dispatch in each selected occurrence. Only the active
children require recursive execution contracts. -/
theorem dispatchedPackedStage [M8.Machine.Net] (n : Fin 9) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let I := Σ _ : StageRun, Σ j : Fin 3, Fin (invocationCounts l r j)
    let k := 142081+2
    ∃ (pre : StageRun → Fin l → MoveIndex) (post : StageRun → Fin r → MoveIndex),
    let child := fun i : I => invocationChildren n i.1 (pre i.1) (post i.1) i.2.1 i.2.2
    ∃ (ts : I → ℕ) (states : ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts i)),
    ∃ leafRate : ℝ, ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (large : ∀ i, P → Pr (WorkerLabel P) (ts i) Q prime U) (f : I → P),
    ∃ body : ∀ i, WorkerLabel P → Pr (WorkerLabel P) (ts i) Q prime U, (∀ i g, body i (.active g) = large i g) ∧
    ∃ (T : ℕ) (src dst : Fin k ↪ Fin T) (host : I × WorkerLabel P → Pr (I × WorkerLabel P) T Q prime U)
      (code : Pr (I × WorkerLabel P) T Q prime U) (localCost : ℕ → ℕ → ℕ),
    (∃ D : ℝ, ∀ w V : ℕ, 0 < w → 0 < V → (localCost w V : ℝ) ≤
      D*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)) ∧ ∀ c : CutoffNodeInput,
    let w := c.w+1
    let V := (prime^w)^16*c.stageWidth
    let desc := fun i => scheduledChild prime c.node (child i)
    ∃ position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V,
    (∀ i, invocationCoordinates i.2.1 w c.stageWidth (position i)) ∧
    ∀ (budget : ℕ → ℕ) (rate : ℝ), leafRate ≤ rate →
    let time := stageBranchTime c.node c.cutoff rate budget
    (∀ i, c.cutoff < (desc i).width →
      if i.2.1 = 1 then ScheduledChildExec c.node (desc i) c.w c.stageWidth (ports i) (binSyms c.root.width.size c.cutoff)
        (position i) (body i) (.active (f i)) (budget (child i).val) true
      else MoveOnBankExec c.node (desc i) c.w c.stageWidth (movePrefix.trans (ports i)) (binSyms c.root.width.size c.cutoff)
        (position i) (body i) (large i (f i)) (budget (child i).val) true) →
    let W := c.B*prime^(64*(w*64))*c.stageFactor
    let size : (prime^w)^128*W = V :=
      (ordinaryCompact_width _ _).symm.trans (by simp [V,W,CutoffNodeInput.stageWidth,Nat.mul_assoc,w])
    ∃ seed, PackedPieceHandoffWithCharge cleanupWeight V (fun x y => ∀ j : Fin W,
      let address := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
      readRoles address y = (Piece.stage n).run (readRoles address x)) host code src dst seed
      (localCost w V+((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum) := by
  classical
  intro l r I k
  obtain ⟨pre,post,ts,states,ports,leafRate,build⟩ := callerRestoredStage n
  obtain ⟨C,base,tapes,chartStates,chart⟩ := borrowedFlatHandoffWithCharge
  refine ⟨pre,post,ts,max states chartStates,ports,leafRate,?_⟩
  intro P U Q cap large f
  obtain ⟨body,active,T,shared,owners,banks,align,inner,rate,compile⟩ :=
    build ((Nat.le_max_left ..).trans cap) large f
  let H := 80+((T+273)+LeafCore.small)
  let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb LeafCore.small)).trans (Fin.natAddEmb 80)
  let archive := archiveSetupPlacement 80 T LeafCore.small
  let place := Fin.castAddEmb 37 (n := H)
  let fan := shared.trans owner
  let data := (Fin.castAddEmb 1 (n := k)).trans fan
  obtain ⟨source,r,power,tmp,saved,dimensions,division,input,quotientPort,divisionOff,divisionSafe,radixPort,unitPort,dimensionFrame,
    atomOff,atomPorts,privateDimensions,clockWidth,powerClock,clockOff,sourceSafe,placeSafe,tmpSafe,savedSafe,apart,regs⟩ :=
    stageCallerLayout owner archive (fun i => (archiveSetupPlacement_frame (R := 80) (T := T) (L := LeafCore.small) i).1)
  obtain ⟨worker,stage⟩ := compile place source r power tmp saved dimensions division
    quotientPort divisionOff divisionSafe radixPort unitPort dimensionFrame atomOff atomPorts privateDimensions
    clockWidth powerClock clockOff sourceSafe placeSafe tmpSafe savedSafe apart regs
  let table := fun f => embProg place id (inner f)
  obtain ⟨N,host,code,src,dst,pack⟩ := chart n (data.trans place) table worker ((Nat.le_max_right ..).trans cap)
  let overhead := fun w V => 13*((base*V+17760*(2*LeafCore.coreCost V w+14))*(tapes+5)+12)
  let localCost := fun (w V : ℕ) => overhead w V+⌈rate*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)⌉₊+
    ⌈C*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊+(142081*(10*V+10)+1)
  refine ⟨body,active,N,src,dst,host,code,localCost,packedStageCost_bound base tapes rate C,?_⟩
  intro c w V desc
  obtain ⟨position,_,_,coords,run⟩ := stage c
  refine ⟨position,coords,?_⟩
  intro budget childRate enough time recurse W size
  let word := binSyms (A := prime) c.root.width.size c.cutoff
  let words := fun i => (Routines.hdr c.node i).map (bitSymbol (a := prime))
  let external := callerHeaderBank words
  have externalReady := input words
  let initial := callerSeed fan word external
  let kids := ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum
  let fee := rate*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)
  have hb : 0 < c.B := Nat.pos_of_mul_pos_right (c.label ▸ c.stagePositive.2.2.1)
  have hk : 0 < c.stageFactor := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos c.stagePositive.1 c.stagePositive.2.1)
    c.stagePositive.2.2.2.1) c.stagePositive.2.2.2.2
  obtain ⟨seed,handoff⟩ := pack (w := w) (B := c.B) (K := c.stageFactor) (⌈fee⌉₊+kids) initial
    (Nat.succ_pos _) hb hk (by
      intro x u S live fresh
      obtain ⟨readExt,empty,cutoff⟩ := callerSeed_ready fan word external S fresh
      obtain ⟨headers,clocks,temps,ht,hs,divide,atom,t₄,t₅⟩ := externalReady S.R readExt
      have invoke := run budget childRate enough recurse
      have start := invoke x u S ((helperFan_trans data place x S).mp live) cutoff headers clocks temps
      have prepared := start (fun j => empty (archive j) (fun i => ((archiveSetupPlacement_frame (R := 80) (T := T) (L := LeafCore.small) j).1 (shared i)).symm))
        ht hs divide atom t₄ t₅
      obtain ⟨z,F,t,y,exec,bill,user,out,done⟩ := prepared
        (fun i l priv => empty (owner (banks i l)) (fun h eq => priv h ((banks i).injective
          ((align i h).trans (owner.injective eq)))))
        (fun j off _ => empty j (fun i => off (shared i)))
      refine ⟨z,F,t,y,exec,?_,user,(helperFan_trans data place y F).mpr out,done⟩
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
