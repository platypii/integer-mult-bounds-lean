module

public import IntegerMultBounds.MathlibTM2.M6.BitCorrectionSchedule

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout
open Shared50ModularControl (prime)

private theorem callerSeed_from_headers {k H T : ℕ} (fan : Fin (k+1) ↪ Fin H)
    (outer : Fin (H+37) ↪ Fin T) (S : Stacks T prime) (word : List (Fin (prime+4)))
    (external : Fin 37 → List (Fin (prime+4))) :
    let core := (Fin.castAddEmb 37).trans outer
    let header := (Fin.natAddEmb H (m := 37)).trans outer
    S.L (core (fan (Fin.last k))) = [] → S.R (core (fan (Fin.last k))) = word →
    (∀ j, (∀ i, fan i ≠ j) → S.L (core j) = [] ∧ S.R (core j) = []) →
    (∀ i, S.L (header i) = [] ∧ S.R (header i) = external i) →
    PrivateTapes ((Fin.castAddEmb 1).trans (fan.trans (Fin.castAddEmb 37))) (callerSeed fan word external) (embStk outer S) := by
  intro core header left cutoff vacant headers j
  induction j using Fin.addCases with
  | right i =>
    intro _
    change S.L (header i) = [] ∧ S.R (header i) = Fin.append _ external (i.natAdd H)
    rw [Fin.append_right]
    exact headers i
  | left j =>
    intro off
    by_cases eq : j = fan (Fin.last k)
    · subst j
      change S.L (core (fan (Fin.last k))) = [] ∧ S.R (core (fan (Fin.last k))) =
        Fin.append (Function.update (fun _ => []) (fan (Fin.last k)) word) external ((fan (Fin.last k)).castAdd 37)
      rw [Fin.append_left,Function.update_self]
      exact ⟨left,cutoff⟩
    · have away (i) : fan i ≠ j := by
        induction i using Fin.lastCases with
        | last => exact Ne.symm eq
        | cast i => exact fun h => off i (congrArg (Fin.castAdd 37) h)
      change S.L (core j) = [] ∧ S.R (core j) =
        Fin.append (Function.update (fun _ => []) (fan (Fin.last k)) word) external (j.castAdd 37)
      rw [Fin.append_left,Function.update_of_ne eq]
      exact vacant j away

/-- Execute the corrected stage from descriptor, cutoff and chart words.
Stopped occurrences are installed locally; only larger children require induction. -/
theorem dispatchedCorrectedStage [M8.Machine.Net] (n : Fin 9) :
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
    ∃ (H : ℕ) (fan : Fin (k+1) ↪ Fin H) (space : ℕ)
      (table : I × WorkerLabel P → Pr (I × WorkerLabel P) (H+37) Q prime U),
    let inner := (Fin.castAddEmb 1).trans (fan.trans (Fin.castAddEmb 37))
    ∀ {T : ℕ} (mid : Fin (H+37) ↪ Fin T) (entry ret : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (caller : Fin 6 ↪ Fin T),
    (∀ i j, entry i ≠ mid j) → (∀ i j, ret i ≠ mid j) → (∀ i j, caller i ≠ mid j) →
    (∀ i j, entry i ≠ caller j) → (∀ i j, ret i ≠ caller j) → (∀ i j, ret i ≠ entry j) →
    let outer := mid.trans (Fin.castAddEmb (24+space))
    let host := fun f => embProg outer id (table f)
    ∃ code, ∃ (rate : ℝ) (a b : ℕ), ∀ c : CutoffNodeInput,
    let w := c.w+1
    let V := (prime^w)^16*c.stageWidth
    let desc := fun i => scheduledChild prime c.node (child i)
    ∃ position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V,
    (∀ i, invocationCoordinates i.2.1 w c.stageWidth (position i)) ∧
    ∀ (budget : ℕ → ℕ) (childRate : ℝ), leafRate ≤ childRate →
    let time := stageBranchTime c.node c.cutoff childRate budget
    (∀ i, c.cutoff < (desc i).width →
      if i.2.1 = 1 then ScheduledChildExec c.node (desc i) c.w c.stageWidth (ports i) (binSyms c.root.width.size c.cutoff)
        (position i) (body i) (.active (f i)) (budget (child i).val) true
      else MoveOnBankExec c.node (desc i) c.w c.stageWidth (movePrefix.trans (ports i)) (binSyms c.root.width.size c.cutoff)
        (position i) (body i) (large i (f i)) (budget (child i).val) true) →
    let core := (Fin.castAddEmb 37).trans outer
    let header := (Fin.natAddEmb H (m := 37)).trans outer
    ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan (inner.trans outer) x S →
      S.L (core (fan (Fin.last k))) = [] → S.R (core (fan (Fin.last k))) = binSyms c.root.width.size c.cutoff →
      (∀ j, (∀ i, fan i ≠ j) → S.L (core j) = [] ∧ S.R (core j) = []) →
      (∀ i, S.L (header i) = [] ∧ S.R (header i) =
        callerHeaderBank (fun j => (Routines.hdr c.node j).map (bitSymbol (a := prime))) i) →
      S.R ((caller 0).castAdd _) = binSyms (prime^w).size (prime^w) →
      S.R ((caller 1).castAdd _) = binSyms c.stageWidth.size c.stageWidth →
      S.R ((caller 2).castAdd _) = binSyms 1 1 → S.R ((caller 3).castAdd _) = binSyms w.size w →
      S.R ((caller 4).castAdd _) = [] → S.R ((caller 5).castAdd _) = [] →
      (∀ i, i.val ≠ 24 → S.L ((entry i).castAdd _) = [] ∧ S.R ((entry i).castAdd _) = []) →
      (∀ i, i.val ≠ 24 → S.L ((ret i).castAdd _) = [] ∧ S.R ((ret i).castAdd _) = []) →
      (∀ j : Fin (24+space), S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (a*V+b*LeafCore.coreCost V w+⌈rate*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)⌉₊+
          ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum) ∧
        HelperFan (inner.trans outer) y F ∧ ∀ (b : Fin c.B) (t : Fin c.stageFactor) (g : LabelPadding.Label 64 w),
          borrowedStageRead n b t g y = (Piece.stage n).run (borrowedStageRead n b t g x) := by
  classical
  intro l r I k
  obtain ⟨pre,post,ts,states,ports,leafRate,build⟩ := dispatchedRestoredWorker n
  obtain ⟨chartStates,space,chart⟩ := correctedFanWorker n
  refine ⟨pre,post,ts,max states chartStates,ports,leafRate,?_⟩
  intro P U Q cap large f
  obtain ⟨body,active,H,fan,table,worker,rate,stage⟩ := build ((Nat.le_max_left ..).trans cap) large f
  refine ⟨body,active,H,fan,space,table,?_⟩
  intro innerFan T' mid entry ret caller ea ra ca ec rc re outer host
  obtain ⟨code,a,b,combine⟩ := chart table worker innerFan mid entry ret caller
    ((Nat.le_max_right ..).trans cap) le_rfl ea ra ca ec rc re
  refine ⟨code,rate,a,b,?_⟩
  intro c w V desc
  obtain ⟨position,coords,run⟩ := stage c
  refine ⟨position,coords,?_⟩
  intro budget childRate enough time recurse
  let word := binSyms (A := prime) c.root.width.size c.cutoff
  let words := fun i => (Routines.hdr c.node i).map (bitSymbol (a := prime))
  let external := callerHeaderBank words
  let initial := callerSeed fan word external
  let kids := ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum
  let fee := rate*((V : ℝ)*(w : ℝ)^M8.Machine.BudgetBound.tau)
  have hb : 0 < c.B := Nat.pos_of_mul_pos_right (c.label ▸ c.stagePositive.2.2.1)
  have hk : 0 < c.stageFactor := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos c.stagePositive.1 c.stagePositive.2.1)
    c.stagePositive.2.2.2.1) c.stagePositive.2.2.2.2
  have invoke := combine c.w c.B c.stageFactor (by
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hb)
      (pow_pos Shared50ModularControl.prime_prime.pos _)) hk) (⌈fee⌉₊+kids) initial (run budget childRate enough recurse)
  intro core header x u S live left cutoff vacant headers modulus count unit prec tmp saved entryFree retFree free
  have fresh := callerSeed_from_headers fan outer S word external left cutoff vacant headers
  obtain ⟨z,F,t,y,exec,user,bill,out,act⟩ := invoke x u S live fresh modulus count unit prec tmp saved entryFree retFree free
  refine ⟨z,F,t,y,exec,user,?_,out,act⟩
  change CleanupBound S F t (a*V+b*LeafCore.coreCost V w+(⌈fee⌉₊+kids)) at bill
  simpa only [Nat.add_assoc] using bill

end IntegerMultBounds.MathlibTM2.M6.BitNode
