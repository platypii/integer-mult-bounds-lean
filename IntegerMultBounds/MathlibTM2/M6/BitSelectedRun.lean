module

public import IntegerMultBounds.MathlibTM2.M6.BitCutoffNode
public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedSweep
import IntegerMultBounds.MathlibTM2.M6.BitPackedSweepCharge

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Cover
open Shared50ModularControl (prime)
open Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

/-- Execute one selected invocation, retaining the initialized private tapes of every sibling. -/
theorem selectedRunWithCharge {P U : Type} {T Q k : ℕ} (n : Fin 9) (w B K : ℕ) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let J := Σ j : Fin 3, Fin (invocationCounts l r j)
    let I := Σ _ : StageRun, J
    let xs := (List.finRange 3).sigma fun j => List.finRange (invocationCounts l r j)
    let X := Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2
    ∀ (tapes : I → ℕ) (ports : ∀ i, Fin k ↪ Fin (tapes i)) (fan : Fin k ↪ Fin T)
      (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    (∀ i j, bank i (ports i j) = fan j) →
    (∀ i l, (∀ j, ports i j ≠ l) → ∀ m, m ≠ i → ∀ j, bank m j ≠ bank i l) →
    ∀ (body : ∀ i, P → Pr P (tapes i) Q prime U) (worker : ∀ i, Pr P (tapes i) Q prime U)
      (rep : X → Stacks k prime → Prop) (cost : I → ℕ) (seed : ∀ i, Stacks (tapes i) prime),
    let saved := fun (p : StageRun) (S : Stacks T prime) => ∀ j : J,
      PrivateTapes (ports ⟨p,j⟩) (seed ⟨p,j⟩) (embStk (bank ⟨p,j⟩) S)
    let effect := fun i : I => selectedOccurrenceEffect n w B K i.1 i.2.1 i.2.2
    (∀ i x u S, rep x (embStk (ports i) S) → PrivateTapes (ports i) (seed i) S →
      ∃ z F t y, Exec (body i) (worker i) (mk u S) t (mk z F) ∧ CleanupBound S F t (cost i) ∧
        z.user = u.user ∧ rep y (embStk (ports i) F) ∧ effect i x y) →
    let host := fun g : I × P => embProg (bank g.1) (Prod.mk g.1) (body g.1 g.2)
    ∀ p x u S, let order := xs.map (fun j : J => (⟨p,j⟩ : I))
      saved p S → rep x (embStk fan S) →
      ∃ z F t y, Exec host (Prog.seqList (order.map fun i => embProg (bank i) (Prod.mk i) (worker i)))
        (mk u S) t (mk z F) ∧ CleanupBound S F t ((order.map cost).sum+1) ∧ z.user = u.user ∧
        rep y (embStk fan F) ∧ BorrowedStep n w B K p x y ∧ ∀ q, q ≠ p → saved q S → saved q F := by
  intro l r J I xs X tapes ports fan bank aligned apart body worker rep cost seed saved effect run host
  intro p x u S order stock ready
  have distinct : xs.Nodup := (List.nodup_finRange 3).sigma fun _ => List.nodup_finRange _
  have unique : order.Nodup := distinct.map (fun _ _ h => by cases h; rfl)
  obtain ⟨z,F,t,y,exec,bill,user,out,frame,trace⟩ := runPlacedScheduleWithCharge tapes ports fan bank
    aligned apart body worker cleanupWeight rep effect cost seed run order unique x u S ready (by
      intro i mem
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp mem
      exact stock j)
  refine ⟨z,F,t,y,exec,bill,user,out,selectedRunEffect n w B K p x y ?_,?_⟩
  · apply (orderedEffects_sigma (List.finRange 3) (fun j => List.finRange (invocationCounts l r j))
      (fun j : J => effect ⟨p,j⟩) x y).mp
    simpa only [order,List.foldr_map,Function.comp_def,OrderedEffects] using trace
  · intro q ne other j l off
    obtain ⟨a,b⟩ := frame (bank ⟨q,j⟩ l) (by
      intro i mem
      obtain ⟨h,_,rfl⟩ := List.mem_map.mp mem
      exact apart _ l off _ (fun eq => ne (congrArg Sigma.fst eq).symm))
    obtain ⟨c,d⟩ := other j l off
    exact ⟨a.trans c,b.trans d⟩

/-- Pack each selected invocation on entry and restore the helper labels after the last run. -/
theorem selectedRestoredSweep [M8.Machine.Net] {P U : Type} {T Q : ℕ} (n : Fin 9) (capacity : columnCapacity ≤ Q) :
    let l := (selectedPhaseSchedule false).1.length
    let r := (selectedPhaseSchedule true).1.length
    let J := Σ j : Fin 3, Fin (invocationCounts l r j)
    let I := Σ _ : StageRun, J
    let xs := (List.finRange 3).sigma fun j => List.finRange (invocationCounts l r j)
    let k := 142081+2
    ∀ (tapes : I → ℕ) (ports : ∀ i, Fin (k+1) ↪ Fin (tapes i)) (shared : Fin (k+1) ↪ Fin T)
      (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    (∀ i j, bank i (ports i j) = shared j) →
    (∀ i l, (∀ j, ports i j ≠ l) → ∀ m, m ≠ i → ∀ j, bank m j ≠ bank i l) →
    ∀ (body : ∀ i, P → Pr P (tapes i) Q prime U) (worker : ∀ i, Pr P (tapes i) Q prime U),
    let host := fun g : I × P => embProg (bank g.1) (Prod.mk g.1) (body g.1 g.2)
    let scratch := Fin.castAddEmb LeafCore.small (n := T+273)
    let owner := (Fin.castAddEmb 273 (n := T)).trans scratch
    let fan := (Fin.castAddEmb 1 (n := k)).trans shared
    ∃ rate : ℝ, ∃ code, ∀ w B K : ℕ,
    let blocks := (prime^w)^112*B
    let W := B*prime^(64*(w*64))*K
    let V := (prime^w)^16*(blocks*prime^(64*(w*64))*K)
    0 < V → ∀ (cost : I → ℕ) (seed : ∀ i, Stacks (tapes i) prime) (word : List (Fin (prime+4))),
    let rep := fun (x : Fin 142081 → Fin V → ZMod 2) (D : Stacks (k+1) prime) =>
      HelperFan (Fin.castAddEmb 1) x D ∧ D.R (Fin.last k) = word
    (∀ i x u D, rep x (embStk (ports i) D) → PrivateTapes (ports i) (seed i) D →
      ∃ z F t y, Exec (body i) (worker i) (mk u D) t (mk z F) ∧ CleanupBound D F t (cost i) ∧
        z.user = u.user ∧ rep y (embStk (ports i) F) ∧ selectedOccurrenceEffect n w blocks K i.1 i.2.1 i.2.2 x y) →
    ∀ x u S, HelperFan (fan.trans owner) x S →
      (∀ i j, S.R (scratch (borrowedHeaders T i j)) = (Routines.hdr (helperAdjacentView w 1 W i) j).map bitSymbol) →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd (T+273)) = [] ∧ S.R (j.natAdd (T+273)) = []) →
      S.R (owner (shared (Fin.last k))) = word →
      (∀ i, PrivateTapes (ports i) (seed i) (embStk ((bank i).trans owner) S)) →
      ∃ z F t out, Exec (fun f => embProg owner id (host f)) code (mk u S) t (mk z F) ∧
        (∀ js : List _, js.Nodup → (t : ℝ)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
          rate*((V : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)+
          ((stageRuns.map fun p => (xs.map fun j => cost ⟨p,j⟩).sum+1).sum : ℕ)) ∧
        z.user = u.user ∧ HelperFan (fan.trans owner) out F ∧ RestoredBorrowedStage n w B K x out := by
  intro l r J I xs k tapes ports shared bank aligned apart body worker host scratch owner fan
  let order (p : StageRun) := xs.map fun j => (⟨p,j⟩ : I)
  let call (p : StageRun) := Prog.seqList ((order p).map fun i => embProg (bank i) (Prod.mk i) (worker i))
  obtain ⟨rate,build⟩ := archivedSweepWithCharge n fan capacity host
  obtain ⟨code,stage⟩ := build call
  refine ⟨rate,code,?_⟩
  intro w B K blocks W V positive cost seed word rep run x u S live headers free cut stock
  let saved (p : StageRun) (D : Stacks T prime) := D.R (shared (Fin.last k)) = word ∧
    ∀ j : J, PrivateTapes (ports ⟨p,j⟩) (seed ⟨p,j⟩) (embStk (bank ⟨p,j⟩) D)
  let price (p : StageRun) := (xs.map fun j => cost ⟨p,j⟩).sum+1
  apply stage w B K positive saved price _ x u S live headers free (fun p => ⟨cut,fun j => stock ⟨p,j⟩⟩)
  intro p S previous a v D data unchanged
  have cutReady : D.R (shared (Fin.last k)) = word := by
    apply Eq.trans _ previous.1
    exact (unchanged _ (fun h eq => ne_of_lt h.castSucc_lt_last (shared.injective eq))).2
  have carry (q) (h : saved q S) (j : J) :
      PrivateTapes (ports ⟨q,j⟩) (seed ⟨q,j⟩) (embStk (bank ⟨q,j⟩) D) := by
    intro l off
    obtain ⟨a,b⟩ := unchanged (bank ⟨q,j⟩ l) (by
      intro i eq
      exact off (i.castAdd 1) ((bank ⟨q,j⟩).injective ((aligned _ _).trans eq)))
    obtain ⟨c,d⟩ := h.2 j l off
    exact ⟨a.trans c,b.trans d⟩
  obtain ⟨z,F,t,y,exec,bill,user,out,step,keep⟩ := selectedRunWithCharge n w blocks K tapes ports shared bank
    aligned apart body worker rep cost seed run p a v D (carry p previous) ⟨data,cutReady⟩
  exact ⟨z,F,t,y,exec,by intro js distinct; simpa only [order,List.map_map,Function.comp_def,price,xs,l,r] using bill js distinct,
    user,out.1,step,fun q ne h => ⟨out.2,keep q ne (carry q h)⟩⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
