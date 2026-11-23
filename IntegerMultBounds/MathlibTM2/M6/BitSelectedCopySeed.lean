module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedCall
public import IntegerMultBounds.MathlibTM2.M6.BitWorkerSeedSequence

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback Certificates.PR589
open Shared50ModularControl (prime)

/-- Initialize every selected COPY occurrence of a PR589 stage. Each execution
contract refers to the same layout and seed that the host program prepares. -/
theorem selectedCopyStageSeed [M8.Machine.Net] (n : Fin 9) :
    let I := (Fin 32 × Fin 5) × Fin Copy.lifecycles.length
    ∃ (ts qs : I → ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts i))
      (fan : ∀ i, Fin (142081+2) ↪ Fin (ts i)) (layout : ∀ i, WorkerBasisLayout (ports i)),
      (∀ i : I, SelectedCopyWindow true n i.1 i.2 (ts i) (qs i) (ports i) (fan i) (layout i)) ∧
    ∀ {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
      (bank : ∀ i, Fin (ts i) ↪ Fin T) (caller : Fin 6 ↪ Fin T),
    let privateSlot := fun i j => ∀ h, fan i h ≠ j
    (∀ i l s, bank i l ≠ caller s) →
    (∀ i l, privateSlot i l → ∀ m, m ≠ i → ∀ j, bank m j ≠ bank i l) →
    ∃ code, ∀ w W u (S : Stacks T prime), let M := prime^(w+1)
      0 < W → S.R (caller 0) = binSyms M.size M → S.R (caller 1) = binSyms W.size W →
      S.R (caller 2) = binSyms 1 1 → S.R (caller 3) = binSyms (w+1).size (w+1) →
      S.R (caller 4) = [] → S.R (caller 5) = [] →
      (∀ i j, privateSlot i j → S.L (bank i j) = [] ∧ S.R (bank i j) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (256320*(M^16*W)+1) ∧
        (∀ i j, privateSlot i j → ∀ record, let seed := (layout i).seed w W record
          F.L (bank i j) = seed.L j ∧ F.R (bank i j) = Function.update seed.R (scheduledRecordPorts (ports i) 34) [] j) ∧
        ∀ j, (∀ i l, privateSlot i l → bank i l ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro I
  let order := stageRuns.product (List.finRange Copy.lifecycles.length)
  classical
  choose ts qs ports fan layout owned window using fun i : I => borrowedWindow_layout true n i.1 i.2
  refine ⟨ts,qs,ports,fan,layout,window,?_⟩
  intro P U T Q body bank caller priv away apart
  obtain ⟨code,run⟩ := loadStageWorkerSeeds body ts ports layout bank fan caller away order
    (stageRuns_nodup.product (List.nodup_finRange _)) owned apart
  refine ⟨code,?_⟩
  intro w W u S M pos modulus spectator unit atom ht hs blank
  obtain ⟨z,F,t,exec,user,paid,stock,frame⟩ := run w W u S pos modulus spectator unit atom ht hs (fun i _ => blank i)
  have member (i : I) : i ∈ order := List.mem_product.mpr ⟨mem_stageRuns i.1,List.mem_finRange i.2⟩
  have count : order.length = 1440 := by
    apply (List.length_product stageRuns (List.finRange Copy.lifecycles.length)).trans
    rw [stageRuns_length,List.length_finRange,Copy.copy_count]
  rw [count] at paid
  exact ⟨z,F,t,exec,user,paid,fun i => stock i (member i),fun j off => frame j (fun i _ => off i)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
