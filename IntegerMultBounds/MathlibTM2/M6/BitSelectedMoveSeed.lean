module

public import IntegerMultBounds.MathlibTM2.M6.BitScalarMoveSequence
public import IntegerMultBounds.MathlibTM2.M6.BitWorkerSeedSequence

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback Certificates.PR589
open Shared50ModularControl (prime)

/-- Prepare the MOVE banks of a stage in directory order, for either side of COPY. -/
theorem selectedMoveStageSeed [M8.Machine.Net] (n : Fin 9) (afterCopy : Bool) :
    let count := (selectedPhaseSchedule afterCopy).1.length
    let I := (Fin 32 × Fin 5) × Fin count
    ∃ (ts qs : I → ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts i))
      (fan : ∀ i, Fin (142081+2) ↪ Fin (ts i)) (layout : ∀ i, WorkerBasisLayout (ports i)),
      (∀ i : I, SelectedMoveWindow (⟨ownerTape n i.1.1 i.1.2,ownerTape_injective ..⟩) n i.1 (selectedPhaseIndex afterCopy i.2) (ts i) (qs i) (ports i) (fan i) (layout i)) ∧
    ∀ {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
      (bank : ∀ i, Fin (ts i+1) ↪ Fin T) (caller : Fin 6 ↪ Fin T),
    let privateSlot := fun i j => ∀ h, withCutoffPort (fan i) h ≠ j
    (∀ i l s, bank i l ≠ caller s) →
    (∀ i l, privateSlot i l → ∀ m, m ≠ i → ∀ j, bank m j ≠ bank i l) →
    ∃ code, ∀ w W u (S : Stacks T prime), let M := prime^(w+1)
      0 < W → S.R (caller 0) = binSyms M.size M → S.R (caller 1) = binSyms W.size W →
      S.R (caller 2) = binSyms 1 1 → S.R (caller 3) = binSyms (w+1).size (w+1) →
      S.R (caller 4) = [] → S.R (caller 5) = [] →
      (∀ i j, privateSlot i j → S.L (bank i j) = [] ∧ S.R (bank i j) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (178*(160*count)*(M^16*W)+1) ∧
        (∀ i j, privateSlot i j → ∀ record, let seed := cutoffWorkerSeed ((layout i).seed w W record)
          F.L (bank i j) = seed.L j ∧ F.R (bank i j) = Function.update seed.R ((scheduledRecordPorts (ports i) 34).castAdd 1) [] j) ∧
        ∀ j, (∀ i l, privateSlot i l → bank i l ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro count I
  let order := stageRuns.product (List.finRange count)
  classical
  choose ts qs ports fan layout owned window using fun i : I => invocationMoveLayout (k := 142081) ⟨ownerTape n i.1.1 i.1.2,ownerTape_injective ..⟩ n i.1 (selectedPhaseIndex afterCopy i.2)
  refine ⟨ts,qs,ports,fan,layout,window,?_⟩
  intro P U T Q body bank caller priv away apart
  let localBank (i : I) : Fin (ts i) ↪ Fin T := (Fin.castAddEmb 1).trans (bank i)
  obtain ⟨code,run⟩ := loadStageWorkerSeeds body ts ports layout localBank fan caller
    (fun i l => away i (l.castAdd 1)) order (stageRuns_nodup.product (List.nodup_finRange _)) owned
    (fun i l off m ne j => apart i (l.castAdd 1) ((withCutoffPort_private_cast _ _).mpr off) m ne (j.castAdd 1))
  refine ⟨code,?_⟩
  intro w W u S M pos modulus spectator unit atom ht hs blank
  obtain ⟨z,F,t,exec,user,paid,stock,frame⟩ := run w W u S pos modulus spectator unit atom ht hs (fun i _ j off => blank i (j.castAdd 1) ((withCutoffPort_private_cast _ _).mpr off))
  have member (i : I) : i ∈ order := List.mem_product.mpr ⟨mem_stageRuns i.1,List.mem_finRange i.2⟩
  have length : order.length = 160*count := by
    apply (List.length_product stageRuns (List.finRange count)).trans
    rw [stageRuns_length,List.length_finRange]
  rw [length] at paid
  refine ⟨z,F,t,exec,user,paid,?_,fun j off => frame j (fun i _ l priv =>
    off i (l.castAdd 1) ((withCutoffPort_private_cast _ _).mpr priv))⟩
  intro i j
  induction j using Fin.lastCases with
  | last => exact fun outside => False.elim (outside _ (withCutoffPort_cut _))
  | cast j =>
    intro outside record
    have ready := stock i (member i) j ((withCutoffPort_private_cast _ _).mp outside) record
    change F.L (bank i (j.castAdd 1)) = (cutoffWorkerSeed _).L (j.castAdd 1) ∧
      F.R (bank i (j.castAdd 1)) = Function.update (cutoffWorkerSeed _).R
        ((scheduledRecordPorts (ports i) 34).castAdd 1) [] (j.castAdd 1)
    by_cases eq : j = scheduledRecordPorts (ports i) 34
    · subst j
      simpa only [localBank,Function.Embedding.trans_apply,Fin.coe_castAddEmb,cutoffWorkerSeed,Fin.append_left,Function.update_self] using ready
    · have ne : j.castAdd 1 ≠ (scheduledRecordPorts (ports i) 34).castAdd 1 := (Fin.castAddEmb 1).injective.ne eq
      simpa only [localBank,Function.Embedding.trans_apply,Fin.coe_castAddEmb,cutoffWorkerSeed,Fin.append_left,Function.update_of_ne eq,
        Function.update_of_ne ne,Fin.coe_castAddEmb] using ready

end IntegerMultBounds.MathlibTM2.M6.BitNode
