module

public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankReady

/-! One reusable-bank call: load metadata, execute a stream-only program, erase
metadata. The uniform loop can reuse this boundary without accumulating tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def delimitedBankCall (src tmp saved : Fin T) (delimiter : Fin (A + 4))
    (p : Fin (A + 4) → Bool) (destinations : List (Fin T)) (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (delimitedBankLoad src tmp saved delimiter p destinations)
    (.seq call (metadataClean destinations))

theorem delimitedBankCall_exec (body : P → Pr P T Q A U)
    (src tmp saved str : Fin T) (hreg : [src, tmp, saved].Nodup)
    (delimiter : Fin (A + 4)) (p : Fin (A + 4) → Bool) (hstop : p delimiter = false)
    (jobs : List (Fin T × List (Fin (A + 4)))) (hdistinct : (jobs.map Prod.fst).Nodup)
    (hseparate : ∀ j ∈ jobs, j.1 ≠ src ∧ j.1 ≠ tmp ∧ j.1 ≠ saved)
    (hstr : str ∉ jobs.map Prod.fst)
    (hword : ∀ j ∈ jobs, ∀ x ∈ j.2, p x = true)
    (rest output : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = delimitedBankFrames delimiter jobs ++ rest)
    (htmp : S.R tmp = []) (hblank : ∀ j ∈ jobs, S.R j.1 = [])
    (call : Pr P T Q A U) (C : ℝ)
    (hcall : ∀ u : HS T Q A U,
      let G : Stacks T A := { S with R := delimitedBankLoaded src tmp saved delimiter rest jobs S.R }
      ∃ (u' : HS T Q A U) (steps : ℕ), u'.user = u.user ∧ (steps : ℝ) ≤ C ∧
        Exec body call (mk u G) steps (mk u' { G with R := Function.update G.R str output })) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ C + (6 * (delimitedBankFrames delimiter jobs).length + 2 * jobs.length + 2 : ℕ) ∧
      Exec body (delimitedBankCall src tmp saved delimiter p (jobs.map Prod.fst) call)
        (mk v S) steps
        (mk v' { S with R := Function.update (Function.update (Function.update S.R src rest) saved
          ((delimitedBankFrames delimiter jobs).reverse ++ S.R saved)) str output }) := by
  let G : Stacks T A := { S with R := delimitedBankLoaded src tmp saved delimiter rest jobs S.R }
  obtain ⟨v₁, hu₁, hx₁⟩ := delimitedBankLoad_exec body src tmp saved hreg delimiter p hstop jobs
    hdistinct hseparate hword rest v S hsrc htmp hblank
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := hcall v₁
  let H : Stacks T A := { G with R := Function.update G.R str output }
  obtain ⟨v₃, hu₃, hx₃⟩ := metadataClean_exec body (jobs.map Prod.fst) hdistinct v₂ H
  have hcost : metadataCleanCost H.R (jobs.map Prod.fst) =
      2 * (delimitedBankFrames delimiter jobs).length + 1 := by
    apply metadataCleanCost_framed
    intro job hj
    have hne : job.1 ≠ str := by
      intro he
      exact hstr (List.mem_map.mpr ⟨job, hj, he⟩)
    dsimp only [H]
    rw [Function.update_of_ne hne]
    exact delimitedBankLoaded_at src tmp saved delimiter rest jobs hdistinct hseparate job hj S.R
  have hfinal : metadataCleared H.R (jobs.map Prod.fst) =
      Function.update (Function.update (Function.update S.R src rest) saved
        ((delimitedBankFrames delimiter jobs).reverse ++ S.R saved)) str output := by
    dsimp only [H, G]
    rw [metadataCleared_update _ _ str output hstr,
      delimitedBankLoaded_clean src tmp saved hreg delimiter rest jobs hseparate S.R hsrc htmp hblank]
  rw [hcost, hfinal] at hx₃
  refine ⟨v₃, delimitedBankLoadCost jobs + (m₂ + (2 * (delimitedBankFrames delimiter jobs).length + 1)),
    hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩
  rw [delimitedBankLoadCost_frames delimiter]
  push_cast
  linarith

end IntegerMultBounds.MathlibTM2.Routing
