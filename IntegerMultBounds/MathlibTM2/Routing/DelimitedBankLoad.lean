module

public import IntegerMultBounds.MathlibTM2.Routing.DelimitedConfigurationLoad

/-! Load a fixed bank from consecutive framed metadata words, sharing one scanner
and one archive. The program depends only on destination registers, not word data. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def delimitedBankFrames (delimiter : Fin (A + 4)) : List (Fin T × List (Fin (A + 4))) → List (Fin (A + 4))
  | [] => []
  | (_, word) :: jobs => word ++ delimiter :: delimitedBankFrames delimiter jobs

def delimitedBankLoad (src tmp saved : Fin T) (delimiter : Fin (A + 4))
    (p : Fin (A + 4) → Bool) : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | dst :: ds => .seq (delimitedConfigurationLoad src dst tmp saved delimiter p false)
      (delimitedBankLoad src tmp saved delimiter p ds)

def delimitedBankLoaded (src tmp saved : Fin T) (delimiter : Fin (A + 4))
    (rest : List (Fin (A + 4))) :
    List (Fin T × List (Fin (A + 4))) → (Fin T → List (Fin (A + 4))) → Fin T → List (Fin (A + 4))
  | [], R => R
  | (dst, word) :: jobs, R => delimitedBankLoaded src tmp saved delimiter rest jobs
      (delimitedConfigurationLoaded R src dst tmp saved delimiter word
        (delimitedBankFrames delimiter jobs ++ rest) false)

def delimitedBankLoadCost : List (Fin T × List (Fin (A + 4))) → ℕ
  | [] => 1
  | (_, word) :: jobs => 4 * word.length + 6 + delimitedBankLoadCost jobs

theorem delimitedBankLoad_exec (body : P → Pr P T Q A U)
    (src tmp saved : Fin T) (hreg : [src, tmp, saved].Nodup)
    (delimiter : Fin (A + 4)) (p : Fin (A + 4) → Bool) (hstop : p delimiter = false)
    (jobs : List (Fin T × List (Fin (A + 4)))) (hdistinct : (jobs.map Prod.fst).Nodup)
    (hseparate : ∀ j ∈ jobs, j.1 ≠ src ∧ j.1 ≠ tmp ∧ j.1 ≠ saved)
    (hword : ∀ j ∈ jobs, ∀ x ∈ j.2, p x = true)
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = delimitedBankFrames delimiter jobs ++ rest)
    (htmp : S.R tmp = []) (hblank : ∀ j ∈ jobs, S.R j.1 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (delimitedBankLoad src tmp saved delimiter p (jobs.map Prod.fst))
        (mk v S) (delimitedBankLoadCost jobs)
        (mk v' { S with R := delimitedBankLoaded src tmp saved delimiter rest jobs S.R }) := by
  have hn := hreg
  regs_ne hn
  induction jobs generalizing v S with
  | nil => exact ⟨v, rfl, Exec.act (body := body) .done (mk v S)⟩
  | cons job jobs ih =>
    obtain ⟨dst, word⟩ := job
    obtain ⟨hds, hdt, hda⟩ := hseparate (dst, word) (by simp)
    have hnd : (jobs.map Prod.fst).Nodup := (List.nodup_cons.mp hdistinct).2
    have hnot : dst ∉ jobs.map Prod.fst := (List.nodup_cons.mp hdistinct).1
    obtain ⟨v₁, hu₁, hx₁⟩ := delimitedConfigurationLoad_exec body src dst tmp saved
      ‹src ≠ tmp› ‹src ≠ saved› ‹tmp ≠ saved› hds.symm hdt.symm hda.symm
      delimiter p hstop false word (delimitedBankFrames delimiter jobs ++ rest)
      (hword (dst, word) (by simp)) v S
      (by simpa only [delimitedBankFrames, List.append_assoc, List.cons_append] using hsrc)
      htmp (hblank (dst, word) (by simp))
    let S₁ : Stacks T A := { S with R := delimitedConfigurationLoaded S.R src dst tmp saved delimiter word (delimitedBankFrames delimiter jobs ++ rest) false }
    have hkeep (j : Fin T × List (Fin (A + 4))) (hj : j ∈ jobs) : S₁.R j.1 = S.R j.1 := by
      obtain ⟨hjs, hjt, hja⟩ := hseparate j (by simp [hj])
      have hjd : j.1 ≠ dst := by
        intro he
        exact hnot (List.mem_map.mpr ⟨j, hj, he⟩)
      simp only [S₁, delimitedConfigurationLoaded, Function.update_of_ne hjs,
        Function.update_of_ne hjt, Function.update_of_ne hja, Function.update_of_ne hjd]
    obtain ⟨v₂, hu₂, hx₂⟩ := ih hnd
      (fun j hj => hseparate j (by simp [hj])) (fun j hj => hword j (by simp [hj]))
      v₁ S₁
      (by simp [S₁, delimitedConfigurationLoaded, hds.symm, ‹src ≠ tmp›, ‹src ≠ saved›])
      (by simp [S₁, delimitedConfigurationLoaded, hdt.symm, ‹tmp ≠ saved›])
      (fun j hj => (hkeep j hj).trans (hblank j (by simp [hj])))
    exact ⟨v₂, hu₂.trans hu₁, Exec.seq hx₁ hx₂⟩

end IntegerMultBounds.MathlibTM2.Routing
