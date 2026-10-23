module

public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationWord

/-! Load arbitrary metadata words with a caller-chosen delimiter. This permits
embedded binary delimiters while retaining the complete rewind archive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def configurationDelimiter (src saved : Fin T) (delimiter : Fin (A + 4)) : Act T Q A U :=
  .pop (.rt src) (fun v _ => v) (.push (.rt saved) (fun _ => delimiter) .done)

def delimitedConfigurationLoad (src dst tmp saved : Fin T) (delimiter : Fin (A + 4)) (p : Fin (A + 4) → Bool)
    (header : Bool) : Pr P T Q A U :=
  .seq (configurationScan src tmp saved p)
    (.seq (.act (configurationDelimiter src saved delimiter))
      (.seq (moveR tmp dst id) (.act (MetadataJob.copyFinish dst header))))

def delimitedConfigurationLoaded (R : Fin T → List (Fin (A + 4))) (src dst tmp saved : Fin T) (delimiter : Fin (A + 4))
    (word rest : List (Fin (A + 4))) (header : Bool) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update R src rest) tmp [])
    saved (delimiter :: (word.reverse ++ R saved))) dst ((if header then [separator] else []) ++ word)

/-- Load a word with its complete frame and exact linear cost. The raw input is
preserved in the rewind archive, including the consumed delimiter. -/
theorem delimitedConfigurationLoad_exec (body : P → Pr P T Q A U) (src dst tmp saved : Fin T)
    (hst : src ≠ tmp) (hss : src ≠ saved) (hts : tmp ≠ saved)
    (hsd : src ≠ dst) (htd : tmp ≠ dst) (had : saved ≠ dst)
    (delimiter : Fin (A + 4)) (p : Fin (A + 4) → Bool) (hsep : p delimiter = false) (header : Bool)
    (word rest : List (Fin (A + 4))) (hword : ∀ x ∈ word, p x = true)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = word ++ delimiter :: rest) (htmp0 : S.R tmp = []) (hdst0 : S.R dst = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (delimitedConfigurationLoad src dst tmp saved delimiter p header) (mk v S) (4 * word.length + 6)
        (mk v' { S with R := delimitedConfigurationLoaded S.R src dst tmp saved delimiter word rest header }) := by
  let S₁ : Stacks T A := { S with R := configurationScanned S.R src tmp saved word (delimiter :: rest) }
  obtain ⟨v₁, hu₁, he₁⟩ := configurationScan_exec body src tmp saved hst hss hts p word
    (delimiter :: rest) hword (by simp [hsep]) v S hsrc
  let S₂ : Stacks T A := { S₁ with R := Function.update (Function.update S₁.R src rest) saved (delimiter :: S₁.R saved) }
  have hrun : (configurationDelimiter src saved delimiter : Act T Q A U).run (mk v₁ S₁) = mk v₁ S₂ := by
    simp [configurationDelimiter, Action.run, update_rt, S₂, S₁, configurationScanned,
      Function.update_of_ne hss, Function.update_of_ne hst, Function.update_of_ne hss.symm]
  have ht : S₂.R tmp = word.reverse := by
    simp [S₂, S₁, configurationScanned, htmp0, Function.update_of_ne hts,
      Function.update_of_ne hst.symm]
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tmp dst htd id v₁ S₂
  let S₃ : Stacks T A := { S₂ with R := movedR S₂.R tmp dst id (S₂.R tmp) }
  have hfinish : (MetadataJob.copyFinish dst header : Act T Q A U).run (mk v₂ S₃) =
      mk v₂ { S₃ with R := Function.update S₃.R dst ((if header then [separator] else []) ++ S₃.R dst) } := by
    cases header <;> simp [MetadataJob.copyFinish, Action.run, update_rt]
  have hfinal : Function.update S₃.R dst ((if header then [separator] else []) ++ S₃.R dst) =
      delimitedConfigurationLoaded S.R src dst tmp saved delimiter word rest header := by
    funext j
    by_cases h₁ : j = src <;> by_cases h₂ : j = dst <;>
      by_cases h₃ : j = tmp <;> by_cases h₄ : j = saved <;>
      simp_all [S₃, S₂, S₁, movedR, configurationScanned, delimitedConfigurationLoaded]
  refine ⟨v₂, hu₂.trans hu₁, ?_⟩
  have he := Exec.seq he₁ (Exec.seq (hrun ▸ Exec.act (body := body) (configurationDelimiter src saved delimiter) (mk v₁ S₁))
    (Exec.seq he₂ (hfinish ▸ Exec.act (body := body) (MetadataJob.copyFinish dst header) (mk v₂ S₃))))
  refine Exec.cast he (by rw [ht, List.length_reverse]; omega) ?_
  congr 2

end IntegerMultBounds.MathlibTM2.Routing
