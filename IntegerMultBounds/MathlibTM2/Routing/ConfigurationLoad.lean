module

public import IntegerMultBounds.MathlibTM2.Routing.DelimitedConfigurationLoad

/-!
# Load one framed metadata word into a reusable register

Consume its trailing separator into the right-stack archive, reverse the scanned
word into the destination, and optionally add the leading separator required by
interchange headers. Every left stack remains unchanged, so host interchanges
can run between loads. No code depends on the loaded word's length or value.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def configurationSeparator (src saved : Fin T) : Act T Q A U :=
  .pop (.rt src) (fun v _ => v) (.push (.rt saved) (fun _ => separator) .done)

def configurationLoad (src dst tmp saved : Fin T) (p : Fin (A + 4) → Bool)
    (header : Bool) : Pr P T Q A U :=
  .seq (configurationScan src tmp saved p)
    (.seq (.act (configurationSeparator src saved))
      (.seq (moveR tmp dst id) (.act (MetadataJob.copyFinish dst header))))

def configurationLoaded (R : Fin T → List (Fin (A + 4))) (src dst tmp saved : Fin T)
    (word rest : List (Fin (A + 4))) (header : Bool) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update R src rest) tmp [])
    saved (separator :: (word.reverse ++ R saved))) dst ((if header then [separator] else []) ++ word)

/-- Load a word with its complete frame and exact linear cost. The raw input is
preserved in the rewind archive, including the consumed separator. -/
theorem configurationLoad_exec (body : P → Pr P T Q A U) (src dst tmp saved : Fin T)
    (hst : src ≠ tmp) (hss : src ≠ saved) (hts : tmp ≠ saved)
    (hsd : src ≠ dst) (htd : tmp ≠ dst) (had : saved ≠ dst)
    (p : Fin (A + 4) → Bool) (hsep : p separator = false) (header : Bool)
    (word rest : List (Fin (A + 4))) (hword : ∀ x ∈ word, p x = true)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = word ++ separator :: rest) (htmp0 : S.R tmp = []) (hdst0 : S.R dst = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (configurationLoad src dst tmp saved p header) (mk v S) (4 * word.length + 6)
        (mk v' { S with R := configurationLoaded S.R src dst tmp saved word rest header }) := by
  exact delimitedConfigurationLoad_exec body src dst tmp saved hst hss hts hsd htd had
    separator p hsep header word rest hword v S hsrc htmp0 hdst0

end IntegerMultBounds.MathlibTM2.Routing
