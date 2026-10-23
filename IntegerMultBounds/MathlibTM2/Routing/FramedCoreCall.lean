module

public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreLayout
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedCallLoop

/-! Execute an embedded stream-only core from its complete framed input bank,
then erase that bank. Only three shared loader tapes lie outside the fixed core. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {N Q A : ℕ} {P P' U : Type}

def framedCoreCallProgram (str : Fin N) (delimiter : Fin (A + 4)) (scan : Fin (A + 4) → Bool)
    (ι : P → P') (core : Pr P N Q A U) : Pr P' (N + 3) Q A U :=
  delimitedBankCall (framedCoreAux N 0) (framedCoreAux N 1) (framedCoreAux N 2) delimiter scan
    (framedCoreDestinations (framedCoreEmbed N) str) (embProg (framedCoreEmbed N) ι core)

theorem framedCoreCall_exec (body : P → Pr P N Q A U)
    (outerBody : P' → Pr P' (N + 3) Q A U) (ι : P → P')
    (hbody : ∀ f, outerBody (ι f) = embProg (framedCoreEmbed N) ι (body f))
    (str : Fin N) (delimiter : Fin (A + 4)) (scan : Fin (A + 4) → Bool)
    (hstop : scan delimiter = false) (words : Fin N → List (Fin (A + 4)))
    (hword : ∀ j, j ≠ str → ∀ x ∈ words j, scan x = true)
    (rest output : List (Fin (A + 4))) (v : HS (N + 3) Q A U) (S : Stacks (N + 3) A)
    (hinput : S.R (framedCoreAux N 0) = delimitedBankFrames delimiter (framedCoreJobs (framedCoreEmbed N) str words) ++ rest)
    (htmp : S.R (framedCoreAux N 1) = [])
    (hblank : ∀ j, j ≠ str → S.R (framedCoreEmbed N j) = [])
    (core : Pr P N Q A U) (C : ℝ)
    (hcore : ∀ u : HS N Q A U,
      let B : Stacks N A := { embStk (framedCoreEmbed N) S with R := Function.update words str (S.R (framedCoreEmbed N str)) }
      ∃ (u' : HS N Q A U) (steps : ℕ), u'.user = u.user ∧ (steps : ℝ) ≤ C ∧
        Exec body core (mk u B) steps (mk u' { B with R := Function.update B.R str output })) :
    ∃ (v' : HS (N + 3) Q A U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ C + (6 * (delimitedBankFrames delimiter (framedCoreJobs (framedCoreEmbed N) str words)).length + 2 * (framedCoreJobs (framedCoreEmbed N) str words).length + 2 : ℕ) ∧
      Exec outerBody (framedCoreCallProgram str delimiter scan ι core) (mk v S) steps
        (mk v' { S with R := delimitedCallAdvanced S.R (framedCoreAux N 0) (framedCoreAux N 2) (framedCoreEmbed N str) (delimitedBankFrames delimiter (framedCoreJobs (framedCoreEmbed N) str words)) rest output }) := by
  let G : Stacks (N + 3) A := { S with R := delimitedBankLoaded (framedCoreAux N 0) (framedCoreAux N 1) (framedCoreAux N 2) delimiter rest (framedCoreJobs (framedCoreEmbed N) str words) S.R }
  have hx := delimitedBankCall_exec outerBody (framedCoreAux N 0) (framedCoreAux N 1) (framedCoreAux N 2)
    (framedCoreEmbed N str) (framedCoreAux_nodup N) delimiter scan hstop
    (framedCoreJobs (framedCoreEmbed N) str words)
    (by rw [framedCoreJobs_destinations]; exact framedCoreDestinations_nodup _ (framedCoreEmbed_injective N) str)
    (by intro job hj; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hj
        exact ⟨framedCoreEmbed_aux N j 0, framedCoreEmbed_aux N j 1, framedCoreEmbed_aux N j 2⟩)
    (by rw [framedCoreJobs_destinations]; exact framedCoreDestinations_stream _ (framedCoreEmbed_injective N) str)
    (by intro job hj; obtain ⟨j, hmem, rfl⟩ := List.mem_map.mp hj
        exact hword j ((mem_framedCoreRegisters str j).mp hmem))
    rest output v S hinput htmp
    (by intro job hj; obtain ⟨j, hmem, rfl⟩ := List.mem_map.mp hj
        exact hblank j ((mem_framedCoreRegisters str j).mp hmem))
    (embProg (framedCoreEmbed N) ι core) C ?_
  · simpa only [framedCoreCallProgram, framedCoreJobs_destinations, delimitedCallAdvanced] using hx
  · intro u
    obtain ⟨u', steps, hu, hm, he⟩ := hcore (embDn (framedCoreEmbed N) u)
    have hproject := framedCoreLoad_stack str delimiter rest words S
    change embStk (framedCoreEmbed N) G = _ at hproject
    rw [← hproject] at he
    obtain ⟨u'', hu'', he''⟩ := exec_emb_stream (framedCoreEmbed N) (framedCoreEmbed_injective N) ι
      body outerBody hbody core u G u' steps str output he
    refine ⟨u'', steps, hu''.trans hu, hm, he''⟩

end IntegerMultBounds.MathlibTM2.Routing
