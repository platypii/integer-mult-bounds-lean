module

public import IntegerMultBounds.MathlibTM2.Routing.DelimitedScheduleExec

/-! The uniform framed loop instantiated with the actual metadata-bank loader,
stream-only call and cleanup program. The destination list is fixed for all stages. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U I : Type}

theorem delimitedBankFrames_ne_nil (delimiter : Fin (A + 4))
    (jobs : List (Fin T × List (Fin (A + 4)))) (destinations : List (Fin T))
    (hdest : jobs.map Prod.fst = destinations) (hne : destinations ≠ []) :
    delimitedBankFrames delimiter jobs ≠ [] := by
  intro he
  have hlen := congrArg List.length he
  rw [delimitedBankFrames_length] at hlen
  have hd := congrArg List.length hdest
  simp only [List.length_map, List.length_nil] at hd hlen
  have hp := List.length_pos_iff.mpr hne
  omega

def delimitedBankStagePrice (delimiter : Fin (A + 4))
    (jobs : I → List (Fin T × List (Fin (A + 4)))) (callPrice : I → ℝ) (i : I) : ℝ :=
  callPrice i + (6 * (delimitedBankFrames delimiter (jobs i)).length + 2 * (jobs i).length + 2 : ℕ)

theorem delimitedBankSchedule_exec (body : P → Pr P T Q A U)
    (src tmp saved str : Fin T) (hreg : [src, tmp, saved].Nodup)
    (hstream : [src, saved, str].Nodup)
    (delimiter : Fin (A + 4)) (p : Fin (A + 4) → Bool) (hstop : p delimiter = false)
    (destinations : List (Fin T)) (hdistinct : destinations.Nodup) (hne : destinations ≠ [])
    (hseparate : ∀ d ∈ destinations, d ≠ src ∧ d ≠ tmp ∧ d ≠ saved)
    (hstr : str ∉ destinations)
    (jobs : I → List (Fin T × List (Fin (A + 4))))
    (hdest : ∀ i, (jobs i).map Prod.fst = destinations)
    (hword : ∀ i, ∀ j ∈ jobs i, ∀ x ∈ j.2, p x = true)
    (effect : I → List (Fin (A + 4)) → List (Fin (A + 4))) (callPrice : I → ℝ)
    (Ready : Stacks T A → Prop)
    (htmp : ∀ B, Ready B → B.R tmp = [])
    (hblank : ∀ B, Ready B → ∀ d ∈ destinations, B.R d = [])
    (hstable : ∀ i rest (B : Stacks T A), Ready B →
      Ready { B with R := delimitedCallAdvanced B.R src saved str (delimitedBankFrames delimiter (jobs i)) rest (effect i (B.R str)) })
    (call : Pr P T Q A U)
    (hcall : ∀ i rest (u : HS T Q A U) (B : Stacks T A), Ready B →
      B.R src = delimitedBankFrames delimiter (jobs i) ++ rest →
      let G : Stacks T A := { B with R := delimitedBankLoaded src tmp saved delimiter rest (jobs i) B.R }
      ∃ (u' : HS T Q A U) (steps : ℕ), u'.user = u.user ∧ (steps : ℝ) ≤ callPrice i ∧
        Exec body call (mk u G) steps (mk u' { G with R := Function.update G.R str (effect i (B.R str)) }))
    (stages : List I) (v : HS T Q A U) (S : Stacks T A) (hready : Ready S)
    (hsrc : S.R src = delimitedScheduleInput (fun i => delimitedBankFrames delimiter (jobs i)) stages)
    (hsaved : S.R saved = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ delimitedSchedulePrice (delimitedBankStagePrice delimiter jobs callPrice) stages +
        (2 * (delimitedScheduleInput (fun i => delimitedBankFrames delimiter (jobs i)) stages).length + 3 : ℕ) ∧
      Exec body (delimitedScheduleProgram src saved
        (delimitedBankCall src tmp saved delimiter p destinations call)) (mk v S) steps
        (mk v' { S with R := Function.update S.R str (delimitedScheduleEffect effect stages (S.R str)) }) := by
  apply delimitedSchedule_exec body src saved str hstream
    (fun i => delimitedBankFrames delimiter (jobs i)) effect
    (delimitedBankStagePrice delimiter jobs callPrice) Ready
    (delimitedBankCall src tmp saved delimiter p destinations call) stages
    (fun i _ => delimitedBankFrames_ne_nil delimiter (jobs i) destinations (hdest i) hne)
    ?_ v S hready hsrc hsaved
  intro i _ rest u B hr hi
  have hsep : ∀ j ∈ jobs i, j.1 ≠ src ∧ j.1 ≠ tmp ∧ j.1 ≠ saved := by
    intro j hj
    apply hseparate j.1
    rw [← hdest i]
    exact List.mem_map.mpr ⟨j, hj, rfl⟩
  obtain ⟨u', steps, hu, hm, hx⟩ := delimitedBankCall_exec body src tmp saved str hreg delimiter p hstop
    (jobs i) (by rw [hdest i]; exact hdistinct) hsep (by rw [hdest i]; exact hstr)
    (hword i) rest (effect i (B.R str)) u B hi (htmp B hr)
    (fun j hj => hblank B hr j.1 (by rw [← hdest i]; exact List.mem_map.mpr ⟨j, hj, rfl⟩))
    call (callPrice i) (fun u => hcall i rest u B hr hi)
  rw [hdest i] at hx
  exact ⟨u', steps, hu, hm, hstable i rest B hr, hx⟩

end IntegerMultBounds.MathlibTM2.Routing
