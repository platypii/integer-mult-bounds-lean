module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupTransfers

/-! # Restore the input archive and publish the collected output once per group -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

def finishGroup : Pr P 640 Q A U :=
  .seq (moveR inputArchive groupInput id) (moveR outputArchive groupOutput id)

/-- One final archive reversal restores the original input prefix and publishes output in line order. -/
theorem finishGroup_exec (v : HS 640 Q A U) (S : Stacks 640 A) (xs ys rest : List (Fin (A + 4)))
    (hinput : S.R inputArchive = xs.reverse) (houtput : S.R outputArchive = ys.reverse)
    (hrest : S.R groupInput = rest) :
    ∃ v', v'.user = v.user ∧
      Exec body finishGroup (mk v S) (2 * xs.length + 2 * ys.length + 4)
        (mk v' { S with R := (Function.update (Function.update (Function.update
          (Function.update S.R inputArchive []) groupInput (xs ++ rest)) outputArchive [])
          groupOutput (ys ++ S.R groupOutput)) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := moveR_exec body inputArchive groupInput (by decide +kernel) id v S
  rw [hinput, List.length_reverse] at he₁
  let S₁ : Stacks 640 A := { S with R :=
    (Function.update (Function.update S.R inputArchive []) groupInput (xs ++ rest)) }
  have he₁' : Exec body (moveR inputArchive groupInput id) (mk v S) (2 * xs.length + 2) (mk v₁ S₁) := by
    simpa only [S₁, movedR, List.map_id, List.reverse_reverse, hrest] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body outputArchive groupOutput (by decide +kernel) id v₁ S₁
  have hout : S₁.R outputArchive = ys.reverse := by
    simpa only [S₁, Function.update_of_ne (show outputArchive ≠ groupInput by decide +kernel),
      Function.update_of_ne (show outputArchive ≠ inputArchive by decide +kernel)] using houtput
  rw [hout, List.length_reverse] at he₂
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁' he₂).cast (by omega) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  simp only [S₁, movedR, List.map_id, List.reverse_reverse,
    Function.update_of_ne (show groupOutput ≠ groupInput by decide +kernel),
    Function.update_of_ne (show groupOutput ≠ inputArchive by decide +kernel)]

/-- A staged line and its collected result change only the three group-level data ports. -/
theorem group_roundTrip (xs rest ys : List (Fin (A + 4))) (R : Regs 640 A)
    (hraw : R (raw .raw) = []) (hout : R (output.nr .out) = []) :
    collectLineR ys (Function.update (stageLineR xs rest R) (output.nr .out) ys) =
      Function.update (Function.update (Function.update R groupInput rest)
        inputArchive (xs.reverse ++ R inputArchive)) outputArchive (ys.reverse ++ R outputArchive) := by
  have hreg : [raw .raw, output.nr .out, groupInput, inputArchive, outputArchive].Nodup := by decide +kernel
  regs_ne hreg
  funext k
  by_cases hr : k = raw .raw
  · subst k; simp_all [collectLineR, stageLineR]
  by_cases ho : k = output.nr .out
  · subst k; simp_all [collectLineR, stageLineR]
  by_cases hi : k = groupInput
  · subst k; simp_all [collectLineR, stageLineR]
  by_cases ha : k = inputArchive
  · subst k; simp_all [collectLineR, stageLineR]
  by_cases hb : k = outputArchive
  · subst k; simp_all [collectLineR, stageLineR]
  · simp_all [collectLineR, stageLineR]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
