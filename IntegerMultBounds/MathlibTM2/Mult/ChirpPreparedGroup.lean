module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupLoop

/-! # Group execution from one prepared setup, restoring inputs and loop counters -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

noncomputable def preparedGroup (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) (shared : Bool := false) : Pr P 640 Q A U :=
  .seq (.act (peekR lineCount)) <|
  .seq (.loop (·.flag) (groupLoopBody hQ hQrp shared)) <|
  .seq (moveR savedLineCount lineCount id) finishGroup

private theorem groupFinish_restore (cs xs rest ys : List (Fin (A + 4))) (R : Regs 640 A)
    (hc : R lineCount = cs) (hs : R savedLineCount = [])
    (ha : R inputArchive = []) (ho : R outputArchive = []) (hi : R groupInput = xs ++ rest) :
    let R₁ := groupLoopR cs xs rest ys R
    let R₂ := Function.update (Function.update R₁ savedLineCount []) lineCount cs
    Function.update (Function.update (Function.update (Function.update R₂ inputArchive [])
      groupInput (xs ++ rest)) outputArchive []) groupOutput (ys ++ R₂ groupOutput) =
      Function.update R groupOutput (ys ++ R groupOutput) := by
  dsimp only
  have hreg : [lineCount, savedLineCount, groupInput, inputArchive, outputArchive, groupOutput].Nodup := by
    decide +kernel
  regs_ne hreg
  funext k
  by_cases hn : k = lineCount
  · subst k; simp_all [groupLoopR, groupStepR]
  by_cases hs' : k = savedLineCount
  · subst k; simp_all [groupLoopR, groupStepR]
  by_cases hi' : k = groupInput
  · subst k; simp_all [groupLoopR, groupStepR]
  by_cases ha' : k = inputArchive
  · subst k; simp_all [groupLoopR, groupStepR]
  by_cases ho' : k = outputArchive
  · subst k; simp_all [groupLoopR, groupStepR]
  by_cases hg : k = groupOutput
  · subst k; simp_all [groupLoopR, groupStepR]
  · simp_all [groupLoopR, groupStepR]

/-- Execute a whole group, preserving the raw batch and all prepared setup. -/
theorem preparedGroup_exec {shared : Bool} (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) (hA : 96 ≤ A)
    (s t α p : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p)
    (us : List (ZMod s → GaussianInt))
    (hu : ∀ u ∈ us, ∀ j,
      ‖value (chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α)) (u j)‖ ≤ 1)
    (v : HS 640 Q A U) (S : Stacks 640 A) (rest : List (Fin (A + 4)))
    (hd : SelectedLineData s t α p S shared) (hc : (S.R lineCount).length = us.length)
    (hi : S.R groupInput = (us.map (groupLineInput A s α p)).flatten ++ rest)
    (hw : (S.R lineSymbols).length =
      s * (chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α) +
        chirpForwardRingLog p α + chirpForwardGrowth p + 5))
    (hr : S.R (raw .raw) = []) (hb : S.R groupBuf = []) (ht : S.R groupTmp = [])
    (hs : S.R savedLineCount = []) (ha : S.R inputArchive = []) (ho : S.R outputArchive = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (us.map (fun u => groupLineCost A s t α p u shared)).sum + 5 * us.length +
        2 * (us.map (groupLineInput A s α p)).flatten.length +
        2 * (us.map (groupLineOutput A s t α p)).flatten.length + 8 ∧
      Exec body (preparedGroup hQ hQrp shared) (mk v S) n
        (mk v' { S with R := (Function.update S.R groupOutput
          ((us.map (groupLineOutput A s t α p)).flatten ++ S.R groupOutput)) }) := by
  let xs := (us.map (groupLineInput A s α p)).flatten
  let ys := (us.map (groupLineOutput A s t α p)).flatten
  have hreg : [lineCount, savedLineCount, groupInput, inputArchive, outputArchive, groupOutput].Nodup := by
    decide +kernel
  regs_ne hreg
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := groupLoop_exec (shared := shared) (body := body) hQ hQrp hA s t α p
    hst hα hαp us hu (S.R lineCount) hc { v with flag := (S.R lineCount).head?.isSome }
    S rest hd rfl hi hw hr hb ht rfl
  let S₁ : Stacks 640 A := { S with R := groupLoopR (S.R lineCount) xs rest ys S.R }
  have hs₁ : S₁.R savedLineCount = (S.R lineCount).reverse := by
    simp [S₁, groupLoopR, groupStepR, hs, (‹savedLineCount ≠ outputArchive›),
      (‹savedLineCount ≠ inputArchive›), (‹savedLineCount ≠ groupInput›)]
  have hc₁ : S₁.R lineCount = [] := by
    simp [S₁, groupLoopR, groupStepR, ‹lineCount ≠ savedLineCount›,
      ‹lineCount ≠ outputArchive›, ‹lineCount ≠ inputArchive›, ‹lineCount ≠ groupInput›]
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body savedLineCount lineCount
    (‹lineCount ≠ savedLineCount›.symm) id v₁ S₁
  rw [hs₁, List.length_reverse, hc] at he₂
  let S₂ : Stacks 640 A := { S₁ with R :=
    (Function.update (Function.update S₁.R savedLineCount []) lineCount (S.R lineCount)) }
  have he₂' : Exec body (moveR savedLineCount lineCount id) (mk v₁ S₁)
      (2 * us.length + 2) (mk v₂ S₂) := by
    simpa only [S₂, movedR, List.map_id, List.reverse_reverse, hc₁, List.append_nil] using he₂
  have ha₂ : S₂.R inputArchive = xs.reverse := by
    simp [S₂, S₁, groupLoopR, groupStepR, ha, (‹lineCount ≠ inputArchive›.symm),
      (‹savedLineCount ≠ inputArchive›.symm), ‹inputArchive ≠ outputArchive›]
  have ho₂ : S₂.R outputArchive = ys.reverse := by
    simp [S₂, S₁, groupLoopR, groupStepR, ho, (‹lineCount ≠ outputArchive›.symm),
      (‹savedLineCount ≠ outputArchive›.symm)]
  have hi₂ : S₂.R groupInput = rest := by
    simp [S₂, S₁, groupLoopR, groupStepR, (‹lineCount ≠ groupInput›.symm),
      (‹savedLineCount ≠ groupInput›.symm), ‹groupInput ≠ outputArchive›, ‹groupInput ≠ inputArchive›]
  obtain ⟨v₃, hu₃, he₃⟩ := finishGroup_exec (body := body) v₂ S₂ xs ys rest ha₂ ho₂ hi₂
  have hp := Exec.act (body := body) (peekR lineCount) (mk v S)
  rw [peekR_run] at hp
  refine ⟨v₃, 1 + (n₁ + ((2 * us.length + 2) + (2 * xs.length + 2 * ys.length + 4))),
    hu₃.trans (hu₂.trans hu₁), by dsimp only [xs, ys] at *; omega, ?_⟩
  have he := Exec.seq hp (Exec.seq he₁ (Exec.seq he₂' he₃))
  refine he.cast rfl ?_
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  exact groupFinish_restore (S.R lineCount) xs rest ys S.R rfl hs ha ho hi

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
