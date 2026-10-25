module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherBatch

/-! Gather an ordered window group after an initial forward seek. Both source
and delimited controls are restored, with total source motion charged once. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def gatherOffset (dst control savedControl advance window src acc current savedSource buf tmp
    initialControl initialSource : Fin T) : Pr P T Q A U :=
  .seq (gatherRead control advance initialControl)
    (.seq (transfer advance src initialSource tmp)
      (.seq (uclear advance)
        (.seq (gatherBatch dst control savedControl advance window src acc current savedSource buf tmp)
          (.seq (moveR initialSource src id) (moveR initialControl control id)))))

theorem gatherOffset_exec {dst control savedControl advance window src acc current savedSource buf tmp
    initialControl initialSource : Fin T}
    (hreg : [dst, control, savedControl, advance, window, src, acc, current, savedSource, buf, tmp,
      initialControl, initialSource].Nodup)
    (L d : ℕ) (ds : List ℕ) (E : List (Fin (A+4))) (hd : d ≤ E.length)
    (hfit : GatherFits L (E.drop d) ds) (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = gatherControls A (d::ds)) (hs : S.R src = E)
    (hw : (S.R window).length = L)
    (hclean : ∀ k ∈ [savedControl, advance, acc, current, savedSource, buf, tmp, initialControl,
      initialSource], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (gatherOffset dst control savedControl advance window src acc current savedSource buf tmp
        initialControl initialSource) (mk v S)
        (ds.length*(14*L+25)+12*(d+ds.sum)+23)
        (mk v' { S with R := Function.update S.R dst (gatherRows L (E.drop d) ds ++ S.R dst) }) := by
  have hz0 := hclean savedControl (by simp)
  have hz1 := hclean advance (by simp)
  have hz2 := hclean acc (by simp)
  have hz3 := hclean current (by simp)
  have hz4 := hclean savedSource (by simp)
  have hz5 := hclean buf (by simp)
  have hz6 := hclean tmp (by simp)
  have hz7 := hclean initialControl (by simp)
  have hz8 := hclean initialSource (by simp)
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁, hu₁, he₁⟩ := gatherRead_exec (body := body)
    (show [control, advance, initialControl].Nodup by regs_nodup) d (gatherControls A ds) v S hc
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update (Function.update S.R control
    (gatherControls A ds)) advance (List.replicate d tick)) initialControl (blank :: List.replicate d tick)) }
  have he₁' : Exec body (gatherRead control advance initialControl) (mk v S) (2*d+3) (mk v₁ S₁) := by
    simpa [S₁, hclean advance (by simp), hclean initialControl (by simp)] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := transfer_exec (body := body)
    (show [advance, src, initialSource, tmp].Nodup by regs_nodup) v₁ S₁ (E.take d) (E.drop d)
    (by simp [S₁, ‹control ≠ src›.symm, ‹advance ≠ src›.symm, ‹src ≠ initialControl›, hs])
    (by simp [S₁, ‹advance ≠ initialControl›, List.length_take, Nat.min_eq_left hd])
    (by simp [S₁, ‹control ≠ tmp›.symm, ‹advance ≠ tmp›.symm, ‹tmp ≠ initialControl›, hclean tmp (by simp)])
  let S₂ : Stacks T A := { S₁ with R := (Function.update (Function.update S₁.R src (E.drop d))
    initialSource (E.take d).reverse) }
  have he₂' : Exec body (transfer advance src initialSource tmp) (mk v₁ S₁) (4*d+4) (mk v₂ S₂) := by
    simpa [S₂, S₁, ‹control ≠ initialSource›.symm, ‹advance ≠ initialSource›.symm,
      ‹initialControl ≠ initialSource›.symm, hclean initialSource (by simp), List.length_take, Nat.min_eq_left hd] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body advance v₂ S₂
  let S₃ : Stacks T A := { S₂ with R := Function.update S₂.R advance [] }
  have he₃' : Exec body (uclear advance) (mk v₂ S₂) (2*d+2) (mk v₃ S₃) := by
    simpa [S₂, S₁, ‹advance ≠ src›, ‹advance ≠ initialSource›, ‹advance ≠ initialControl›] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := gatherBatch_exec (body := body)
    (show [dst, control, savedControl, advance, window, src, acc, current, savedSource, buf, tmp].Nodup by regs_nodup)
    L ds (E.drop d) hfit v₃ S₃
    (by simp [S₃, S₂, S₁, ‹control ≠ advance›, ‹control ≠ initialSource›, ‹control ≠ src›,
      ‹control ≠ initialControl›])
    (by simp [S₃, S₂, ‹advance ≠ src›.symm, ‹src ≠ initialSource›])
    (by simpa [S₃, S₂, S₁, ‹advance ≠ window›.symm, ‹window ≠ initialSource›, ‹window ≠ src›,
      ‹window ≠ initialControl›, ‹control ≠ window›.symm] using hw) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp (disch := first | assumption | (apply Ne.symm; assumption))
        [S₃, S₂, S₁, hz0, hz2, hz3, hz4, hz5, hz6])
  let S₄ : Stacks T A := { S₃ with R := Function.update S₃.R dst (gatherRows L (E.drop d) ds ++ S₃.R dst) }
  obtain ⟨v₅, hu₅, he₅⟩ := moveR_exec body initialSource src ‹src ≠ initialSource›.symm id v₄ S₄
  let S₅ : Stacks T A := { S₄ with R := movedR S₄.R initialSource src id (S₄.R initialSource) }
  obtain ⟨v₆, hu₆, he₆⟩ := moveR_exec body initialControl control ‹control ≠ initialControl›.symm id v₅ S₅
  have his : S₄.R initialSource = (E.take d).reverse := by
    simp [S₄, S₃, S₂, ‹dst ≠ initialSource›.symm, ‹advance ≠ initialSource›.symm]
  have hic : S₅.R initialControl = blank :: List.replicate d tick := by
    simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₅, S₄, S₃, S₂, S₁, movedR]
  refine ⟨v₆, hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄ (Exec.seq he₅ he₆))))).cast ?_ ?_⟩
  · rw [his, hic]
    simp [List.length_take, Nat.min_eq_left hd]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      clear he₁ he₁' he₂ he₂' he₃ he₃' he₄ he₅ he₆ hreg hclean
      by_cases hk0 : k = dst
      · subst k
        simp (disch := first | assumption | (apply Ne.symm; assumption))
          [S₅, S₄, S₃, S₂, S₁, movedR]
      by_cases hk1 : k = control
      · subst k
        simp (disch := first | assumption | (apply Ne.symm; assumption))
          [S₅, S₄, S₃, S₂, S₁, movedR, hc, gatherControls]
      by_cases hk2 : k = advance
      · subst k
        simp (disch := first | assumption | (apply Ne.symm; assumption))
          [S₅, S₄, S₃, S₂, S₁, movedR, hz1]
      by_cases hk3 : k = src
      · subst k
        simp (disch := first | assumption | (apply Ne.symm; assumption))
          [S₅, S₄, S₃, S₂, S₁, movedR, hs]
      by_cases hk4 : k = initialControl
      · subst k
        simp (disch := first | assumption | (apply Ne.symm; assumption))
          [S₅, S₄, S₃, S₂, S₁, movedR, hz7]
      by_cases hk5 : k = initialSource
      · subst k
        simp (disch := first | assumption | (apply Ne.symm; assumption))
          [S₅, S₄, S₃, S₂, S₁, movedR, hz8]
      simp [S₅, S₄, S₃, S₂, S₁, movedR, hk0, hk1, hk2, hk3, hk4, hk5]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
