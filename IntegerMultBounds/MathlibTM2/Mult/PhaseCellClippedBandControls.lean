module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandIntervalEndpoints
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClipUnary

/-! Generate the clipped folded-band cursor and count, restoring borrowed headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def clippedBandControls (index band total cursor count saved tmp : Fin T) : Pr P T Q A U :=
  .seq (bandIntervalEndpoints index band cursor count tmp)
    (.seq (clipUnary total count saved tmp) (usub cursor count tmp))

def clippedBandControlsCost (n W N : ℕ) : ℕ :=
  bandIntervalEndpointsCost n W+(clipUnaryCost N (n+W+1)+(4*(n-W)+4))

theorem clippedBandControls_exec {index band total cursor count saved tmp : Fin T}
    (hreg : [index,band,total,cursor,count,saved,tmp].Nodup) (n W N : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hn : (S.R index).length = n) (hW : (S.R band).length = W) (hN : (S.R total).length = N)
    (hfresh : ∀ k ∈ [cursor,count,saved,tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (clippedBandControls index band total cursor count saved tmp) (mk v S)
        (clippedBandControlsCost n W N)
        (mk v' {S with R := (Function.update (Function.update S.R cursor (List.replicate (n-W) tick))
          count (List.replicate (min N (n+W+1)-(n-W)) tick))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := bandIntervalEndpoints_exec (body := body)
    (index := index) (band := band) (cursor := cursor) (count := count) (tmp := tmp)
    (by regs_nodup) n W v S hn hW (by
      intro k hk
      exact hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto))
  let S₁ : Stacks T A := {S with R := (Function.update (Function.update S.R cursor
    (List.replicate (n-W) tick)) count (List.replicate (n+W+1) tick))}
  obtain ⟨v₂,hu₂,he₂⟩ := clipUnary_exec (body := body)
    (total := total) (count := count) (saved := saved) (tmp := tmp) (by regs_nodup)
    N (n+W+1) v₁ S₁
    (by simpa [S₁,‹total ≠ cursor›,‹total ≠ count›] using hN)
    (by simp [S₁]) (by simp [S₁]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with hk | hk
      · subst k
        simpa [S₁,‹cursor ≠ saved›.symm,‹count ≠ saved›.symm] using hfresh saved (by simp)
      · subst k
        simpa [S₁,‹cursor ≠ tmp›.symm,‹count ≠ tmp›.symm] using hfresh tmp (by simp))
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R count (List.replicate (min N (n+W+1)) tick)}
  obtain ⟨v₃,hu₃,he₃⟩ := usub_exec body (a := cursor) (b := count) (t := tmp)
    ‹cursor ≠ count› ‹cursor ≠ tmp› ‹count ≠ tmp› v₂ S₂ (by
      simpa [S₂,S₁,‹count ≠ tmp›.symm,‹cursor ≠ tmp›.symm] using hfresh tmp (by simp))
  have hlen : (S₂.R cursor).length = n-W := by simp [S₂,S₁,‹cursor ≠ count›]
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hlen]; rfl) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hc : k = cursor <;> by_cases hn' : k = count <;>
    simp_all [S₂,S₁,List.drop_replicate]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
