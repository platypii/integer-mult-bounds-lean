module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceBinaryPacket
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishMarkedWidth

/-! Advance a self-describing binary field without executing its payload consumer. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def advanceMarkedBinaryPacket (width src word saved tmp cy : Fin T) : Pr P T Q A U :=
  .seq (takeMarkedWidth src width)
    (.seq (advanceBinaryPacket width src word saved tmp cy) (publishMarkedWidth width src tmp))

theorem advanceMarkedBinaryPacket_exec (width src word saved tmp cy : Fin T)
    (hreg : [width,src,word,saved,tmp].Nodup) (W x : ℕ) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A) (hwidth : S.R width = [])
    (hsrc : S.R src = List.replicate W tick++bitSymbol false::(binSyms W x++tail))
    (hword : S.R word = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (advanceMarkedBinaryPacket width src word saved tmp cy) (mk v S) (22*W+25)
        (mk v' {S with R := (Function.update S.R src
          (List.replicate W tick++bitSymbol false::(binSyms W (x+1)++tail)))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := takeMarkedWidth_exec (body := body) src width ‹width ≠ src›.symm W
    (binSyms W x++tail) v S hsrc
  let S₁ : Stacks T A := {S with R := (Function.update (Function.update S.R src (binSyms W x++tail))
    width (List.replicate W tick++S.R width))}
  obtain ⟨v₂,hu₂,he₂⟩ := advanceBinaryPacket_exec (body := body) width src word saved tmp cy
    hreg W x tail v₁ S₁ (by simp [S₁,hwidth]) (by simp [S₁,‹width ≠ src›.symm])
    (by simpa [S₁,‹width ≠ word›.symm,‹src ≠ word›.symm] using hword)
    (by simpa [S₁,‹width ≠ saved›.symm,‹src ≠ saved›.symm] using hsaved)
    (by simpa [S₁,‹width ≠ tmp›.symm,‹src ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R src (binSyms W (x+1)++tail)}
  obtain ⟨v₃,hu₃,he₃⟩ := publishMarkedWidth_exec (body := body) width src tmp (by simp_all) v₂ S₂
    (by simpa [S₂,S₁,‹width ≠ tmp›.symm,‹src ≠ tmp›.symm] using htmp)
  have hlen : (S₂.R width).length = W := by simp [S₂,S₁,hwidth,‹width ≠ src›]
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · rw [hlen]; omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hs : k = src <;> by_cases hw : k = width <;> simp_all [S₂,S₁]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
