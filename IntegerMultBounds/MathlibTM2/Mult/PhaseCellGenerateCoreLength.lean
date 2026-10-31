module

public import IntegerMultBounds.MathlibTM2.Node.Params
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip
public import IntegerMultBounds.MathlibTM2.StackResources

/-! A movement class shares one core-length header, obtained from its halo
length by removing the two equal margins. All source counters are retained. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def generateCoreLength (halo radius core saved : Fin T) : Pr P T Q A U :=
  .seq (ucopy halo core saved) (.seq (usub radius core saved) (usub radius core saved))

theorem generateCoreLength_native (halo radius core saved : Fin T) :
    mnNativePushBound 2 (generateCoreLength (P := P) (Q := Q) (A := A) (U := U) halo radius core saved) := by
  simp [generateCoreLength,ucopy,umulSym,usub,scanR,drainR,popDo,keepIn,pushN,dropTop,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem generateCoreLength_exec (halo radius core saved : Fin T)
    (hreg : [halo,radius,core,saved].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (hcore : S.R core = []) (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (generateCoreLength halo radius core saved) (Host.mk v S)
        (4*(S.R halo).length+8*(S.R radius).length+12)
        (Host.mk v' {S with R := (Function.update S.R core
          (List.replicate ((S.R halo).length-2*(S.R radius).length) tick))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body ‹halo ≠ core› ‹halo ≠ saved› ‹core ≠ saved› v S hsaved
  let F : Stacks T A := {S with R := Function.update S.R core (List.replicate (S.R halo).length tick)}
  have he₁' : Exec body (ucopy halo core saved) (Host.mk v S) (4*(S.R halo).length+4) (Host.mk v₁ F) := by
    simpa only [hcore,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := usub_exec body ‹radius ≠ core› ‹radius ≠ saved› ‹core ≠ saved› v₁ F
    (by simp [F,‹core ≠ saved›.symm,hsaved])
  let G : Stacks T A := {S with R := (Function.update S.R core
    (List.replicate ((S.R halo).length-(S.R radius).length) tick))}
  have he₂' : Exec body (usub radius core saved) (Host.mk v₁ F) (4*(S.R radius).length+4) (Host.mk v₂ G) := by
    simpa [G,F,‹radius ≠ core›] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := usub_exec body ‹radius ≠ core› ‹radius ≠ saved› ‹core ≠ saved› v₂ G
    (by simp [G,‹core ≠ saved›.symm,hsaved])
  have he₃' : Exec body (usub radius core saved) (Host.mk v₂ G) (4*(S.R radius).length+4)
      (Host.mk v₃ {S with R := (Function.update S.R core
        (List.replicate ((S.R halo).length-2*(S.R radius).length) tick))}) := by
    simpa [G,‹radius ≠ core›,Nat.sub_sub,two_mul] using he₃
  exact ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁' (Exec.seq he₂' he₃')).cast (by omega) rfl⟩

theorem generateCoreLength_exec_within (halo radius core saved : Fin T)
    (hreg : [halo,radius,core,saved].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (hcore : S.R core = []) (hsaved : S.R saved = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        2*(4*(S.R halo).length+8*(S.R radius).length+12)) depth
        (generateCoreLength halo radius core saved) (Host.mk v S)
        (4*(S.R halo).length+8*(S.R radius).length+12)
        (Host.mk v' {S with R := (Function.update S.R core
          (List.replicate ((S.R halo).length-2*(S.R radius).length) tick))}) := by
  obtain ⟨v',hu,he⟩ := generateCoreLength_exec halo radius core saved hreg v S hcore hsaved
  exact ⟨v',hu,mn_native_exec_within he 2 (generateCoreLength_native _ _ _ _) depth _ (by omega)⟩
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
