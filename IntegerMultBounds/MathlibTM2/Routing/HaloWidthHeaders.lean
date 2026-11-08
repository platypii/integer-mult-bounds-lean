module

public import IntegerMultBounds.MathlibTM2.Routing.FieldHeaderCopy
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! Copy the word width and construct the enlarged local length L+2H from
ordinary retained masters. No enlarged-width header is supplied by the caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloWidthHeaders
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main FieldHeaderCopy
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def run : Pr P 117 Q A U :=
  .seq (resetCopy 47 33 57) (.seq (resetCopy 55 46 57) (.seq (ucopy 65 46 57) (ucopy 65 46 57)))

def cost (w L H : ℕ) := 4*w+4*L+8*H+20

def result (S : Stacks 117 A) (w L H : ℕ) : Stacks 117 A :=
  {S with R := (Function.update (Function.update S.R 33 (List.replicate w tick))
    46 (List.replicate (L+2*H) tick))}

theorem run_exec (w L H : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hw : (S.R 47).length = w) (hL : (S.R 55).length = L) (hH : (S.R 65).length = H)
    (hblank : ∀ i ∈ [(33 : Fin 117),46,57], S.R i = []) :
    ∃ vf, vf.user = v.user ∧ Exec body run (mk v S) (cost w L H) (mk vf (result S w L H)) := by
  obtain ⟨v₁,hu₁,he₁⟩ := resetCopy_exec (body := body) 47 33 57 (by decide) v S (hblank _ (by simp))
  let F : Stacks 117 A := {S with R := Function.update S.R 33 (List.replicate w tick)}
  have he₁' : Exec body (resetCopy 47 33 57) (mk v S) (4*w+6) (mk v₁ F) := by
    simpa [hw,hblank] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := resetCopy_exec (body := body) 55 46 57 (by decide) v₁ F (by simp [F,hblank])
  let G : Stacks 117 A := {F with R := Function.update F.R 46 (List.replicate L tick)}
  have he₂' : Exec body (resetCopy 55 46 57) (mk v₁ F) (4*L+6) (mk v₂ G) := by
    simpa [F,hL,hblank] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := ucopy_exec (body := body) (a := 65) (b := 46) (t := 57)
    (by decide) (by decide) (by decide) v₂ G (by simp [G,F,hblank])
  let J : Stacks 117 A := {G with R := Function.update G.R 46 (List.replicate (H+L) tick)}
  have he₃' : Exec body (ucopy 65 46 57) (mk v₂ G) (4*H+4) (mk v₃ J) := by
    simpa [J,G,F,hH,←List.replicate_add] using he₃
  obtain ⟨vf,hu₄,he₄⟩ := ucopy_exec (body := body) (a := 65) (b := 46) (t := 57)
    (by decide) (by decide) (by decide) v₃ J (by simp [J,G,F,hblank])
  have hsum : H+(H+L) = L+2*H := by omega
  have he₄' : Exec body (ucopy 65 46 57) (mk v₃ J) (4*H+4) (mk vf (result S w L H)) := by
    simpa [J,G,F,result,hH,←List.replicate_add,hsum] using he₄
  refine ⟨vf,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_⟩
  exact (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄'))).cast (by dsimp [cost]; omega) rfl

theorem run_native : mnNativePushBound 2 (run (P := P) (Q := Q) (A := A) (U := U)) := by
  refine ⟨resetCopy_pushBound _ _ _,resetCopy_pushBound _ _ _,?_,?_⟩ <;>
    simp [ucopy,umulSym,scanR,keepIn,pushN,drainR,popDo,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Routing.HaloWidthHeaders
