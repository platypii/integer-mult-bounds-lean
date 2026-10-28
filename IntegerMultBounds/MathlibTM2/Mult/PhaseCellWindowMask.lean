module

public import IntegerMultBounds.MathlibTM2.Host.WindowStream
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Restrict a generated mask to a scalar window using linear native tape work. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def windowMask (inside outside : Fin (A+4) → Fin (A+4)) : Pr P 117 Q A U :=
  .seq (ucopy 101 0 25) (.seq (ucopy 103 1 25)
    (.seq (windowScan 0 1 109 22 97 23 inside outside) (moveR 22 109 id)))

def windowMaskCost (s a b : ℕ) : ℕ := 4*(a+b)+6*s+14

theorem windowMask_pushBound (inside outside : Fin (A+4) → Fin (A+4)) :
    Fast.Main.mnNativePushBound 2 (windowMask (P := P) (Q := Q) (U := U) inside outside) := by
  simp [windowMask,windowScan,windowStep,ucopy,umulSym,scanR,keepIn,drainR,popDo,pushN,
    moveR,whileR,moveStep,peekR,Fast.Main.mnNativePushBound,Fast.Main.mnActPush]

theorem windowMask_certify (inside outside : Fin (A+4) → Fin (A+4))
    {s t : Store (HΓ (T := 117) A) (HS 117 Q A U)} {steps depth B : ℕ}
    (he : Exec body (windowMask inside outside) s steps t)
    (hB : Fast.Main.mnSize s+depth+2*steps ≤ B) :
    ExecWithin body (fun d z => Fast.Main.mnSize z+d ≤ B) depth
      (windowMask inside outside) s steps t :=
  Fast.Main.mn_native_exec_within he 2 (windowMask_pushBound inside outside) depth B hB

theorem windowMask_exec (s a b : ℕ) (ha : a ≤ s) (hb : b ≤ s) (inside outside : Fin (A+4) → Fin (A+4))
    (v : HS 117 Q A U) (S : Stacks 117 A) (xs tail : List (Fin (A+4)))
    (hs : (S.R 97).length = s) (haSrc : (S.R 101).length = a) (hbSrc : (S.R 103).length = b)
    (hxs : xs.length = s) (hsrc : S.R 109 = xs++tail)
    (hfresh : ∀ k ∈ [(0 : Fin 117),1,22,23,25], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (windowMask inside outside) (mk v S) (windowMaskCost s a b)
        (mk v' {S with R := Function.update S.R 109 (windowWord inside outside a b xs++tail)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (t := (25 : Fin 117))
    (by decide : (101 : Fin 117) ≠ 0) (by decide) (by decide) v S (hfresh 25 (by simp))
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 0 (List.replicate a tick)}
  have he₁' : Exec body (ucopy 101 0 25) (mk v S) (4*a+4) (mk v₁ S₁) := by
    simpa [S₁,haSrc,hfresh 0 (by simp)] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) (t := (25 : Fin 117))
    (by decide : (103 : Fin 117) ≠ 1) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 25 (by simp))
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 1 (List.replicate b tick)}
  have he₂' : Exec body (ucopy 103 1 25) (mk v₁ S₁) (4*b+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hbSrc,hfresh 1 (by simp)] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := windowScan_exec body
    (show [(0 : Fin 117),1,109,22,97,23].Nodup by decide) inside outside v₂ S₂ xs tail a b
    (by simpa [S₂,S₁,hxs] using hs) (by omega) (by omega)
    (by simp [S₂,S₁]) (by simp [S₂]) (by simpa [S₂,S₁] using hsrc)
    (by simpa [S₂,S₁] using hfresh 23 (by simp))
  let S₃ : Stacks 117 A := {S with R := (Function.update (Function.update S.R 109 tail) 22
    (windowWord inside outside a b xs).reverse)}
  have he₃' : Exec body (windowScan 0 1 109 22 97 23 inside outside) (mk v₂ S₂) (4*s+4) (mk v₃ S₃) := by
    apply he₃.cast (by rw [hxs])
    apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [S₃,S₂,S₁,Function.update_apply]
    split_ifs <;> simp_all
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec (body := body) 22 109 (by decide) id v₃ S₃
  refine ⟨v₄,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄))).cast ?_ ?_⟩
  · simp [S₃,windowWord_length,hxs,windowMaskCost]
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [S₃,movedR,Function.update_apply,List.map_id]
    split_ifs <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
