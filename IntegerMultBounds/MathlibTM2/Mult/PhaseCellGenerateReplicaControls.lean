module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaGatherSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnaryGatherControl

/-! Generate same-origin gathering controls from ordinary retained dimensions.
One owned copy of the positive replica count supplies the number of strides. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateReplicaControls : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 97 94 10 6 7) (.seq (unaryProduct 111 94 8 6 7)
    (.seq (ucopy 116 11 6) (.seq (.act (.pop (.rt 11) (fun v _ => v) .done))
      (.seq (.act (.push (.rt 91) (fun _ => blank) .done))
        (.seq (repeatUnaryGatherControl 11 12 10 91 7)
          (.seq (unaryGatherControl 8 91 7) (clearWords [8,10,11])))))))

def generateReplicaControlsCost (B s p w : ℕ) : ℕ :=
  B*(4*s*w+16)+6*s*w+10*p*w+9*(s+p)+34

theorem generateReplicaControls_exec (B s p w : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (hp : (S.R 111).length = p) (hw : (S.R 94).length = w)
    (hB : (S.R 116).length = B+1)
    (hfresh : ∀ k ∈ [(6 : Fin 117),7,8,10,11,12,91], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generateReplicaControlsCost B s p w ∧
      Exec body generateReplicaControls (mk v S) n
        (mk v' { S with R := Function.update S.R 91 (replicaGatherControls A (B+1) s p w) }) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [(97 : Fin 117),94,10,6,7].Nodup by decide) v S (hfresh 6 (by simp)) (hfresh 7 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 10 (List.replicate (s*w) tick) }
  have he₁' : Exec body (unaryProduct 97 94 10 6 7) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hs,hw,hfresh 10 (by simp)] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := unaryProduct_exec (body := body)
    (show [(111 : Fin 117),94,8,6,7].Nodup by decide) v₁ S₁
    (by simpa [S₁] using hfresh 6 (by simp)) (by simpa [S₁] using hfresh 7 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 8 (List.replicate (p*w) tick) }
  have he₂' : Exec body (unaryProduct 111 94 8 6 7) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,hp,hw,hfresh 8 (by simp)] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := ucopy_exec (body := body) (a := 116) (b := 11) (t := 6)
    (by decide) (by decide) (by decide) v₂ S₂ (by simpa [S₂,S₁] using hfresh 6 (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 11 (List.replicate (B+1) tick) }
  have he₃' : Exec body (ucopy 116 11 6) (mk v₂ S₂) (4*(B+1)+4) (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,hB,hfresh 11 (by simp)] using he₃
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 11 (List.replicate B tick) }
  have he₄ : Exec body (.act (.pop (.rt 11) (fun v _ => v) .done)) (mk v₃ S₃) 1 (mk v₃ S₄) := by
    simpa [S₄,S₃,Action.run,List.replicate_succ,update_rt] using
      Exec.act (body := body) (.pop (.rt 11) (fun v _ => v) .done) (mk v₃ S₃)
  let S₅ : Stacks 117 A := { S₄ with R := Function.update S₄.R 91 [blank] }
  have he₅ : Exec body (.act (.push (.rt 91) (fun _ => blank) .done)) (mk v₃ S₄) 1 (mk v₃ S₅) := by
    simpa [S₅,S₄,S₃,S₂,S₁,hfresh 91 (by simp),Action.run,update_rt] using
      Exec.act (body := body) (.push (.rt 91) (fun _ => blank) .done) (mk v₃ S₄)
  obtain ⟨v₆,n₆,hu₆,hn₆,he₆⟩ := repeatUnaryGatherControl_exec (body := body)
    (show [(11 : Fin 117),12,10,91,7].Nodup by decide) B (s*w) v₃ S₅
    (by simp [S₅,S₄]) (by simp [S₅,S₄,S₃,S₂,S₁])
    (by simpa [S₅,S₄,S₃,S₂,S₁] using hfresh 12 (by simp))
    (by simpa [S₅,S₄,S₃,S₂,S₁] using hfresh 7 (by simp))
  let S₆ : Stacks 117 A := { S₅ with R := Function.update S₅.R 91 (gatherControls A (List.replicate B (s*w))++[blank]) }
  obtain ⟨v₇,hu₇,he₇⟩ := unaryGatherControl_exec (body := body)
    (show [(8 : Fin 117),91,7].Nodup by decide) (p*w) v₆ S₆ (by simp [S₆,S₅,S₄,S₃,S₂])
    (by simpa [S₆,S₅,S₄,S₃,S₂,S₁] using hfresh 7 (by simp))
  let S₇ : Stacks 117 A := { S₆ with R := (Function.update S₆.R 91
    (List.replicate (p*w) tick++blank::S₆.R 91)) }
  obtain ⟨v₈,hu₈,he₈⟩ := clearWords_exec (body := body) [(8 : Fin 117),10,11] (by decide) v₇ S₇
  have hsum : ([(8 : Fin 117),10,11].map (fun k => (S₇.R k).length)).sum = p*w+s*w+B := by
    simp [S₇,S₆,S₅,S₄,S₃,S₂,S₁,Nat.add_assoc]
  have hcontrols' (k : ℕ) : gatherControls A (List.replicate k (s*w)++[0]) =
      gatherControls A (List.replicate k (s*w))++[blank] := by
    induction k with
    | zero => simp [gatherControls]
    | succ k ih => simp [List.replicate_succ,gatherControls,ih,List.append_assoc]
  have hcontrols := hcontrols' B
  refine ⟨v₈,n₁+(n₂+((4*(B+1)+4)+(1+(1+(n₆+((4*(p*w)+5)+(2*(p*w+s*w+B)+7))))))),
    hu₈.trans (hu₇.trans (hu₆.trans (hu₃.trans (hu₂.trans hu₁)))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄ (Exec.seq he₅
      (Exec.seq he₆ (Exec.seq he₇ he₈))))))).cast (by rw [hsum]; rfl) ?_⟩
  · simp only [hs,hw] at hn₁
    simp only [S₁,hp,hw,Function.update_of_ne (by decide : (111 : Fin 117) ≠ 10),
      Function.update_of_ne (by decide : (94 : Fin 117) ≠ 10)] at hn₂
    dsimp only [generateReplicaControlsCost]
    nlinarith only [hn₁,hn₂,hn₆]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h8 : k = 8
    · subst k; simp [hfresh 8 (by simp)]
    by_cases h10 : k = 10
    · subst k; simp [hfresh 10 (by simp)]
    by_cases h11 : k = 11
    · subst k; simp [hfresh 11 (by simp)]
    by_cases h91 : k = 91
    · subst k; simp [S₇,S₆,S₅,S₄,S₃,S₂,S₁,replicaGatherControls_succ,gatherControls,hcontrols]
    simp [S₇,S₆,S₅,S₄,S₃,S₂,S₁,h8,h10,h11,h91]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
