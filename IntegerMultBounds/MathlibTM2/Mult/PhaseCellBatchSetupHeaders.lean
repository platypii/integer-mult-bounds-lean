module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Fast.Input

/-! Generate the runtime word width and carry an owned batch count through
weight construction to the shared inverse parser. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateRuntimeWidth : Pr P₀ 117 Q A U :=
  .seq (umul 2 112 94 104) (.act (pushN 94 (fun _ => tick) 8 .done))

theorem generateRuntimeWidth_exec (q : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hq : (S.R 112).length = q) (h94 : S.R 94 = []) (h104 : S.R 104 = []) :
    ∃ v', v'.user = v.user ∧ Exec body generateRuntimeWidth (mk v S) (4*q+5)
      (mk v' { S with R := Function.update S.R 94 (List.replicate (2*q+8) tick) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := umul_exec (body := body) 2 (a := 112) (b := 94) (t := 104)
    (by decide) (by decide) (by decide) v S h104
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 94 (List.replicate (2*q) tick) }
  have he₁' : Exec body (umul 2 112 94 104) (mk v S) (4*q+4) (mk v₁ S₁) := by
    simpa [S₁, hq, h94] using he₁
  have he₂ := Exec.act (body := body) (pushN 94 (fun _ => tick) 8 .done) (mk v₁ S₁)
  rw [pushN_run] at he₂
  refine ⟨v₁, hu₁, (Exec.seq he₁' he₂).cast (by omega) ?_⟩
  simp only [S₁, Action.run, Function.update_self, Function.update_idem,
    List.replicate_append_replicate, show 8+2*q = 2*q+8 by omega]

/-- Consume the temporary width and batch headers after saving one parser packet. -/
def saveBatchInverseHeader : Pr P₀ 117 Q A U :=
  .seq (.act (pushN 109 (fun _ => blank) 1 .done))
    (.seq (copyR 116 109 107 id) (clearWords [94, 116]))

theorem saveBatchInverseHeader_exec (B w : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hB : S.R 116 = List.replicate B tick) (hw : (S.R 94).length = w) (h107 : S.R 107 = []) :
    ∃ v', v'.user = v.user ∧ Exec body saveBatchInverseHeader (mk v S) (6*B+2*w+10)
      (mk v' { S with R := (Function.update (Function.update (Function.update S.R
        109 (List.replicate B tick ++ blank :: S.R 109)) 94 []) 116 []) }) := by
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 109 (blank :: S.R 109) }
  have he₁ : Exec body (.act (pushN 109 (fun _ => blank) 1 .done)) (mk v S) 1 (mk v S₁) := by
    have he := Exec.act (body := body) (pushN 109 (fun _ => blank) 1 .done) (mk v S)
    rw [pushN_run] at he
    simpa [S₁, Action.run] using he
  obtain ⟨v₂, hu₂, he₂⟩ := copyR_exec body 116 109 107 (by decide) (by decide) (by decide)
    id v S₁ (by simpa [S₁] using h107)
  let S₂ : Stacks 117 A := { S₁ with R := (Function.update S₁.R 109
    (List.replicate B tick ++ blank :: S.R 109)) }
  have he₂' : Exec body (copyR 116 109 107 id) (mk v S₁) (4*B+4) (mk v₂ S₂) := by
    simpa [S₂, S₁, hB] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := clearWords_exec (body := body) [(94 : Fin 117), 116] (by decide) v₂ S₂
  refine ⟨v₃, hu₃.trans hu₂, (Exec.seq he₁ (Exec.seq he₂' he₃)).cast ?_ ?_⟩
  · simp [S₂, S₁, hB, hw]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hk94 : k = 94
      · subst k; simp
      by_cases hk116 : k = 116
      · subst k; simp
      by_cases hk109 : k = 109
      · subst k; simp [S₂, S₁]
      simp [S₂, S₁, hk94, hk116, hk109]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
