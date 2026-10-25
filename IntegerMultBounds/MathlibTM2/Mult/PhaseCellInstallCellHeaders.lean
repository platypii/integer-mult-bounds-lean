module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Replace construction headers by the single-cell arithmetic ABI. The q/l/P
sources and old iteration counter are owned input and explicitly consumed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def installCellHeaders : Pr P₀ 117 Q A U :=
  .seq (uclear 101) (.seq (ucopy 112 100 104) (.seq (ucopy 109 101 104)
    (.seq (umul 2 112 94 104) (.seq
      (.act (pushN 94 (fun _ => tick) 8 (pushN 108 (fun _ => tick) 2 .done)))
      (clearWords [109, 112, 114])))))

def installCellHeadersCost (P M q l : ℕ) : ℕ := 2 * M + 2 * P + 10 * q + 6 * l + 22

def cellHeaderBank {A : ℕ} (S : Stacks 117 A) (q l : ℕ) : Stacks 117 A :=
  { S with R := (fun k => if k = 100 then List.replicate q tick else
    if k = 101 then List.replicate l tick else if k = 94 then List.replicate (2 * q + 8) tick else
    if k = 108 then List.replicate 2 tick else if k ∈ [(109 : Fin 117), 112, 114] then [] else S.R k) }

theorem installCellHeaders_exec (P M q l : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hM : (S.R 101).length = M)
    (hq : (S.R 112).length = q) (hl : (S.R 109).length = l)
    (hfresh : ∀ k ∈ [(94 : Fin 117), 100, 104, 108], S.R k = []) :
    ∃ v', v'.user = v.user ∧ Exec body installCellHeaders (mk v S)
      (installCellHeadersCost P M q l) (mk v' (cellHeaderBank S q l)) := by
  obtain ⟨v₁, hu₁, he₁⟩ := uclear_exec body 101 v S
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 101 [] }
  obtain ⟨v₂, hu₂, he₂⟩ := ucopy_exec (body := body) (a := 112) (b := 100) (t := 104)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 104 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 100 (List.replicate q tick) }
  have he₂' : Exec body (ucopy 112 100 104) (mk v₁ S₁) (4 * q + 4) (mk v₂ S₂) := by
    simpa [S₂, S₁, hq, hfresh 100 (by simp)] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := ucopy_exec (body := body) (a := 109) (b := 101) (t := 104)
    (by decide) (by decide) (by decide) v₂ S₂ (by simpa [S₂, S₁] using hfresh 104 (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 101 (List.replicate l tick) }
  have he₃' : Exec body (ucopy 109 101 104) (mk v₂ S₂) (4 * l + 4) (mk v₃ S₃) := by
    simpa [S₃, S₂, S₁, hl] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := umul_exec (body := body) 2 (a := 112) (b := 94) (t := 104)
    (by decide) (by decide) (by decide) v₃ S₃ (by simpa [S₃, S₂, S₁] using hfresh 104 (by simp))
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 94 (List.replicate (2 * q) tick) }
  have he₄' : Exec body (umul 2 112 94 104) (mk v₃ S₃) (4 * q + 4) (mk v₄ S₄) := by
    simpa [S₄, S₃, S₂, S₁, hq, hfresh 94 (by simp)] using he₄
  let S₅ : Stacks 117 A := { S₄ with R := (Function.update (Function.update S₄.R 94
    (List.replicate (2 * q + 8) tick)) 108 (List.replicate 2 tick)) }
  have he₅ : Exec body (.act (pushN 94 (fun _ => tick) 8 (pushN 108 (fun _ => tick) 2 .done)))
      (mk v₄ S₄) 1 (mk v₄ S₅) := by
    have he := Exec.act (body := body) (pushN 94 (fun _ => tick) 8 (pushN 108 (fun _ => tick) 2 .done)) (mk v₄ S₄)
    rw [pushN_run, pushN_run] at he
    rw [show S₄.R 94 = List.replicate (2 * q) tick by simp [S₄], List.replicate_append_replicate] at he
    simpa [S₅, S₄, S₃, S₂, S₁, Action.run, hfresh 108 (by simp), Nat.add_comm] using he
  obtain ⟨v₆, hu₆, he₆⟩ := clearWords_exec (body := body) [109, 112, 114] (by decide) v₄ S₅
  have hsum : ([(109 : Fin 117), 112, 114].map (fun k => (S₅.R k).length)).sum = l + q + P := by
    simp [S₅, S₄, S₃, S₂, S₁, hl, hq, hP, Nat.add_assoc]
  refine ⟨v₆, hu₆.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' (Exec.seq he₅ he₆))))).cast ?_ ?_⟩
  · rw [hM, hsum]
    unfold installCellHeadersCost
    simp
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h100 : k = 100
      · subst k; simp [cellHeaderBank, S₅, S₄, S₃, S₂, S₁]
      by_cases h101 : k = 101
      · subst k; simp [cellHeaderBank, S₅, S₄, S₃, S₂, S₁]
      by_cases h94 : k = 94
      · subst k; simp [cellHeaderBank, S₅, S₄, S₃, S₂, S₁]
      by_cases h108 : k = 108
      · subst k; simp [cellHeaderBank, S₅, S₄, S₃, S₂, S₁]
      simp [cellHeaderBank, S₅, S₄, S₃, S₂, S₁, h100, h101, h94, h108]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
