module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedColumnEntry

/-! One restoring table-accumulation step driven by a retained folded-row cursor. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def columnEntryStep : Pr P 151 Q A U :=
  .seq (ucopy 137 0 136) (.seq selectedColumnEntry (.act (.push (.rt 137) (fun _ => tick) .done)))

def columnEntryStepCost (q V n x : ℕ) : ℕ := (4*n+4)+(selectedColumnEntryCost q V n x+1)

theorem columnEntryStep_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V n : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^V) (hn : n < B.card) (C : ZMod s → GaussianInt)
    (pageTail tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hcursor : (S.R 137).length = n) (hwidth : (S.R 115).length = V)
    (hpage : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hq : (S.R 119).length = q)
    (hsource : S.R 110 = cstream A (2*q+8) (chirpLine s C)++tail)
    (h0 : S.R 0 = []) (h94 : S.R 94 = []) (h106 : S.R 106 = [])
    (h135 : S.R 135 = []) (h136 : S.R 136 = []) (h139 : S.R 139 = [])
    (hblank : ∀ r : Fin 151, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ columnEntryStepCost q V n (bFoldAt s B n).val ∧
      Exec body columnEntryStep (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 132
          (csyms A (2*q+8) (C (bFoldAt s B n))++S.R 132)) 137 (tick::S.R 137))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (a := 137) (b := 0) (t := 136)
    (by decide) (by decide) (by decide) v S h136
  let S₁ : Stacks 151 A := {S with R := Function.update S.R 0 (List.replicate n tick)}
  have he₁' : Exec body (ucopy 137 0 136) (mk v S) (4*n+4) (mk v₁ S₁) := by
    simpa [S₁,hcursor,h0] using he₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂,hi,hpos,hread⟩ := selectedColumnEntry_exec (body := body)
    B q V n hA hs hn C pageTail tail v₁ S₁ (by simp [S₁])
    (by simpa [S₁] using hwidth) (by simpa [S₁] using hpage)
    (by simpa [S₁] using hq) (by simpa [S₁] using hsource)
    (by simpa [S₁] using h94) (by simpa [S₁] using h106)
    (by simpa [S₁] using h135) (by simpa [S₁] using h139) (by
      intro r hr1 hr7
      have hr0 : r ≠ 0 := by omega
      simpa [S₁,hr0] using hblank r hr1 hr7)
  let output := csyms A (2*q+8) (C (bFoldAt s B n))++S.R 132
  let S₂ : Stacks 151 A := {S with R := Function.update S.R 132 output}
  have he₂' : Exec body selectedColumnEntry (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    convert he₂ using 1
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk0 : k = 0 <;> by_cases hk132 : k = 132 <;> simp_all [S₂,S₁,output]
  have he₃ := Exec.act (body := body) (.push (.rt 137) (fun _ => tick) .done) (mk v₂ S₂)
  refine ⟨v₂,(4*n+4)+(m₂+1),hu₂.trans hu₁,Nat.add_le_add_left (Nat.add_le_add_right hm₂ 1) _,
    (Exec.seq he₁' (Exec.seq he₂' he₃)).cast rfl ?_⟩
  simp [S₂,output,Action.run,update_rt]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
