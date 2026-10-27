module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNegativeUnitFormat
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate one scaled negative unit from unary precision and word width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def negativeUnitWord (width precision dst rest saved : Fin T) : Pr P₀ T Q A U :=
  .seq (ucopy width rest saved) (.seq (usub precision rest saved)
    (.seq (copyR rest dst saved (fun _ => pairSym A true false))
      (.seq (copyR precision dst saved (fun _ => pairSym A false false)) (uclear rest))))

theorem negativeUnitWord_exec {width precision dst rest saved : Fin T}
    (hreg : [width,precision,dst,rest,saved].Nodup) (w q : ℕ) (hq : q ≤ w)
    (v : HS T Q A U) (S : Stacks T A) (hw : (S.R width).length = w) (hp : (S.R precision).length = q)
    (hrest : S.R rest = []) (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧ Exec body (negativeUnitWord width precision dst rest saved)
      (mk v S) (10*w+2*q+18)
      (mk v' {S with R := (Function.update S.R dst
        (csyms A w (⟨-(2 : ℤ)^q,0⟩ : GaussianInt)++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := width) (b := rest) (t := saved)
    (by assumption) (by assumption) (by assumption) v S hsaved
  let S₁ : Stacks T A := {S with R := Function.update S.R rest (List.replicate w tick)}
  have he₁' : Exec body (ucopy width rest saved) (mk v S) (4*w+4) (mk v₁ S₁) := by
    simpa [S₁,hw,hrest] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := usub_exec (body := body) (a := precision) (b := rest) (t := saved)
    (by assumption) (by assumption) (by assumption) v₁ S₁
    (by simpa [S₁,‹rest ≠ saved›.symm] using hsaved)
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R rest (List.replicate (w-q) tick)}
  have he₂' : Exec body (usub precision rest saved) (mk v₁ S₁) (4*q+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hp,‹precision ≠ rest›] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := copyR_exec body rest dst saved ‹dst ≠ rest›.symm ‹rest ≠ saved› ‹dst ≠ saved›
    (fun _ => pairSym A true false) v₂ S₂ (by simpa [S₂,S₁,‹rest ≠ saved›.symm] using hsaved)
  let S₃ : Stacks T A := {S₂ with R := (Function.update S₂.R dst
    (List.replicate (w-q) (pairSym A true false)++S.R dst))}
  have he₃' : Exec body (copyR rest dst saved (fun _ => pairSym A true false))
      (mk v₂ S₂) (4*(w-q)+4) (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,‹dst ≠ rest›] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := copyR_exec body precision dst saved ‹precision ≠ dst› ‹precision ≠ saved› ‹dst ≠ saved›
    (fun _ => pairSym A false false) v₃ S₃
    (by simpa [S₃,S₂,S₁,‹dst ≠ saved›.symm,‹rest ≠ saved›.symm] using hsaved)
  let S₄ : Stacks T A := {S₃ with R := (Function.update S₃.R dst
    (List.replicate q (pairSym A false false)++S₃.R dst))}
  have he₄' : Exec body (copyR precision dst saved (fun _ => pairSym A false false))
      (mk v₃ S₃) (4*q+4) (mk v₄ S₄) := by
    simpa [S₄,S₃,S₂,S₁,hp,‹precision ≠ dst›,‹precision ≠ rest›] using he₄
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec (body := body) rest v₄ S₄
  refine ⟨v₅,hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' he₅)))).cast ?_ ?_⟩
  · simp [S₄,S₃,S₂,‹dst ≠ rest›.symm]
    omega
  · apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hdst : k = dst <;> by_cases hrest' : k = rest <;>
      simp_all [S₄,S₃,S₂,S₁,csyms_negative_power_two,Function.update_apply,List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
