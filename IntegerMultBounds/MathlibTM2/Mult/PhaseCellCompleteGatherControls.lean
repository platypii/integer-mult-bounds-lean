module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateOriginControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalAdvanceControls

/-! Complete gather-control generation from the retained origin/count/width
handoff. The origin scan is reused, and both width headers are released. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def completeGatherControls : Pr P₀ 117 Q A U :=
  .seq preparedNaturalAdvanceControls (clearWords [94,115])

def completedGatherR (A s t band L w : ℕ) (R : Fin 117 → List (Fin (A+4))) :=
  fun k => if k = 94 ∨ k = 115 then [] else
    Function.update R 91 (naturalGatherControls A s t band L w++R 91) k

theorem completeGatherControls_exec (P q w s t u band L : ℕ) (hst : s ≤ t)
    (hgroup : 0 < (naturalLengthGroup s t band L).length)
    (v : HS 117 Q A U) (S : Stacks 117 A) (suffix : List (Fin (A+4)))
    (hV : (S.R 115).length = weightWorkspaceWidth P q w t u) (hw : (S.R 94).length = w)
    (hsrc : S.R 109 = naturalOriginPackets A (weightWorkspaceWidth P q w t u) s t band L++suffix)
    (hcount : S.R 116 = List.replicate (naturalLengthGroup s t band L).length tick)
    (hblank : ∀ k : Fin 117, k.val < 19 → S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117),89,90,106], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ preparedNaturalAdvanceCost (weightWorkspaceWidth P q w t u) s t band L w+
        (2*(w+weightWorkspaceWidth P q w t u)+5) ∧
      Exec body completeGatherControls (mk v S) n
        (mk v' { S with R := completedGatherR A s t band L w S.R }) := by
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hi₁,ho₁,hl₁,hr₁⟩ := preparedNaturalAdvanceControls_exec (body := body)
    P q w s t u band L hst hgroup v S suffix hV hw hsrc hcount hblank hfresh
  have hS₁ : S₁ = { S with R := Function.update S.R 91 (naturalGatherControls A s t band L w++S.R 91) } :=
    Stacks.ext hi₁ ho₁ hl₁ hr₁
  subst S₁
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 91 (naturalGatherControls A s t band L w++S.R 91) }
  obtain ⟨v₂,hu₂,he₂⟩ := clearWords_exec (body := body) [(94 : Fin 117),115] (by decide) v₁ S₁
  have hsum : (([(94 : Fin 117),115]).map (fun k => (S₁.R k).length)).sum = w+weightWorkspaceWidth P q w t u := by
    simp [S₁,hw,hV]
  refine ⟨v₂,n₁+(2*(w+weightWorkspaceWidth P q w t u)+5),hu₂.trans hu₁,by omega,
    (Exec.seq he₁ he₂).cast (by rw [hsum]; rfl) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  simp [S₁,completedGatherR]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
