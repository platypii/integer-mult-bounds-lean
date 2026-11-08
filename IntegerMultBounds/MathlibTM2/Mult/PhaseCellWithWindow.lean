module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowedSchurResidual

/-! Borrow retained endpoints around a program that changes only its output tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 148 Q A U}

def withWindow (lower upper : Fin 148) (core : Pr P 148 Q A U) : Pr P 148 Q A U :=
  .seq (ucopy lower 141 143) (.seq (ucopy upper 142 143) (.seq core (clearWords [141,142])))

theorem withWindow_exec (lower upper : Fin 148) (hports : [lower,upper,141,142,143].Nodup)
    (core : Pr P 148 Q A U) (a b cost : ℕ) (output : List (Fin (A+4)))
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (ha : (S.R lower).length = a) (hb : (S.R upper).length = b)
    (h141 : S.R 141 = []) (h142 : S.R 142 = []) (h143 : S.R 143 = [])
    (hcore : ∀ vi : HS 148 Q A U,
      let S₀ : Stacks 148 A := {S with R := (Function.update (Function.update S.R
        141 (List.replicate a tick)) 142 (List.replicate b tick))}
      ∃ vf m, vf.user = vi.user ∧ m ≤ cost ∧
        Exec body core (mk vi S₀) m (mk vf {S₀ with R := Function.update S₀.R 132 output})) :
    ∃ v' m, v'.user = v.user ∧ m ≤ (4*a+4)+((4*b+4)+(cost+(2*(a+b)+5))) ∧
      Exec body (withWindow lower upper core) (mk v S) m
        (mk v' {S with R := Function.update S.R 132 output}) := by
  have hlow141 : lower ≠ 141 := by intro he; subst lower; simp at hports
  have hlow143 : lower ≠ 143 := by intro he; subst lower; simp at hports
  have hupp141 : upper ≠ 141 := by intro he; subst upper; simp at hports
  have hupp142 : upper ≠ 142 := by intro he; subst upper; simp at hports
  have hupp143 : upper ≠ 143 := by intro he; subst upper; simp at hports
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 141 (List.replicate a tick)}
  let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 142 (List.replicate b tick)}
  obtain ⟨v₁,hv₁,he₁⟩ := ucopy_exec body (a := lower) (b := 141) (t := 143)
    hlow141 hlow143 (by decide) v S h143
  have he₁' : Exec body (ucopy lower 141 143) (mk v S) (4*a+4) (mk v₁ S₁) := by
    simpa only [ha,h141,List.append_nil] using he₁
  obtain ⟨v₂,hv₂,he₂⟩ := ucopy_exec body (a := upper) (b := 142) (t := 143)
    hupp142 hupp143 (by decide) v₁ S₁ (by simpa [S₁] using h143)
  have he₂' : Exec body (ucopy upper 142 143) (mk v₁ S₁) (4*b+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hupp141,hb,h142] using he₂
  obtain ⟨v₃,m₃,hv₃,hm₃,he₃⟩ := hcore v₂
  let F : Stacks 148 A := {S₂ with R := Function.update S₂.R 132 output}
  obtain ⟨v₄,hv₄,he₄⟩ := clearWords_exec (body := body) [(141 : Fin 148),142] (by decide) v₃ F
  have hlen : ([(141 : Fin 148),142].map (fun k => (F.R k).length)).sum = a+b := by simp [F,S₂,S₁]
  have hfinal : {F with R := fun k => if k ∈ [(141 : Fin 148),142] then [] else F.R k} =
      {S with R := Function.update S.R 132 output} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk141 : k = 141
    · subst k; simp [h141]
    by_cases hk142 : k = 142
    · subst k; simp [h142]
    simp [F,S₂,S₁,hk141,hk142,Function.update_apply]
  refine ⟨v₄,(4*a+4)+((4*b+4)+(m₃+(2*(a+b)+5))),
    hv₄.trans (hv₃.trans (hv₂.trans hv₁)),by omega,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄))).cast (by rw [hlen]; rfl) ?_⟩
  exact congrArg (mk v₄) hfinal

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
