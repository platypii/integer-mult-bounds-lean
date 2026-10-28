module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareOriginWidening

/-! Generate the numerical-width counter, widen geometry packets and erase the counter. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def widenGeometryOrigins : Pr P₀ 117 Q A U :=
  .seq prepareOriginWidening (.seq widenOriginPackets (uclear 19))

def widenGeometryOriginsCost (P q w t u band B : ℕ) : ℕ :=
  let V := haloGeometryWidth t band w
  let W := weightWorkspaceWidth P q w t u
  weightWidthCost P q w t u+4*V+4*W+B*(10*W+10*V+23)+14

theorem widenGeometryOrigins_exec (P q w t u band : ℕ) (hband : band ≤ P)
    (xs : List ℕ) (hfit : ∀ x ∈ xs, x < 2^haloGeometryWidth t band w)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hP : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hw : (S.R 94).length = w) (ht : (S.R 98).length = t) (hu : (S.R 99).length = u)
    (hV : (S.R 115).length = haloGeometryWidth t band w)
    (hcount : (S.R 116).length = xs.length)
    (hsrc : S.R 109 = xs.flatMap (binSyms (haloGeometryWidth t band w))++tail)
    (hfresh : ∀ k ∈ [(0 : Fin 117),1,2,3,4,19,20,21,22,23,24,104,25,26,27], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ widenGeometryOriginsCost P q w t u band xs.length ∧
      Exec body widenGeometryOrigins (mk v S) n
        (mk v' {S with R := (Function.update S.R 109
          (xs.flatMap (binSyms (weightWorkspaceWidth P q w t u))++tail))}) := by
  let V := haloGeometryWidth t band w
  let W := weightWorkspaceWidth P q w t u
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareOriginWidening_exec (body := body) P q w t u V
    v S hP hq hw ht hu hV (by
      intro k hk; apply hfresh k
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 19 (List.replicate W tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := widenOriginPackets_exec (body := body) V W
    (haloGeometryWidth_le_weightWorkspaceWidth hband) xs hfit v₁ S₁ tail
    (by simpa [S₁] using hV) (by simp [S₁])
    (by simpa [S₁] using hcount) (by simpa [S₁] using hsrc) (by
      intro k hk
      have hk19 : k ≠ (19 : Fin 117) := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [S₁,hk19] using hfresh k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 109 (xs.flatMap (binSyms W)++tail)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 19 v₂ S₂
  refine ⟨v₃,n₁+(n₂+(2*W+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · dsimp only [widenGeometryOriginsCost]
    dsimp only [V,W] at *
    omega
  · simp [S₂,S₁]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk19 : k = 19
    · subst k; simp [S₂,S₁,hfresh 19 (by simp)]
    simp [S₂,S₁,hk19,W,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
