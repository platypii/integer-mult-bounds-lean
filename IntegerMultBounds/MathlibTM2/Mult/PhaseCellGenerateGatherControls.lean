module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteGatherControls

/-! Generate origin packets, batch count and RHS sweep controls together from
ordinary parameters. One pair of generated width sources serves both controllers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateOriginAndGatherControls : Pr P₀ 117 Q A U :=
  .seq prepareOriginControls completeGatherControls

def originAndGatherControlsR (A V s t band L w : ℕ) (R : Fin 117 → List (Fin (A+4))) :=
  Function.update (originControlsR A V s t band L R) 91
    (naturalGatherControls A s t band L w ++ R 91)

def generateOriginAndGatherControlsCost (P q s t u band L : ℕ) : ℕ :=
  generateOriginControlsCost P q s t u band L +
    preparedNaturalAdvanceCost (weightWorkspaceWidth P q (2*q+8) t u) s t band L (2*q+8)

theorem completed_preparedOriginR (A P q s t u band L : ℕ) (R : Fin 117 → List (Fin (A+4)))
    (h94 : R 94 = []) (h115 : R 115 = []) :
    completedGatherR A s t band L (2*q+8) (preparedOriginR A P q s t u band L R) =
      originAndGatherControlsR A (weightWorkspaceWidth P q (2*q+8) t u) s t band L (2*q+8) R := by
  funext k
  by_cases hk94 : k = 94
  · subst k; simp [completedGatherR,originAndGatherControlsR,originControlsR,h94]
  by_cases hk115 : k = 115
  · subst k; simp [completedGatherR,originAndGatherControlsR,originControlsR,h115]
  simp [completedGatherR,preparedOriginR,originAndGatherControlsR,originControlsR,
    Function.update_apply,hk94,hk115]

theorem generateOriginAndGatherControls_exec (P q s t u band L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hgroup : 0 < (naturalLengthGroup s t band L).length) (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hLSrc : (S.R 102).length = L)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115, 116, 88, 89, 90], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generateOriginAndGatherControlsCost P q s t u band L ∧
      Exec body generateOriginAndGatherControls (mk v S) m
        (mk v' { S with R := originAndGatherControlsR A (weightWorkspaceWidth P q (2*q+8) t u) s t band L (2*q+8) S.R }) := by
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareOriginControls_exec (body := body)
    P q s t u band L hP hs hst hu hband hL hLs hA v S hPSrc hq hsSrc htSrc huSrc hbSrc hLSrc hblank (by
      intro k hk
      apply hfresh k
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)
  let S₁ : Stacks 117 A := { S with R := preparedOriginR A P q s t u band L S.R }
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := completeGatherControls_exec (body := body)
    P q w s t u band L hst.le hgroup v₁ S₁ (S.R 109)
    (by simp [S₁,preparedOriginR,originControlsR,w])
    (by simp [S₁,preparedOriginR,originControlsR,w])
    (by simp [S₁,preparedOriginR,originControlsR,w])
    (by simp [S₁,preparedOriginR,originControlsR]) (by
      intro k hk
      have hn (n : ℕ) (hn : 19 ≤ n) : k.val ≠ n := by omega
      simpa [S₁,preparedOriginR,originControlsR,Function.update_apply,Fin.ext_iff,
        hn 94 (by decide),hn 115 (by decide),hn 109 (by decide),hn 116 (by decide)] using hblank k (by omega)) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      all_goals simpa [S₁,preparedOriginR,originControlsR] using hfresh _ (by simp))
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · dsimp only [generateOriginAndGatherControlsCost,generateOriginControlsCost,prepareOriginControlsCost] at *
    dsimp only [w,V] at *
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    exact completed_preparedOriginR A P q s t u band L S.R (hfresh 94 (by simp)) (hfresh 115 (by simp))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
