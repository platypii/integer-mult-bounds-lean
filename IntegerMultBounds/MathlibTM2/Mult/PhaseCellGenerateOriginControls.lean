module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWeightWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchSetupHeaders

/-! Construct the complete origin/count control input from ordinary parameters,
then release all controller workspace and temporary widths. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateOriginControls : Pr P₀ 117 Q A U :=
  .seq generateRuntimeWidth (.seq generateWeightWidth
    (.seq cleanOriginController (clearWords [94, 115])))

def originControlsR (A V s t band L : ℕ) (R : Fin 117 → List (Fin (A+4))) :=
  Function.update (Function.update R 109 (naturalOriginPackets A V s t band L ++ R 109))
    116 (List.replicate (naturalLengthGroup s t band L).length tick)

def generateOriginControlsCost (P q s t u band L : ℕ) : ℕ :=
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  4*q+5 + weightWidthCost P q w t u +
    unaryOriginControllerCost P q w s t u band L + (62*V+63) + 2*(w+V)+5

theorem generateOriginControls_exec (P q s t u band L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hLSrc : (S.R 102).length = L)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115, 116], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generateOriginControlsCost P q s t u band L ∧
      Exec body generateOriginControls (mk v S) m
        (mk v' { S with R := originControlsR A (weightWorkspaceWidth P q (2*q+8) t u) s t band L S.R }) := by
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁, hu₁, he₁⟩ := generateRuntimeWidth_exec (body := body) q v S hq
    (hfresh 94 (by simp)) (hfresh 104 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 94 (List.replicate w tick) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := generateWeightWidth_exec (body := body) P q w t u v₁ S₁
    (by simpa [S₁] using hPSrc) (by simpa [S₁] using hq) (by simp [S₁])
    (by simpa [S₁] using htSrc) (by simpa [S₁] using huSrc) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [S₁, Function.update_apply]
      all_goals norm_num
      all_goals first | exact hblank _ (by decide) | exact hfresh _ (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 115 (List.replicate V tick) }
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := cleanOriginController_exec (body := body)
    P q w s t u band L hP hs hst hu hband hL hLs hA v₂ S₂
    (by simpa [S₂, S₁] using hsSrc) (by simpa [S₂, S₁] using htSrc)
    (by simpa [S₂, S₁] using hbSrc) (by simpa [S₂, S₁] using hLSrc) (by simp [S₂, V])
    (by simpa [S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₂, S₁] using hfresh 106 (by simp))
    (by simpa [S₂, S₁] using hfresh 116 (by simp)) (by
      intro r
      have hr := originReg_range r
      have h94 : originReg r ≠ (94 : Fin 117) := by intro he; rw [he] at hr; omega
      have h115 : originReg r ≠ (115 : Fin 117) := by intro he; rw [he] at hr; omega
      simpa [S₂, S₁, h94, h115] using hblank _ hr)
  let S₃ : Stacks 117 A := { S₂ with R := originControlsR A V s t band L S₂.R }
  obtain ⟨v₄, hu₄, he₄⟩ := clearWords_exec (body := body) [(94 : Fin 117), 115] (by decide) v₃ S₃
  have hsum : (([(94 : Fin 117), 115]).map (fun k => (S₃.R k).length)).sum = w+V := by
    simp [S₃, originControlsR, S₂, S₁]
  refine ⟨v₄, (4*q+5)+(m₂+(m₃+(2*(w+V)+5))), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp only [generateOriginControlsCost]
    dsimp only [w, V] at *
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h94 : k = 94
      · subst k; simp [S₃, originControlsR, hfresh 94 (by simp)]
      by_cases h115 : k = 115
      · subst k; simp [S₃, originControlsR, hfresh 115 (by simp)]
      simp [S₃, originControlsR, S₂, S₁, h94, h115, Function.update_apply, V, w]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
