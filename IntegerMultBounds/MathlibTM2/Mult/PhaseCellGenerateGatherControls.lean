module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateOriginControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalAdvanceControls

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
  .seq generateRuntimeWidth (.seq generateWeightWidth
    (.seq cleanOriginController (.seq preparedNaturalAdvanceControls (clearWords [94, 115]))))

def originAndGatherControlsR (A V s t band L w : ℕ) (R : Fin 117 → List (Fin (A+4))) :=
  Function.update (originControlsR A V s t band L R) 91
    (naturalGatherControls A s t band L w ++ R 91)

def generateOriginAndGatherControlsCost (P q s t u band L : ℕ) : ℕ :=
  generateOriginControlsCost P q s t u band L +
    preparedNaturalAdvanceCost (weightWorkspaceWidth P q (2*q+8) t u) s t band L (2*q+8)

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
  obtain ⟨v₄, S₄, m₄, hu₄, hm₄, he₄, hi₄, ho₄, hl₄, hr₄⟩ :=
    preparedNaturalAdvanceControls_exec (body := body) P q w s t u band L hst.le hgroup v₃ S₃ (S.R 109)
      (by simp [S₃, originControlsR, S₂, V]) (by simp [S₃, originControlsR, S₂, S₁])
      (by simp [S₃, originControlsR, S₂, S₁, V]) (by simp [S₃, originControlsR]) (by
        intro k hk
        have h91 : k ≠ (91 : Fin 117) := by intro he; subst k; norm_num at hk
        have h109 : k ≠ (109 : Fin 117) := by intro he; subst k; norm_num at hk
        have h116 : k ≠ (116 : Fin 117) := by intro he; subst k; norm_num at hk
        have h94 : k ≠ (94 : Fin 117) := by intro he; subst k; norm_num at hk
        have h115 : k ≠ (115 : Fin 117) := by intro he; subst k; norm_num at hk
        simpa [S₃, originControlsR, S₂, S₁, h109, h116, h94, h115] using hblank k (by omega)) (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl
        all_goals simpa [S₃, originControlsR, S₂, S₁] using hfresh _ (by simp))
  have hS₄ : S₄ = { S₃ with R := (Function.update S₃.R 91
      (naturalGatherControls A s t band L w ++ S₃.R 91)) } := Stacks.ext hi₄ ho₄ hl₄ hr₄
  subst S₄
  let S₄ : Stacks 117 A := { S₃ with R := (Function.update S₃.R 91
    (naturalGatherControls A s t band L w ++ S₃.R 91)) }
  obtain ⟨v₅, hu₅, he₅⟩ := clearWords_exec (body := body) [(94 : Fin 117), 115] (by decide) v₄ S₄
  have hsum : (([(94 : Fin 117), 115]).map (fun k => (S₄.R k).length)).sum = w+V := by
    simp [S₄, S₃, originControlsR, S₂, S₁]
  refine ⟨v₅, (4*q+5)+(m₂+(m₃+(m₄+(2*(w+V)+5)))), hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp only [generateOriginAndGatherControlsCost, generateOriginControlsCost]
    dsimp only [w, V] at *
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h94 : k = 94
      · subst k; simp [originAndGatherControlsR, originControlsR, hfresh 94 (by simp)]
      by_cases h115 : k = 115
      · subst k; simp [originAndGatherControlsR, originControlsR, hfresh 115 (by simp)]
      simp [S₄, S₃, originAndGatherControlsR, originControlsR, S₂, S₁, h94, h115,
        Function.update_apply, V, w]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
