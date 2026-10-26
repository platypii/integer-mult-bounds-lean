module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteHaloGatherControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateHaloClassControls

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

def generateHaloOriginAndGatherControls : Pr P₀ 117 Q A U :=
  .seq prepareHaloClassControls completeGatherControls

def haloOriginAndGatherControlsR (A V s t band a b L w : ℕ) (R : Fin 117 → List (Fin (A+4))) :=
  Function.update (haloClassControlsR A V s t band a b L R) 91
    (haloGatherControls A s t band a b L w ++ R 91)

def generateHaloOriginAndGatherControlsCost (P q s t u band a b L : ℕ) : ℕ :=
  generateHaloClassControlsCost P q s t u band a b L +
    preparedHaloAdvanceCost (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L (2*q+8)

theorem completed_preparedHaloClassR (A P q s t u band a b L : ℕ) (R : Fin 117 → List (Fin (A+4)))
    (h94 : R 94 = []) (h115 : R 115 = []) :
    completedHaloGatherR A s t band a b L (2*q+8) (preparedHaloClassR A P q s t u band a b L R) =
      haloOriginAndGatherControlsR A (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L (2*q+8) R := by
  funext k
  by_cases hk94 : k = 94
  · subst k; simp [completedHaloGatherR,haloOriginAndGatherControlsR,haloClassControlsR,h94]
  by_cases hk115 : k = 115
  · subst k; simp [completedHaloGatherR,haloOriginAndGatherControlsR,haloClassControlsR,h115]
  simp [completedHaloGatherR,preparedHaloClassR,haloOriginAndGatherControlsR,haloClassControlsR,
    Function.update_apply,hk94,hk115]

theorem generateHaloOriginAndGatherControls_exec (P q s t u band a b L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b) (hLSrc : (S.R 102).length = L)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115, 116, 88, 89, 90], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generateHaloOriginAndGatherControlsCost P q s t u band a b L ∧
      Exec body generateHaloOriginAndGatherControls (mk v S) m
        (mk v' { S with R := haloOriginAndGatherControlsR A (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L (2*q+8) S.R }) := by
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareHaloClassControls_exec (body := body)
    P q s t u band a b L hP hs hst hu hband has hbs hL hLs hA v S hPSrc hq hsSrc htSrc huSrc hbSrc haSrc hbEndSrc hLSrc hblank (by
      intro k hk
      apply hfresh k
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)
  let S₁ : Stacks 117 A := { S with R := preparedHaloClassR A P q s t u band a b L S.R }
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := completeHaloGatherControls_exec (body := body)
    P q w s t u band a b L hst.le hgroup v₁ S₁ (S.R 109)
    (by simp [S₁,preparedHaloClassR,haloClassControlsR,w])
    (by simp [S₁,preparedHaloClassR,haloClassControlsR,w])
    (by simp [S₁,preparedHaloClassR,haloClassControlsR,w])
    (by simp [S₁,preparedHaloClassR,haloClassControlsR]) (by
      intro k hk
      have hn (n : ℕ) (hn : 19 ≤ n) : k.val ≠ n := by omega
      simpa [S₁,preparedHaloClassR,haloClassControlsR,Function.update_apply,Fin.ext_iff,
        hn 94 (by decide),hn 115 (by decide),hn 109 (by decide),hn 116 (by decide)] using hblank k (by omega)) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      all_goals simpa [S₁,preparedHaloClassR,haloClassControlsR] using hfresh _ (by simp))
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · dsimp only [generateHaloOriginAndGatherControlsCost,generateHaloClassControlsCost,prepareHaloClassControlsCost] at *
    dsimp only [w,V] at *
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    exact completed_preparedHaloClassR A P q s t u band a b L S.R (hfresh 94 (by simp)) (hfresh 115 (by simp))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
