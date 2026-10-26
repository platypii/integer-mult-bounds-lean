module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateGatherControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProbePreparedOrigins

/-! Runtime selection after one origin scan. Empty classes release the width
headers; nonempty classes continue from the same retained origins and count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def probeAndGatherControls : Pr P₀ 117 Q A U :=
  .seq probePreparedOrigins (.seq (.cond (·.flag) completeGatherControls (clearWords [94,115])) (.act (peekR 116)))

def probedGatherR (A P q s t u band L : ℕ) (R : Fin 117 → List (Fin (A+4))) :=
  if 0 < (naturalLengthGroup s t band L).length then
    originAndGatherControlsR A (weightWorkspaceWidth P q (2*q+8) t u) s t band L (2*q+8) R else R

def probeAndGatherControlsCost (P q s t u band L : ℕ) : ℕ :=
  generateOriginControlsCost P q s t u band L+
    (if 0 < (naturalLengthGroup s t band L).length then
      preparedNaturalAdvanceCost (weightWorkspaceWidth P q (2*q+8) t u) s t band L (2*q+8) else 0)+3

theorem probeAndGatherControls_exec (P q s t u band L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hLSrc : (S.R 102).length = L)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115, 116, 88, 89, 90], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ v'.flag = decide (0 < (naturalLengthGroup s t band L).length) ∧ m ≤ probeAndGatherControlsCost P q s t u band L ∧
      Exec body probeAndGatherControls (mk v S) m
        (mk v' { S with R := probedGatherR A P q s t u band L S.R }) := by
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁,n₁,hu₁,hflag₁,hn₁,he₁⟩ := probePreparedOrigins_exec (body := body)
    P q s t u band L hP hs hst hu hband hL hLs hA v S hPSrc hq hsSrc htSrc huSrc hbSrc hLSrc hblank (by
      intro k hk
      apply hfresh k
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)
  let S₁ : Stacks 117 A := { S with R := preparedOriginR A P q s t u band L S.R }
  let S₂ : Stacks 117 A := { S with R := probedGatherR A P q s t u band L S.R }
  have hbranch : ∃ v₂ n₂, v₂.user = v₁.user ∧
      n₂ ≤ (if 0 < (naturalLengthGroup s t band L).length then
        preparedNaturalAdvanceCost V s t band L w else 0)+(2*(w+V)+5)+1 ∧
      Exec body (.cond (·.flag) completeGatherControls (clearWords [94,115])) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    by_cases hB : 0 < (naturalLengthGroup s t band L).length
    · obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := completeGatherControls_exec (body := body)
        P q w s t u band L hst.le hB v₁ S₁ (S.R 109)
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
      have he₂' : Exec body completeGatherControls (mk v₁ S₁) n₂ (mk v₂ S₂) := by
        refine he₂.cast rfl ?_
        congr 1
        ext1
        · rfl
        · rfl
        · rfl
        simpa only [S₂,probedGatherR,ite_eq_left hB,S₁,w] using
          completed_preparedOriginR A P q s t u band L S.R (hfresh 94 (by simp)) (hfresh 115 (by simp))
      refine ⟨v₂,n₂+1,hu₂,by simpa only [ite_eq_left hB] using Nat.add_le_add_right hn₂ 1,
        Exec.cond_true (by change v₁.flag = true; simpa only [hflag₁,decide_eq_true_eq] using hB) he₂'⟩
    · have hzero : (naturalLengthGroup s t band L).length = 0 := by omega
      obtain ⟨v₂,hu₂,he₂⟩ := releaseEmptyPreparedOrigins_exec (body := body) P q s t u band L hzero v₁ S
        (hfresh 94 (by simp)) (hfresh 115 (by simp)) (hfresh 116 (by simp))
      refine ⟨v₂,(2*(w+V)+5)+1,hu₂,by simp [hB],?_⟩
      apply Exec.cond_false (by change v₁.flag = false; simpa only [hflag₁,decide_eq_false_iff_not] using hB)
      simpa only [S₂,probedGatherR,ite_eq_right hB] using he₂
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := hbranch
  have hflag₂ : (S₂.R 116).head?.isSome = decide (0 < (naturalLengthGroup s t band L).length) := by
    cases he : (naturalLengthGroup s t band L).length <;>
      simp [S₂,probedGatherR,originAndGatherControlsR,originControlsR,he,hfresh 116 (by simp)]
  have hp := Exec.act (body := body) (peekR 116) (mk v₂ S₂)
  rw [peekR_run,hflag₂] at hp
  refine ⟨{ v₂ with flag := decide (0 < (naturalLengthGroup s t band L).length) },n₁+(n₂+1),
    hu₂.trans hu₁,rfl,?_,Exec.seq he₁ (Exec.seq he₂ hp)⟩
  dsimp only [probeAndGatherControlsCost,generateOriginControlsCost,prepareOriginControlsCost] at *
  dsimp only [w,V] at *
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
