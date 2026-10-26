module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateHaloGatherControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProbePreparedHaloOrigins

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

def probeAndGatherHaloControls : Pr P₀ 117 Q A U :=
  .seq probePreparedHaloOrigins (.seq (.cond (·.flag) completeGatherControls (clearWords [94,115])) (.act (peekR 116)))

def probedHaloGatherR (A P q s t u band a b L : ℕ) (R : Fin 117 → List (Fin (A+4))) :=
  if 0 < (haloLengthGroup s t band a b L).length then
    haloOriginAndGatherControlsR A (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L (2*q+8) R else R

def probeAndGatherHaloControlsCost (P q s t u band a b L : ℕ) : ℕ :=
  generateHaloClassControlsCost P q s t u band a b L+
    (if 0 < (haloLengthGroup s t band a b L).length then
      preparedHaloAdvanceCost (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L (2*q+8) else 0)+3

theorem probeAndGatherHaloControls_exec (P q s t u band a b L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b) (hLSrc : (S.R 102).length = L)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115, 116, 88, 89, 90], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ v'.flag = decide (0 < (haloLengthGroup s t band a b L).length) ∧ m ≤ probeAndGatherHaloControlsCost P q s t u band a b L ∧
      Exec body probeAndGatherHaloControls (mk v S) m
        (mk v' { S with R := probedHaloGatherR A P q s t u band a b L S.R }) := by
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁,n₁,hu₁,hflag₁,hn₁,he₁⟩ := probePreparedHaloOrigins_exec (body := body)
    P q s t u band a b L hP hs hst hu hband has hbs hL hLs hA v S hPSrc hq hsSrc htSrc huSrc hbSrc haSrc hbEndSrc hLSrc hblank (by
      intro k hk
      apply hfresh k
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp)
  let S₁ : Stacks 117 A := { S with R := preparedHaloClassR A P q s t u band a b L S.R }
  let S₂ : Stacks 117 A := { S with R := probedHaloGatherR A P q s t u band a b L S.R }
  have hbranch : ∃ v₂ n₂, v₂.user = v₁.user ∧
      n₂ ≤ (if 0 < (haloLengthGroup s t band a b L).length then
        preparedHaloAdvanceCost V s t band a b L w else 0)+(2*(w+V)+5)+1 ∧
      Exec body (.cond (·.flag) completeGatherControls (clearWords [94,115])) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    by_cases hB : 0 < (haloLengthGroup s t band a b L).length
    · obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := completeHaloGatherControls_exec (body := body)
        P q w s t u band a b L hst.le hB v₁ S₁ (S.R 109)
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
      have he₂' : Exec body completeGatherControls (mk v₁ S₁) n₂ (mk v₂ S₂) := by
        refine he₂.cast rfl ?_
        congr 1
        ext1
        · rfl
        · rfl
        · rfl
        simpa only [S₂,probedHaloGatherR,ite_eq_left hB,S₁,w] using
          completed_preparedHaloClassR A P q s t u band a b L S.R (hfresh 94 (by simp)) (hfresh 115 (by simp))
      refine ⟨v₂,n₂+1,hu₂,by simpa only [ite_eq_left hB] using Nat.add_le_add_right hn₂ 1,
        Exec.cond_true (by change v₁.flag = true; simpa only [hflag₁,decide_eq_true_eq] using hB) he₂'⟩
    · have hzero : (haloLengthGroup s t band a b L).length = 0 := by omega
      obtain ⟨v₂,hu₂,he₂⟩ := releaseEmptyPreparedHaloOrigins_exec (body := body) P q s t u band a b L hzero v₁ S
        (hfresh 94 (by simp)) (hfresh 115 (by simp)) (hfresh 116 (by simp))
      refine ⟨v₂,(2*(w+V)+5)+1,hu₂,by simp [hB],?_⟩
      apply Exec.cond_false (by change v₁.flag = false; simpa only [hflag₁,decide_eq_false_iff_not] using hB)
      simpa only [S₂,probedHaloGatherR,ite_eq_right hB] using he₂
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := hbranch
  have hflag₂ : (S₂.R 116).head?.isSome = decide (0 < (haloLengthGroup s t band a b L).length) := by
    cases he : (haloLengthGroup s t band a b L).length <;>
      simp [S₂,probedHaloGatherR,haloOriginAndGatherControlsR,haloClassControlsR,he,hfresh 116 (by simp)]
  have hp := Exec.act (body := body) (peekR 116) (mk v₂ S₂)
  rw [peekR_run,hflag₂] at hp
  refine ⟨{ v₂ with flag := decide (0 < (haloLengthGroup s t band a b L).length) },n₁+(n₂+1),
    hu₂.trans hu₁,rfl,?_,Exec.seq he₁ (Exec.seq he₂ hp)⟩
  dsimp only [probeAndGatherHaloControlsCost,generateHaloClassControlsCost,prepareHaloClassControlsCost] at *
  dsimp only [w,V] at *
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
