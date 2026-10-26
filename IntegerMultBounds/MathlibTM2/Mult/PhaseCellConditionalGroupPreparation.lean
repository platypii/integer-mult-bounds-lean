module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProbedNaturalGroupInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseEmptyGroup

/-! Runtime preparation of an installed length class. Empty classes release
all private headers and the current length; nonempty classes retain the exact
controlled bank needed by publication setup and the numerical continuation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def conditionalGroupPreparation : Pr P₀ 144 Q A U :=
  .seq installGroupHeaders (.seq (embProg groupReg id probeAndGatherControls)
    (.seq (.cond (·.flag) (.act .done) releaseEmptyGroup) (.act (peekR 116))))

def conditionalGroupPreparationCost (P N q l s t u band L : ℕ) : ℕ :=
  installGroupHeadersCost P N q l s t u band L+probeAndGatherControlsCost P q s t u band L+
    (if 0 < (naturalLengthGroup s t band L).length then 1 else
      2*(P+N+q+l+s+t+u+band+3*L)+23)+2

theorem conditionalGroupPreparation_exec (P N q l s t u band L : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (C : ZMod s → GaussianInt) (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed : List (Fin (A+4)))
    (hmasters : ∀ r ∈ groupHeaderCopies, (S.R r.1).length = groupHeaderValue P N q l s t u band L r.1)
    (hleft : ∀ k : Fin 144, k.val < 117 → S.L k = [])
    (hblank : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hsrc : S.R 110 = cstream A (2*q+8) (chirpLine s C)++borrowed) (h133 : S.R 133 = []) :
    ∃ v' S' n, v'.user = v.user ∧ v'.flag = decide (0 < (naturalLengthGroup s t band L).length) ∧
      n ≤ conditionalGroupPreparationCost P N q l s t u band L ∧
      Exec (embTab groupReg body) conditionalGroupPreparation (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (if 0 < (naturalLengthGroup s t band L).length then
        embStk groupReg S' = controlledNaturalGroupInputBank P N q l t u band L C borrowed (S.R 93) S.inp S.out ∧
        ∀ k : Fin 144, 117 ≤ k.val → S'.R k = S.R k
       else S'.R = Function.update S.R 128 []) := by
  obtain ⟨v₁,hu₁,he₁⟩ := installGroupHeaders_exec (body := embTab groupReg body)
    P N q l s t u band L v S hmasters h133
  let S₁ : Stacks 144 A := { S with R := copiedGroupR P N q l s t u band L S.R }
  have hbank₁ := copiedGroup_project P N q l s t u band L S
    (cstream A (2*q+8) (chirpLine s C)) borrowed hleft hblank hsrc
  obtain ⟨vp,np,hup,hfp,hnp,hep⟩ := probeNaturalGroupInputBank_exec (body := body)
    P N q l s t u band L hP hs hst hu hband hL hLs hA C (embDn groupReg v₁) borrowed (S.R 93) S.inp S.out
  have hbody : ∀ f, embTab groupReg body (id f) = embProg groupReg id (body f) := fun _ => rfl
  obtain ⟨v₂,S₂,he₂,hv₂,hu₂,hbank₂,hoff₂⟩ := exec_emb groupReg_injective hbody hep v₁ rfl S₁ hbank₁
  have hflag₂ : v₂.flag = decide (0 < (naturalLengthGroup s t band L).length) :=
    (congrArg (fun v : HS 117 Q A U => v.flag) hv₂).trans hfp
  have hR₂ (k : Fin 144) (hk : 117 ≤ k.val) : S₂.R k = S.R k :=
    (hoff₂ k (groupReg_off k hk)).2.trans (copiedGroupR_off P N q l s t u band L S.R k hk)
  have hi₂ : S₂.inp = S.inp := by
    have hh := congrArg (fun B : Stacks 117 A => B.inp) hbank₂
    by_cases hB : 0 < (naturalLengthGroup s t band L).length <;>
      simpa [embStk,probedNaturalGroupInputBank,hB,controlledNaturalGroupInputBank,naturalGroupInputBank,batchInputBank] using hh
  have ho₂ : S₂.out = S.out := by
    have hh := congrArg (fun B : Stacks 117 A => B.out) hbank₂
    by_cases hB : 0 < (naturalLengthGroup s t band L).length <;>
      simpa [embStk,probedNaturalGroupInputBank,hB,controlledNaturalGroupInputBank,naturalGroupInputBank,batchInputBank] using hh
  have hL₂ : S₂.L = S.L := by
    funext k
    by_cases hk : k.val < 117
    · let i : Fin 117 := ⟨k.val,hk⟩
      have hi : groupReg i = k := Fin.ext rfl
      have hh := congrArg (fun B : Stacks 117 A => B.L i) hbank₂
      have hz : S₂.L k = [] := by
        by_cases hB : 0 < (naturalLengthGroup s t band L).length <;>
          simpa [embStk,Function.comp_apply,hi,probedNaturalGroupInputBank,hB,controlledNaturalGroupInputBank,
            naturalGroupInputBank,batchInputBank] using hh
      rw [hz,hleft k hk]
    · exact (hoff₂ k (groupReg_off k (by omega))).1
  let S₃ : Stacks 144 A := if 0 < (naturalLengthGroup s t band L).length then S₂ else
    { S with R := Function.update S.R 128 [] }
  have hbranch : ∃ v₃ n₃, v₃.user = v₂.user ∧
      n₃ ≤ (if 0 < (naturalLengthGroup s t band L).length then 1 else
        2*(P+N+q+l+s+t+u+band+3*L)+23)+1 ∧
      Exec (embTab groupReg body) (.cond (·.flag) (.act .done) releaseEmptyGroup) (mk v₂ S₂) n₃ (mk v₃ S₃) := by
    by_cases hB : 0 < (naturalLengthGroup s t band L).length
    · refine ⟨v₂,2,rfl,by simp [hB],Exec.cond_true ?_ ?_⟩
      · change v₂.flag = true
        simp [hflag₂,hB]
      · simpa [S₃,hB,Action.run] using Exec.act (body := embTab groupReg body) .done (mk v₂ S₂)
    · have hbank₂' : embStk groupReg S₂ = embStk groupReg S₁ := by
        rw [hbank₁]
        simpa only [probedNaturalGroupInputBank,ite_eq_right hB] using hbank₂
      have heq : S₂ = S₁ := groupStacks_eq S₂ S₁ hbank₂'
        (fun k hk => (hoff₂ k (groupReg_off k hk)).1) (fun k hk => (hoff₂ k (groupReg_off k hk)).2)
      obtain ⟨v₃,hu₃,he₃⟩ := releaseEmptyGroup_exec (body := embTab groupReg body)
        P N q l s t u band L v₂ S (by
          intro r hr
          simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals apply hblank <;> decide) (by
          have hh := hmasters (128,102) (by simp [groupHeaderCopies])
          simpa [groupHeaderValue] using hh)
      refine ⟨v₃,(2*(P+N+q+l+s+t+u+band+3*L)+23)+1,hu₃,by simp [hB],Exec.cond_false ?_ ?_⟩
      · change v₂.flag = false
        simp [hflag₂,hB]
      · simpa only [heq,S₁,S₃,ite_eq_right hB] using he₃
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := hbranch
  have hflag₃ : (S₃.R 116).head?.isSome = decide (0 < (naturalLengthGroup s t band L).length) := by
    by_cases hB : 0 < (naturalLengthGroup s t band L).length
    · have hh := congrArg (fun B : Stacks 117 A => B.R 116) hbank₂
      have he : S₂.R 116 = List.replicate (naturalLengthGroup s t band L).length tick := by
        simpa [embStk,groupReg,probedNaturalGroupInputBank,controlledNaturalGroupInputBank,
          originAndGatherControlsR,originControlsR,hB] using hh
      simp only [S₃,ite_eq_left hB,he]
      cases hn : (naturalLengthGroup s t band L).length with
      | zero => omega
      | succ n => simp
    · simp [S₃,hB,hblank 116 (by decide) (by decide) (by decide)]
  have hp := Exec.act (body := embTab groupReg body) (peekR 116) (mk v₃ S₃)
  rw [peekR_run,hflag₃] at hp
  refine ⟨{ v₃ with flag := decide (0 < (naturalLengthGroup s t band L).length) },S₃,
    installGroupHeadersCost P N q l s t u band L+(np+(n₃+1)),
    hu₃.trans (hu₂.trans (hup.trans hu₁)),rfl,?_,Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ hp)),?_,?_,?_,?_⟩
  · dsimp only [conditionalGroupPreparationCost]
    omega
  · by_cases hB : 0 < (naturalLengthGroup s t band L).length
    · simpa [S₃,hB] using hi₂
    · simp [S₃,hB]
  · by_cases hB : 0 < (naturalLengthGroup s t band L).length
    · simpa [S₃,hB] using ho₂
    · simp [S₃,hB]
  · by_cases hB : 0 < (naturalLengthGroup s t band L).length
    · simpa [S₃,hB] using hL₂
    · simp [S₃,hB]
  · by_cases hB : 0 < (naturalLengthGroup s t band L).length
    · simp only [ite_eq_left hB,S₃]
      exact ⟨by simpa only [probedNaturalGroupInputBank,ite_eq_left hB] using hbank₂,hR₂⟩
    · simp [S₃,hB]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
