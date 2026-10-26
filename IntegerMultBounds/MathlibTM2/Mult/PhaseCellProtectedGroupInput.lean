module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellControlledNaturalGroupInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedPublicationControls

/-! Generate both gather and publication controls before consuming the ambient
source. Publication controls survive on the protected side of the solver bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def protectedGroupInput : Pr P₀ 144 Q A U :=
  .seq (embProg groupReg id generateOriginAndGatherControls)
    (.seq protectedPublicationControls (embProg groupReg id rawNaturalGather))

theorem protectedGroupInput_exec (P N q l s t u band L : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hgroup : 0 < (naturalLengthGroup s t band L).length)
    (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (C : ZMod s → GaussianInt) (v : HS 144 Q A U) (S : Stacks 144 A)
    (borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (hbank : embStk groupReg S = naturalGroupInputBank P N q l s t u band L
      (cstream A (2*q+8) (chirpLine s C)) borrowed outTail inp out)
    (h128 : (S.R 128).length = L) (h130 : (S.R 130).length = 2*q+8)
    (hfresh : ∀ k ∈ [(131 : Fin 144),134,135], S.R k = []) :
    let B := (naturalLengthGroup s t band L).length
    let raw := cstream A (2*q+8) (chirpLine s C)
    let rhs := cstream A (2*q+8) ((List.range B).flatMap
      (cellSourceRows L (naturalGroupOrigin s t band L) (fun _ => C)))
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ generateOriginAndGatherControlsCost P q s t u band L+(48*s*(2*q+8)+27)+rawNaturalGatherCost q s ∧
      Exec (embTab groupReg body) protectedGroupInput (mk v S) n (mk v' S') ∧
      embStk groupReg S' = batchInputBank P N q l s t u band L B
        (fun n => (naturalGroupOrigin s t band L n).val) rhs (raw++borrowed) outTail inp out ∧
      (∀ k : Fin 144, 117 ≤ k.val → S'.L k = S.L k) ∧
      (∀ k : Fin 144, 117 ≤ k.val → k ≠ 140 → S'.R k = S.R k) ∧
      S'.R 140 = gatherControls A (naturalScatterGaps s t band L (2*q+8))++S.R 140 := by
  dsimp only
  let ctrl := controlledNaturalGroupInputBank P N q l t u band L C borrowed outTail inp out
  have hbody : ∀ f, embTab groupReg body (id f) = embProg groupReg id (body f) := fun _ => rfl
  obtain ⟨vp,np,hup,hnp,hep⟩ := generateNaturalGroupInputBank_exec (body := body)
    P N q l s t u band L hP hs hst hu hgroup hband hL hLs hA C (embDn groupReg v) borrowed outTail inp out
  obtain ⟨v₁,S₁,he₁,hv₁,hu₁,hbank₁,hoff₁⟩ := exec_emb groupReg_injective hbody hep v rfl S hbank
  have hlow (i : Fin 117) : S₁.R (groupReg i) = ctrl.R i :=
    congrArg (fun S : Stacks 117 A => S.R i) hbank₁
  have hlowFresh : ∀ k ∈ [(88 : Fin 144),89,90,92,94,104,106], S₁.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | simpa [groupReg,ctrl,controlledNaturalGroupInputBank,originAndGatherControlsR,originControlsR,
          naturalGroupInputBank,batchInputBank] using hlow 88
      | simpa [groupReg,ctrl,controlledNaturalGroupInputBank,originAndGatherControlsR,originControlsR,
          naturalGroupInputBank,batchInputBank] using hlow 89
      | simpa [groupReg,ctrl,controlledNaturalGroupInputBank,originAndGatherControlsR,originControlsR,
          naturalGroupInputBank,batchInputBank] using hlow 90
      | simpa [groupReg,ctrl,controlledNaturalGroupInputBank,originAndGatherControlsR,originControlsR,
          naturalGroupInputBank,batchInputBank] using hlow 92
      | simpa [groupReg,ctrl,controlledNaturalGroupInputBank,originAndGatherControlsR,originControlsR,
          naturalGroupInputBank,batchInputBank] using hlow 94
      | simpa [groupReg,ctrl,controlledNaturalGroupInputBank,originAndGatherControlsR,originControlsR,
          naturalGroupInputBank,batchInputBank] using hlow 104
      | simpa [groupReg,ctrl,controlledNaturalGroupInputBank,originAndGatherControlsR,originControlsR,
          naturalGroupInputBank,batchInputBank] using hlow 106
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := protectedPublicationControls_exec (body := embTab groupReg body)
    hst band L (2*q+8) (by omega) hgroup [] v₁ S₁
    (by rw [(hoff₁ 128 (groupReg_off 128 (by decide))).2]; exact h128)
    (by rw [(hoff₁ 130 (groupReg_off 130 (by decide))).2]; exact h130)
    (by simpa [groupReg,ctrl,controlledNaturalGroupInputBank,originAndGatherControlsR,originControlsR]
      using hlow 116)
    (by simpa [groupReg,ctrl,controlledNaturalGroupInputBank,originAndGatherControlsR,
      naturalGroupInputBank,batchInputBank] using hlow 91) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (apply hlowFresh; simp; done)
        | (rw [(hoff₁ _ (groupReg_off _ (by decide))).2]; exact hfresh _ (by simp)))
  let S₂ : Stacks 144 A := { S₁ with R := (Function.update S₁.R 140
    (gatherControls A (naturalScatterGaps s t band L (2*q+8))++S₁.R 140)) }
  have hbank₂ : embStk groupReg S₂ = ctrl := by
    rw [groupProject_updateR S₁ 140 _ (by decide)]; exact hbank₁
  obtain ⟨vr,nr,hur,hnr,her⟩ := gatherControlledNaturalGroupInputBank_exec (body := body)
    P N q l s t u band L hst hgroup C (embDn groupReg v₂) borrowed outTail inp out
  obtain ⟨v₃,S₃,he₃,hv₃,hu₃,hbank₃,hoff₃⟩ := exec_emb groupReg_injective hbody her v₂ rfl S₂ hbank₂
  refine ⟨v₃,S₃,np+(n₂+nr),hu₃.trans (hur.trans (hu₂.trans (hu₁.trans hup))),by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃),hbank₃,?_,?_,?_⟩
  · intro k hk
    exact (hoff₃ k (groupReg_off k hk)).1.trans (hoff₁ k (groupReg_off k hk)).1
  · intro k hk hk140
    exact (hoff₃ k (groupReg_off k hk)).2.trans
      (by simpa [S₂,hk140] using (hoff₁ k (groupReg_off k hk)).2)
  · rw [(hoff₃ 140 (groupReg_off 140 (by decide))).2]
    simp only [S₂,Function.update_self,(hoff₁ 140 (groupReg_off 140 (by decide))).2]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
