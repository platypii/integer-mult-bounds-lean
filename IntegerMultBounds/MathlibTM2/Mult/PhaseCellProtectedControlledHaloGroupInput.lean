module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawHaloGroupInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedHaloPublicationControls

/-! Continue from the existing controlled bank: generate protected publication
controls and gather the RHS without repeating origin or gather-control setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def protectedControlledHaloGroupInput : Pr P₀ 144 Q A U :=
  .seq protectedPublicationControls (embProg groupReg id gatherHaloGroupInput)

theorem protectedControlledHaloGroupInput_exec (P N q l s t u band a b L : ℕ) [NeZero s]
    (hst : s < t)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (C : ZMod s → GaussianInt) (v : HS 144 Q A U) (S : Stacks 144 A)
    (borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (hbank : embStk groupReg S = controlledHaloGroupInputBank P N q l t u band a b L C borrowed outTail inp out)
    (h128 : (S.R 128).length = L) (h130 : (S.R 130).length = 2*q+8)
    (hfresh : ∀ k ∈ [(131 : Fin 144),134,135], S.R k = []) :
    let B := (haloLengthGroup s t band a b L).length
    let raw := cstream A (2*q+8) (chirpLine s C)
    let rhs := cstream A (2*q+8) ((List.range B).flatMap
      (cellSourceRows L (haloGroupOrigin s t band a b L) (fun _ => C)))
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ (48*s*(2*q+8)+27)+(rawNaturalGatherCost q s+2*(a+b)+5) ∧
      Exec (embTab groupReg body) protectedControlledHaloGroupInput (mk v S) n (mk v' S') ∧
      embStk groupReg S' = batchInputBank P N q l s t u band L B
        (fun n => (haloGroupOrigin s t band a b L n).val) rhs (raw++borrowed) outTail inp out ∧
      (∀ k : Fin 144, 117 ≤ k.val → S'.L k = S.L k) ∧
      (∀ k : Fin 144, 117 ≤ k.val → k ≠ 140 → S'.R k = S.R k) ∧
      S'.R 140 = gatherControls A (haloScatterGaps s t band a b L (2*q+8))++S.R 140 := by
  dsimp only
  let ctrl := controlledHaloGroupInputBank P N q l t u band a b L C borrowed outTail inp out
  have hbody : ∀ f, embTab groupReg body (id f) = embProg groupReg id (body f) := fun _ => rfl
  have hlow (i : Fin 117) : S.R (groupReg i) = ctrl.R i :=
    congrArg (fun S : Stacks 117 A => S.R i) hbank
  have hlowFresh : ∀ k ∈ [(88 : Fin 144),89,90,92,94,104,106], S.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | simpa [groupReg,ctrl,controlledHaloGroupInputBank,haloOriginAndGatherControlsR,haloClassControlsR,
          haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using hlow 88
      | simpa [groupReg,ctrl,controlledHaloGroupInputBank,haloOriginAndGatherControlsR,haloClassControlsR,
          haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using hlow 89
      | simpa [groupReg,ctrl,controlledHaloGroupInputBank,haloOriginAndGatherControlsR,haloClassControlsR,
          haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using hlow 90
      | simpa [groupReg,ctrl,controlledHaloGroupInputBank,haloOriginAndGatherControlsR,haloClassControlsR,
          haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using hlow 92
      | simpa [groupReg,ctrl,controlledHaloGroupInputBank,haloOriginAndGatherControlsR,haloClassControlsR,
          haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using hlow 94
      | simpa [groupReg,ctrl,controlledHaloGroupInputBank,haloOriginAndGatherControlsR,haloClassControlsR,
          haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using hlow 104
      | simpa [groupReg,ctrl,controlledHaloGroupInputBank,haloOriginAndGatherControlsR,haloClassControlsR,
          haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using hlow 106
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := protectedHaloPublicationControls_exec (body := embTab groupReg body)
    hst band a b L (2*q+8) (by omega) hgroup [] v S
    h128
    h130
    (by simpa [groupReg,ctrl,controlledHaloGroupInputBank,haloOriginAndGatherControlsR,haloClassControlsR]
      using hlow 116)
    (by simpa [groupReg,ctrl,controlledHaloGroupInputBank,haloOriginAndGatherControlsR,
      haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank] using hlow 91) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (apply hlowFresh; simp; done)
        | exact hfresh _ (by simp))
  let S₂ : Stacks 144 A := { S with R := (Function.update S.R 140
    (gatherControls A (haloScatterGaps s t band a b L (2*q+8))++S.R 140)) }
  have hbank₂ : embStk groupReg S₂ = ctrl := by
    rw [groupProject_updateR S 140 _ (by decide)]; exact hbank
  obtain ⟨vr,nr,hur,hnr,her⟩ := finishControlledHaloGroupInput_exec (body := body)
    P N q l s t u band a b L hst hgroup C (embDn groupReg v₂) borrowed outTail inp out
  obtain ⟨v₃,S₃,he₃,hv₃,hu₃,hbank₃,hoff₃⟩ := exec_emb groupReg_injective hbody her v₂ rfl S₂ hbank₂
  refine ⟨v₃,S₃,n₂+nr,hu₃.trans (hur.trans hu₂),by omega,
    Exec.seq he₂ he₃,hbank₃,?_,?_,?_⟩
  · intro k hk
    exact (hoff₃ k (groupReg_off k hk)).1
  · intro k hk hk140
    simpa [S₂,hk140] using (hoff₃ k (groupReg_off k hk)).2
  · simpa only [S₂,Function.update_self] using (hoff₃ 140 (groupReg_off 140 (by decide))).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
