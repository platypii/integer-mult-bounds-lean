module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawHaloGroupInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedGroupWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedControlledHaloGroupInput
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

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 148 Q A U}

def cachedProtectedControlledHaloGroupInput : Pr P₀ 148 Q A U :=
  embProg cachedGroupLegacyReg Empty.elim (protectedControlledHaloGroupInput (P₀ := Empty))

theorem cachedProtectedControlledHaloGroupInput_exec (P N q l s t u band a b L : ℕ) [NeZero s]
    (hst : s < t)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (C : ZMod s → GaussianInt) (v : HS 148 Q A U) (S : Stacks 148 A)
    (borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (hbank : embStk groupReg (embStk cachedGroupLegacyReg S) = controlledHaloGroupInputBank P N q l t u band a b L C borrowed outTail inp out)
    (h128 : (S.R 128).length = L) (h130 : (S.R 130).length = 2*q+8)
    (hfresh : ∀ k ∈ [(131 : Fin 148),134,135], S.R k = []) :
    let B := (haloLengthGroup s t band a b L).length
    let raw := cstream A (2*q+8) (chirpLine s C)
    let rhs := cstream A (2*q+8) ((List.range B).flatMap
      (cellSourceRows L (haloGroupOrigin s t band a b L) (fun _ => C)))
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ (48*s*(2*q+8)+27)+(rawNaturalGatherCost q s+2*(a+b)+5) ∧
      Exec body cachedProtectedControlledHaloGroupInput (mk v S) n (mk v' S') ∧
      embStk groupReg (embStk cachedGroupLegacyReg S') = batchInputBank P N q l s t u band L B
        (fun n => (haloGroupOrigin s t band a b L n).val) rhs (raw++borrowed) outTail inp out ∧
      (∀ k : Fin 148, 117 ≤ k.val → S'.L k = S.L k) ∧
      (∀ k : Fin 148, 117 ≤ k.val → k ≠ 140 → S'.R k = S.R k) ∧
      S'.R 140 = gatherControls A (haloScatterGaps s t band a b L (2*q+8))++S.R 140 := by
  dsimp only
  obtain ⟨vi,E,n,hu,hn,he,hbank',hleft,hframe,hcontrol⟩ := protectedControlledHaloGroupInput_exec
    (body := fun p : Empty => nomatch p) P N q l s t u band a b L hst hgroup C
    (embDn cachedGroupLegacyReg v) (embStk cachedGroupLegacyReg S) borrowed outTail inp out
    hbank h128 h130 (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl
      all_goals exact hfresh _ (by simp [cachedGroupLegacyReg]))
  obtain ⟨v',T,he',hv',hu',hproj,hoff⟩ := exec_emb (body' := body) (ι := Empty.elim)
    cachedGroupLegacyReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',T,n,hu'.trans hu,hn,he',?_,?_,?_,?_⟩
  · rw [hproj]
    exact hbank'
  · intro k hk
    by_cases hsmall : k.val < 144
    · let j : Fin 144 := ⟨k.val,hsmall⟩
      have heq : cachedGroupLegacyReg j = k := Fin.ext rfl
      have h := congrArg (fun S : Stacks 144 A => S.L j) hproj
      have h' := h.trans (hleft j hk)
      simpa only [embStk_L,heq] using h'
    · exact (hoff k (cachedGroupLegacyReg_off k (by omega))).1
  · intro k hk hk140
    by_cases hsmall : k.val < 144
    · let j : Fin 144 := ⟨k.val,hsmall⟩
      have heq : cachedGroupLegacyReg j = k := Fin.ext rfl
      have h := congrArg (fun S : Stacks 144 A => S.R j) hproj
      have h' := h.trans (hframe j hk (by
        intro he; apply hk140; exact Fin.ext (congrArg (fun i : Fin 144 => i.val) he)))
      simpa only [embStk_R,heq] using h'
    · exact (hoff k (cachedGroupLegacyReg_off k (by omega))).2
  · have h := congrArg (fun S : Stacks 144 A => S.R 140) hproj
    exact h.trans hcontrol

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
