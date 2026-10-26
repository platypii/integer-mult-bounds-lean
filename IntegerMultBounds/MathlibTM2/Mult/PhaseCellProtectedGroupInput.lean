module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedControlledGroupInput

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
    protectedControlledGroupInput

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
  have hbody : ∀ f, embTab groupReg body (id f) = embProg groupReg id (body f) := fun _ => rfl
  obtain ⟨vp,np,hup,hnp,hep⟩ := generateNaturalGroupInputBank_exec (body := body)
    P N q l s t u band L hP hs hst hu hgroup hband hL hLs hA C (embDn groupReg v) borrowed outTail inp out
  obtain ⟨v₁,S₁,he₁,hv₁,hu₁,hbank₁,hoff₁⟩ := exec_emb groupReg_injective hbody hep v rfl S hbank
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,he₂,hbank₂,hL₂,hR₂,hctrl₂⟩ := protectedControlledGroupInput_exec (body := body)
    P N q l s t u band L hst hgroup C v₁ S₁ borrowed outTail inp out hbank₁
    (by rw [(hoff₁ 128 (groupReg_off 128 (by decide))).2]; exact h128)
    (by rw [(hoff₁ 130 (groupReg_off 130 (by decide))).2]; exact h130) (by
      intro k hk
      have hkhi : 117 ≤ k.val := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> decide
      rw [(hoff₁ k (groupReg_off k hkhi)).2]
      exact hfresh k hk)
  refine ⟨v₂,S₂,np+n₂,hu₂.trans (hu₁.trans hup),by omega,Exec.seq he₁ he₂,hbank₂,?_,?_,?_⟩
  · intro k hk
    exact (hL₂ k hk).trans (hoff₁ k (groupReg_off k hk)).1
  · intro k hk hk140
    exact (hR₂ k hk hk140).trans (hoff₁ k (groupReg_off k hk)).2
  · simpa only [(hoff₁ 140 (groupReg_off 140 (by decide))).2] using hctrl₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
