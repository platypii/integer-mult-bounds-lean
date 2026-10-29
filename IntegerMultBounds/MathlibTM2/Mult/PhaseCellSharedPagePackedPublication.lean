module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPagePublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellControlledPackedBoundaryPublish

/-! Generate publication advances once and retain them across repeated scatters, outside the factor bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def sharedPageControlledPackedScatter : Pr P 240 Q A U :=
  embProg sharedPagePublicationReg Empty.elim (controlledPackedBoundaryPublish (P := Empty))

theorem sharedPageControlledPackedScatter_exec (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (a L w : ℕ) (hw : 1 ≤ w)
    (hfit : a+L ≤ s) (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L)
    (G : ZMod s → GaussianInt) (hoff : ∀ i ∉ B, G i = 0)
    (sourceTail borrowed : List (Fin (A+4))) (v : HS 240 Q A U) (S : Stacks 240 A)
    (hs : (S.R 222).length = L) (hwidth : (S.R 160).length = w)
    (hc : S.R 116 = List.replicate B.card tick)
    (hadv : S.R 239 = gatherControls A (originAdvances w 0 (packedBoundaryOrigins B a)++[0])++borrowed)
    (hsrc : S.R 237 = cstream A w ((bOrder s B).map G)++sourceTail)
    (hclean : ∀ i ∈ ([184,217,223,201,208,211,215,220] : List (Fin 240)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 89*L*w+41 ∧
      Exec body sharedPageControlledPackedScatter (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 237 sourceTail) 132
          (cstream A w (packedInterval a L G)++S.R 132))}) := by
  let T := embStk sharedPagePublicationReg S
  have hz : ∀ i ∈ ([184,217,223,201,208,211,215,220] : List (Fin 224)), T.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hclean _ (by simp [sharedPagePublicationReg])
  obtain ⟨v₁,n,hu₁,hn,he⟩ := controlledPackedBoundaryPublish_exec (body := fun p : Empty => nomatch p)
    s B a L w hw hfit hB G hoff sourceTail borrowed (embDn sharedPagePublicationReg v) T hs hwidth hc hadv hsrc hz
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    sharedPagePublicationReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let T₀ : Stacks 224 A := {T with R := Function.update T.R 204 sourceTail}
  change embOvr sharedPagePublicationReg ({T₀ with R := (Function.update T₀.R 132
    (cstream A w (packedInterval a L G)++T.R 132))} : Stacks 224 A).get S = _
  rw [embOvr_updR sharedPagePublicationReg_injective]
  dsimp only [T₀]
  rw [embOvr_updR sharedPagePublicationReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
