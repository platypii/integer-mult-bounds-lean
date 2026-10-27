module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryOriginAdvances
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellControlledBoundaryPublish

/-! Generate publication advances once and retain them across repeated scatters, outside the factor bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

def sharedPagePublicationReg (i : Fin 224) : Fin 240 :=
  ⟨if i.val = 109 then 238 else if i.val = 204 then 237 else if i.val = 206 then 239 else i.val,
    by split_ifs <;> omega⟩

theorem sharedPagePublicationReg_injective : Function.Injective sharedPagePublicationReg := by
  intro i j h
  have hh := congrArg (fun k : Fin 240 => k.val) h
  apply Fin.ext
  dsimp only [sharedPagePublicationReg] at hh
  split_ifs at hh <;> omega

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def sharedPagePublicationControls : Pr P 240 Q A U :=
  embProg sharedPagePublicationReg Empty.elim (generateBoundaryAdvances (P := Empty))

def sharedPageControlledScatter : Pr P 240 Q A U :=
  embProg sharedPagePublicationReg Empty.elim (controlledBoundaryPublish (P := Empty))

theorem sharedPagePublicationControls_exec (hA : 4 ≤ A) (s : ℕ) [NeZero s]
    (B : Finset (ZMod s)) (V w : ℕ) (hsV : s ≤ 2^V)
    (coordinateTail : List (Fin (A+4))) (v : HS 240 Q A U) (S : Stacks 240 A)
    (hc : S.R 116 = List.replicate B.card tick) (hV : (S.R 115).length = V)
    (hw : (S.R 160).length = w)
    (hcoords : S.R 238 = cstream A V ((bOrder s B).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))++coordinateTail)
    (hclean : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9] : List (Fin 240)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generateBoundaryAdvancesCost B.card V w s ∧
      Exec body sharedPagePublicationControls (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 238 coordinateTail) 239
          (gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])++S.R 239))}) := by
  let T := embStk sharedPagePublicationReg S
  have hz : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9] : List (Fin 224)), T.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hclean _ (by simp [sharedPagePublicationReg])
  obtain ⟨v₁,n,hu₁,hn,he⟩ := boundaryOriginAdvances_exec (body := fun p : Empty => nomatch p)
    hA s B V w hsV coordinateTail (embDn sharedPagePublicationReg v) T hc hV hw hcoords hz
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    sharedPagePublicationReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let T₀ : Stacks 224 A := {T with R := Function.update T.R 109 coordinateTail}
  change embOvr sharedPagePublicationReg ({T₀ with R := (Function.update T₀.R 206
    (gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])++T.R 206))} : Stacks 224 A).get S = _
  rw [embOvr_updR sharedPagePublicationReg_injective]
  dsimp only [T₀]
  rw [embOvr_updR sharedPagePublicationReg_injective,embOvr_stk]
  rfl

theorem sharedPageControlledScatter_exec (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (w : ℕ) (hw : 1 ≤ w)
    (G : ZMod s → GaussianInt) (hoff : ∀ i ∉ B, G i = 0)
    (sourceTail borrowed : List (Fin (A+4))) (v : HS 240 Q A U) (S : Stacks 240 A)
    (hs : (S.R 121).length = s) (hwidth : (S.R 160).length = w)
    (hc : S.R 116 = List.replicate B.card tick)
    (hadv : S.R 239 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])++borrowed)
    (hsrc : S.R 237 = cstream A w ((bOrder s B).map G)++sourceTail)
    (hclean : ∀ i ∈ ([184,217,223,201,208,211,215,220] : List (Fin 240)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 89*s*w+41 ∧
      Exec body sharedPageControlledScatter (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 237 sourceTail) 132
          (cstream A w (chirpLine s G)++S.R 132))}) := by
  let T := embStk sharedPagePublicationReg S
  have hz : ∀ i ∈ ([184,217,223,201,208,211,215,220] : List (Fin 224)), T.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hclean _ (by simp [sharedPagePublicationReg])
  obtain ⟨v₁,n,hu₁,hn,he⟩ := controlledBoundaryPublish_exec (body := fun p : Empty => nomatch p)
    s B w hw G hoff sourceTail borrowed (embDn sharedPagePublicationReg v) T hs hwidth hc hadv hsrc hz
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    sharedPagePublicationReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let T₀ : Stacks 224 A := {T with R := Function.update T.R 204 sourceTail}
  change embOvr sharedPagePublicationReg ({T₀ with R := (Function.update T₀.R 132
    (cstream A w (chirpLine s G)++T.R 132))} : Stacks 224 A).get S = _
  rw [embOvr_updR sharedPagePublicationReg_injective]
  dsimp only [T₀]
  rw [embOvr_updR sharedPagePublicationReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
