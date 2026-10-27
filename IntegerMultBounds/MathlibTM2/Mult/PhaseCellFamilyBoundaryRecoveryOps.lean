module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyBoundaryResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageBoundaryAmbient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageRetireResidual

/-! Scatter a borrowed boundary solution and retire the owned residual outside both retained cache banks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 263 Q A U}

def familyBoundaryAmbient : Pr P 263 Q A U :=
  embProg familyBoundaryReg Empty.elim (sharedPageBoundaryAmbient (P := Empty))

def familyBoundaryResidualRetire : Pr P 263 Q A U :=
  embProg familyBoundaryReg Empty.elim (sharedPageRetireResidual (P := Empty))

theorem familyBoundaryAmbient_exec (hA : 4 ≤ A) (s : ℕ) [NeZero s]
    (B : Finset (ZMod s)) (w : ℕ) (hw : 1 ≤ w)
    (solution : List GaussianInt) (hlen : solution.length = B.card)
    (v : HS 263 Q A U) (S : Stacks 263 A) (tail borrowed : List (Fin (A+4)))
    (hleft : ∀ i : Fin 240, (embStk familyBoundaryReg S).L i = [])
    (hmul : ∀ i : Fin 64, S.R ⟨i.val,by omega⟩ = [])
    (hc : S.R 116 = List.replicate B.card tick) (hrows : (S.R 192).length = B.card)
    (hwidth : (S.R 160).length = w) (hs : (S.R 121).length = s)
    (hadv : S.R 239 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])++borrowed)
    (hsource : S.R 224 = cstream A w solution++tail)
    (hclean : ∀ i ∈ ([184,217,223,201,208,211,215,220,231,232,233,234,235,236,237] : List (Fin 263)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ sharedPageBoundaryAmbientCost B.card w s ∧
      Exec body familyBoundaryAmbient (mk v S) n
        (mk v' {S with R := (Function.update S.R 132
          (cstream A w (chirpLine s (boundarySolutionField B solution))++S.R 132))}) ∧
      ∀ (q : ℕ) (x : ZMod s → ℝ) (ε : ℝ), (∀ z ∈ solution, Fits w z) →
        (∀ i < B.card, ‖value q (solution.getD i 0) - (x (bFoldAt s B i) : ℂ)‖ ≤ ε) →
        PhaseCellInterface.ErrorOn B
          (fun i => publishedCellRead q w (0 : ZMod s)
            (cstream A w (chirpLine s (boundarySolutionField B solution))++S.R 132) i) x ε := by
  have hz : ∀ i ∈ ([184,217,223,201,208,211,215,220,231,232,233,234,235,236,237] : List (Fin 240)),
      (embStk familyBoundaryReg S).R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hclean _ (by decide)
  obtain ⟨vi,n,hu,hn,he,hbytes⟩ := sharedPageBoundaryAmbient_exec (body := fun p : Empty => nomatch p)
    hA s B w hw solution hlen (embDn familyBoundaryReg v) (embStk familyBoundaryReg S)
    tail borrowed hleft hmul hc hrows hwidth hs hadv hsource hz
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    familyBoundaryReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',n,hu'.trans hu,hn,he'.cast rfl ?_,hbytes⟩
  apply congrArg (mk v')
  rw [embOvr_updR familyBoundaryReg_injective,embOvr_stk]
  rfl

theorem familyBoundaryResidualRetire_exec (s w : ℕ) (residual tail : List (Fin (A+4)))
    (hlen : residual.length = s*w) (v : HS 263 Q A U) (S : Stacks 263 A)
    (hs : (S.R 121).length = s) (hw : (S.R 160).length = w)
    (hsource : S.R 110 = residual++tail)
    (h231 : S.R 231 = []) (h232 : S.R 232 = []) (h233 : S.R 233 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ sharedPageRetireResidualCost s w ∧
      Exec body familyBoundaryResidualRetire (mk v S) n
        (mk v' {S with R := Function.update S.R 110 tail}) := by
  obtain ⟨vi,n,hu,hn,he⟩ := sharedPageRetireResidual_exec (body := fun p : Empty => nomatch p)
    s w residual tail hlen (embDn familyBoundaryReg v) (embStk familyBoundaryReg S)
    hs hw hsource h231 h232 h233
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    familyBoundaryReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',n,hu'.trans hu,hn,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  rw [embOvr_updR familyBoundaryReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
