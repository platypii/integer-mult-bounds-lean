module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRhsPhysical

/-! Gather the computed ambient residual into the retained factor bank's RHS port without changing any page or coordinate tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def sharedPageBoundaryRhs : Pr P 240 Q A U :=
  embProg sharedPageRecoveryReg Empty.elim (boundaryRhsPhysical (P := Empty))

theorem sharedPageBoundaryRhs_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (V w : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^V) (C : ZMod s → GaussianInt)
    (coordinateTail rhsTail : List (Fin (A+4))) (v : HS 240 Q A U) (S : Stacks 240 A)
    (hN : (S.R 116).length = B.card) (hV : (S.R 115).length = V) (hw : (S.R 160).length = w)
    (hcoordinates : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++coordinateTail)
    (hrhs : S.R 110 = cstream A w (chirpLine s C)++rhsTail)
    (h0 : S.R 0 = []) (h106 : S.R 106 = []) (h139 : S.R 139 = [])
    (hblank : ∀ r : Fin 240, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ boundaryRhsPrepareCost V w B.card s ∧
      Exec body sharedPageBoundaryRhs (mk v S) n
        (mk v' {S with R := (Function.update S.R 206
          (cstream A w ((List.range B.card).map (fun j => C (bFoldAt s B j)))++S.R 206))}) := by
  let T := embStk sharedPageRecoveryReg S
  have hz : ∀ r : Fin 224, 1 ≤ r.val → r.val < 7 → T.R r = [] := by
    intro r hr1 hr7
    exact hblank (sharedPageRecoveryReg r) hr1 hr7
  obtain ⟨v₁,n,hu₁,hn,he⟩ := boundaryRhsPhysical_exec (body := fun p : Empty => nomatch p)
    B V w hA hs C coordinateTail rhsTail (embDn sharedPageRecoveryReg v) T
    hN hV hw hcoordinates hrhs h0 h106 h139 hz
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    sharedPageRecoveryReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [embOvr_updR sharedPageRecoveryReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
