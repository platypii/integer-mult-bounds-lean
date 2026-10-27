module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFamilyInteriorForCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedBoundaryRhs

/-! Gather the computed residual into the existing boundary factor bank while
retaining the interior family in its disjoint ports. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

theorem familyCouplingSource_high_update {A : ℕ} (S : Stacks 263 A) (k : Fin 263) (hk : 154 ≤ k.val)
    (words : List (Fin (A+4))) :
    embStk familyCouplingSourceReg {S with R := Function.update S.R k words} = embStk familyCouplingSourceReg S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  have hne : familyCouplingSourceReg i ≠ k := by
    intro h
    have hi := couplingSourceReg_lt i
    have hv := congrArg Fin.val h
    dsimp [familyCouplingSourceReg,familyInverseLegacyReg] at hv
    omega
  simp [embStk,Function.comp_def,hne]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 263 Q A U}

def familyBoundaryRhs : Pr P 263 Q A U :=
  embProg familyInverseLegacyReg Empty.elim (placedBoundaryRhs (P := Empty))

theorem familyBoundaryRhs_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (V w : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^V) (C D : ZMod s → GaussianInt) (hCD : ∀ i ∈ B, C i = D i)
    (coordinateTail rhsTail : List (Fin (A+4))) (v : HS 263 Q A U) (S : Stacks 263 A)
    (hN : (S.R 116).length = B.card) (hV : (S.R 115).length = V) (hw : (S.R 160).length = w)
    (hcoordinates : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++coordinateTail)
    (hrhs : S.R 110 = cstream A w (chirpLine s C)++rhsTail)
    (h0 : S.R 0 = []) (h106 : S.R 106 = []) (h139 : S.R 139 = [])
    (hblank : ∀ r : Fin 263, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ boundaryRhsPrepareCost V w B.card s ∧
      Exec body familyBoundaryRhs (mk v S) n
        (mk v' {S with R := (Function.update S.R 206
          (cstream A w ((List.range B.card).map (fun j => D (bFoldAt s B j)))++S.R 206))}) := by
  obtain ⟨vi,n,hu,hn,he⟩ := placedBoundaryRhs_exec (body := fun p : Empty => nomatch p)
    B V w hA hs C D hCD coordinateTail rhsTail (embDn familyInverseLegacyReg v) (embStk familyInverseLegacyReg S)
    hN hV hw hcoordinates hrhs h0 h106 h139 (by
      intro r hr1 hr7
      exact hblank (familyInverseLegacyReg r) hr1 hr7)
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    familyInverseLegacyReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',n,hu'.trans hu,hn,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  rw [embOvr_updR familyInverseLegacyReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
