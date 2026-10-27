module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingSource

/-! Gather the computed ambient residual into the retained factor bank's RHS port without changing any page or coordinate tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

def couplingBoundaryReg (i : Fin 240) : Fin 256 :=
  couplingCacheLegacyReg (sharedComplexBatchCoreReg i)

theorem couplingBoundaryReg_injective : Function.Injective couplingBoundaryReg :=
  couplingCacheLegacyReg_injective.comp sharedComplexBatchCoreReg_injective

theorem couplingSourceReg_lt (i : Fin 144) : (couplingSourceReg i).val < 154 := by
  have hi := i.isLt
  simp only [couplingSourceReg,couplingCacheLegacyReg,couplingLegacyReg,sharedComplexBatchCoreReg,
    sharedPageRecoveryReg,boundaryFactorLegacyReg,tableReg,boundaryArithmeticReg,componentReg]
  split_ifs <;> omega

theorem couplingSource_high_update {A : ℕ} (S : Stacks 256 A) (k : Fin 256) (hk : 154 ≤ k.val)
    (words : List (Fin (A+4))) :
    embStk couplingSourceReg {S with R := Function.update S.R k words} = embStk couplingSourceReg S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  have hne : couplingSourceReg i ≠ k := by
    intro h
    have hi := couplingSourceReg_lt i
    have hv := congrArg Fin.val h
    omega
  simp [embStk,Function.comp_def,hne]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 256 Q A U}

def placedBoundaryRhs : Pr P 256 Q A U :=
  embProg couplingBoundaryReg Empty.elim (sharedPageBoundaryRhs (P := Empty))

theorem placedBoundaryRhs_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (V w : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^V) (C D : ZMod s → GaussianInt) (hCD : ∀ i ∈ B, C i = D i)
    (coordinateTail rhsTail : List (Fin (A+4))) (v : HS 256 Q A U) (S : Stacks 256 A)
    (hN : (S.R 116).length = B.card) (hV : (S.R 115).length = V) (hw : (S.R 160).length = w)
    (hcoordinates : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++coordinateTail)
    (hrhs : S.R 110 = cstream A w (chirpLine s C)++rhsTail)
    (h0 : S.R 0 = []) (h106 : S.R 106 = []) (h139 : S.R 139 = [])
    (hblank : ∀ r : Fin 256, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ boundaryRhsPrepareCost V w B.card s ∧
      Exec body placedBoundaryRhs (mk v S) n
        (mk v' {S with R := (Function.update S.R 206
          (cstream A w ((List.range B.card).map (fun j => D (bFoldAt s B j)))++S.R 206))}) := by
  have hz : ∀ r : Fin 240, 1 ≤ r.val → r.val < 7 → (embStk couplingBoundaryReg S).R r = [] := by
    intro r hr1 hr7
    exact hblank (couplingBoundaryReg r) hr1 hr7
  obtain ⟨vi,n,hu,hn,he⟩ := sharedPageBoundaryRhs_exec (body := fun p : Empty => nomatch p)
    B V w hA hs C D hCD coordinateTail rhsTail (embDn couplingBoundaryReg v) (embStk couplingBoundaryReg S)
    hN hV hw hcoordinates hrhs h0 h106 h139 hz
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingBoundaryReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',n,hu'.trans hu,hn,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  rw [embOvr_updR couplingBoundaryReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
