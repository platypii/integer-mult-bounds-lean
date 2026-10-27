module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCouplingWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareSpatialCouplingOperands

/-! Generate spatial operands with the source retained outside arithmetic scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 118 Q A U}

def spatialCouplingOperands : Pr P₀ 118 Q A U :=
  embProg cachedCouplingLookupReg Empty.elim (prepareSpatialCouplingOperands (P₀ := Empty))

theorem spatialCouplingOperands_exec {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) 
    (hst : s < t) (hi : i < s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 118 Q A U) (S : Stacks 118 A)
    (hPsrc : ((embStk cachedCouplingLookupReg S).R 114).length = P) (hqsrc : ((embStk cachedCouplingLookupReg S).R 112).length = q) (husrc : ((embStk cachedCouplingLookupReg S).R 99).length = u)
    (hsSrc : ((embStk cachedCouplingLookupReg S).R 97).length = s) (htSrc : ((embStk cachedCouplingLookupReg S).R 98).length = t)
    (hbandSrc : ((embStk cachedCouplingLookupReg S).R 100).length = band) (hiSrc : ((embStk cachedCouplingLookupReg S).R 107).length = i) (h105 : (embStk cachedCouplingLookupReg S).R 105 = [])
    (hwsrc : ((embStk cachedCouplingLookupReg S).R 94).length = w) (h115 : (embStk cachedCouplingLookupReg S).R 115 = []) (h104 : (embStk cachedCouplingLookupReg S).R 104 = [])
    (h109 : (embStk cachedCouplingLookupReg S).R 109 = []) (h106 : (embStk cachedCouplingLookupReg S).R 106 = []) (h108 : (embStk cachedCouplingLookupReg S).R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → (embStk cachedCouplingLookupReg S).R r = [])
    (hsrc : (embStk cachedCouplingLookupReg S).R 92 = cstream A w ((PhaseCellMatrix.cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band).drop i)++tail) (h116 : (embStk cachedCouplingLookupReg S).R 116 = []) (h102 : (embStk cachedCouplingLookupReg S).R 102 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareSpatialCouplingOperandsCost P q w s t u band i ∧
      Exec body spatialCouplingOperands (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          111 (cstream A w (spatialCouplingCoefficientWords P q s t u band i)++S.R 111))
          102 (List.replicate (2*band+1) tick))
          110 (cstream A w (spatialCouplingInputWords boundary t band a b i C)++S.R 110))}) := by
  obtain ⟨v₁,m,hu₁,hm,he⟩ := prepareSpatialCouplingOperands_exec
    (body := fun p : Empty => nomatch p) boundary hst hi hP C tail
    (embDn cachedCouplingLookupReg v) (embStk cachedCouplingLookupReg S)
    hPsrc hqsrc husrc hsSrc htSrc hbandSrc hiSrc h105 hwsrc h115 h104
    h109 h106 h108 hblank hsrc h116 h102
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    cachedCouplingLookupReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let T := embStk cachedCouplingLookupReg S
  let T₁ : Stacks 117 A := {T with R := (Function.update T.R 111
    (cstream A w (spatialCouplingCoefficientWords P q s t u band i)++T.R 111))}
  let T₂ : Stacks 117 A := {T₁ with R := Function.update T₁.R 102 (List.replicate (2*band+1) tick)}
  change embOvr cachedCouplingLookupReg
    ({T₂ with R := (Function.update T₂.R 110
      (cstream A w (spatialCouplingInputWords boundary t band a b i C)++T.R 110))} : Stacks 117 A).get S = _
  rw [embOvr_updR cachedCouplingLookupReg_injective T₂ S 110,
    embOvr_updR cachedCouplingLookupReg_injective T₁ S 102,
    embOvr_updR cachedCouplingLookupReg_injective T S 111,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
