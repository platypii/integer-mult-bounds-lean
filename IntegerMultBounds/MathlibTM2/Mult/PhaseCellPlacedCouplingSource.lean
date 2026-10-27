module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingCacheRead
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareSpatialCouplingSource
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireSpatialCouplingSource

/-! Source preparation uses the ordinary scratch placement, outside both retained keys. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def couplingSourceReg (i : Fin 144) : Fin 256 := couplingCacheLegacyReg (couplingLegacyReg i)

theorem couplingSourceReg_injective : Function.Injective couplingSourceReg :=
  couplingCacheLegacyReg_injective.comp couplingLegacyReg_injective

theorem couplingSource_view {A : ℕ} (S : Stacks 256 A) :
    embStk couplingSourceReg S = embStk couplingLegacyReg (embStk couplingCacheLegacyReg S) := rfl

theorem couplingSource_update {A : ℕ} (S : Stacks 256 A) (words : List (Fin (A+4))) :
    embOvr couplingSourceReg
      ({embStk couplingSourceReg S with R := Function.update (embStk couplingSourceReg S).R 141 words} : Stacks 144 A).get S =
      {S with R := Function.update S.R 141 words} := by
  rw [embOvr_updR couplingSourceReg_injective,embOvr_stk]
  rfl

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 256 Q A U}

def placedCouplingSourcePrepare (boundary : Bool) : Pr P₀ 256 Q A U :=
  embProg couplingSourceReg Empty.elim (prepareSpatialCouplingSource (P₀ := Empty) boundary)

def placedCouplingSourceRetire : Pr P₀ 256 Q A U :=
  embProg couplingSourceReg Empty.elim (retireSpatialCouplingSource (P := Empty))

theorem placedCouplingSourcePrepare_exec {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 4 ≤ A) (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : band ≤ s)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (v : HS 256 Q A U) (S : Stacks 256 A)
    (hready : CouplingReady P q w s t u band a b (cstream A w (chirpLine s C)++tail)
      (embStk groupReg (embStk couplingSourceReg S)))
    (h107 : (embStk couplingSourceReg S).R 107 = [])
    (h135 : (embStk couplingSourceReg S).R 135 = [])
    (h143 : (embStk couplingSourceReg S).R 143 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareSpatialCouplingSourceCost s t band a b w ∧
      Exec body (placedCouplingSourcePrepare boundary) (mk v S) m
        (mk v' {S with R := Function.update S.R 141 (cstream A w (cyclicPaddedLine (fun j =>
          if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
          then C j else 0) band)++S.R 141)}) := by
  obtain ⟨vi,m,hu,hm,he⟩ := prepareSpatialCouplingSource_exec (body := fun p : Empty => nomatch p)
    boundary hA hst ha hb hband C tail (embDn couplingSourceReg v) (embStk couplingSourceReg S)
    hready h107 h135 h143
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingSourceReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  exact couplingSource_update S _

theorem placedCouplingSourceRetire_exec (s band w : ℕ)
    (words tail : List (Fin (A+4))) (hlen : words.length = (s+2*band)*w)
    (v : HS 256 Q A U) (S : Stacks 256 A)
    (hs : ((embStk couplingSourceReg S).R 97).length = s)
    (hb : ((embStk couplingSourceReg S).R 100).length = band)
    (hw : ((embStk couplingSourceReg S).R 94).length = w)
    (hsrc : S.R 141 = words++tail)
    (h116 : (embStk couplingSourceReg S).R 116 = [])
    (h108 : (embStk couplingSourceReg S).R 108 = [])
    (h104 : (embStk couplingSourceReg S).R 104 = [])
    (h105 : (embStk couplingSourceReg S).R 105 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retireSpatialCouplingSourceCost s band w ∧
      Exec body placedCouplingSourceRetire (mk v S) m
        (mk v' {S with R := Function.update S.R 141 tail}) := by
  obtain ⟨vi,m,hu,hm,he⟩ := retireSpatialCouplingSource_exec (body := fun p : Empty => nomatch p)
    s band w words tail hlen (embDn couplingSourceReg v) (embStk couplingSourceReg S)
    hs hb hw hsrc h116 h108 h104 h105
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingSourceReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  exact couplingSource_update S _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
