module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingRow
public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedCouplingRow

/-! Lift spatial row arithmetic while isolating its retained source from ordinary headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def spatialCouplingReg (i : Fin 117) : Fin 144 :=
  ⟨if i.val = 92 then 141 else i.val,by split <;> omega⟩

theorem spatialCouplingReg_injective : Function.Injective spatialCouplingReg := by
  intro i j he
  have hv := congrArg (fun k : Fin 144 => k.val) he
  simp only [spatialCouplingReg] at hv
  have hi := i.isLt
  have hj := j.isLt
  split at hv <;> split at hv <;> apply Fin.ext <;> omega

noncomputable def outerSpatialCouplingRow (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  embProg spatialCouplingReg Empty.elim (spatialCouplingRow (P₀ := Empty) hQ)

theorem outerSpatialCouplingRow_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hPsrc : ((embStk spatialCouplingReg S).R 114).length = P) (hqsrc : ((embStk spatialCouplingReg S).R 112).length = q) (husrc : ((embStk spatialCouplingReg S).R 99).length = u)
    (hsSrc : ((embStk spatialCouplingReg S).R 97).length = s) (htSrc : ((embStk spatialCouplingReg S).R 98).length = t)
    (hbandSrc : ((embStk spatialCouplingReg S).R 100).length = band) (hiSrc : ((embStk spatialCouplingReg S).R 107).length = i) (h105 : (embStk spatialCouplingReg S).R 105 = [])
    (hwsrc : ((embStk spatialCouplingReg S).R 94).length = w) (h115 : (embStk spatialCouplingReg S).R 115 = []) (h104 : (embStk spatialCouplingReg S).R 104 = [])
    (h109 : (embStk spatialCouplingReg S).R 109 = []) (h106 : (embStk spatialCouplingReg S).R 106 = []) (h108 : (embStk spatialCouplingReg S).R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → (embStk spatialCouplingReg S).R r = [])
    (hsrc : (embStk spatialCouplingReg S).R 92 = cstream A w ((cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band).drop i)++tail) (h116 : (embStk spatialCouplingReg S).R 116 = []) (h102 : (embStk spatialCouplingReg S).R 102 = [])
    (rhs : GaussianInt) (rhsTail : List (Fin (A+4)))
    (hrhs : (embStk spatialCouplingReg S).R 93 = csyms A w rhs++rhsTail) (hc : CClean mul (embStk spatialCouplingReg S))
    (hcr : ∀ r : CR, (embStk spatialCouplingReg S).R (cr r) = [])
    (hleft : ∀ k ∈ [(97 : Fin 117),98,99,100], (embStk spatialCouplingReg S).L k = []) (h96 : (embStk spatialCouplingReg S).R 96 = [])
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band i, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ spatialCouplingRowCost P q w s t u band i ∧
      Exec body (outerSpatialCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update S.R 113
          (csyms A w (rhs-(List.zipWith (fun x z => tdivN q (x*z))
            (couplingInputWords boundary t band a b i C)
            (couplingCoefficientWords P q s t u band i)).sum)++S.R 113))}) := by
  obtain ⟨v₁,m,hu₁,hm,he₁⟩ := spatialCouplingRow_exec
    (body := fun p : Empty => nomatch p) hQ boundary hA hw5 hqw hst hi hP C tail
    (embDn spatialCouplingReg v) (embStk spatialCouplingReg S)
    hPsrc hqsrc husrc hsSrc htSrc hbandSrc hiSrc h105 hwsrc h115 h104 h109 h106 h108
    hblank hsrc h116 h102 rhs rhsTail hrhs hc hcr hleft h96 hxs has
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    spatialCouplingReg_injective (fun p => nomatch p) he₁ v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [embOvr_updR spatialCouplingReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
