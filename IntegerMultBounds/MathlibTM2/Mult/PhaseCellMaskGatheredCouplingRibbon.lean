module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskCouplingSource
public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRibbonMask

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Layer

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def ribbonMaskReg (i : Fin 144) : Fin 168 :=
  if i = 97 then 166 else if i = 107 then 167 else if i = 109 then 158 else
  if i = 110 then 160 else ⟨i.val,by omega⟩

theorem ribbonMaskReg_injective : Function.Injective ribbonMaskReg := by
  intro i j he
  have hv := congrArg (fun k : Fin 168 => k.val) he
  unfold ribbonMaskReg at hv
  split_ifs at hv <;> simp_all only
  all_goals omega

def maskGatheredCouplingRibbon : Pr P 168 Q A U :=
  embProg ribbonMaskReg Empty.elim (maskCouplingSource (P := Empty))

theorem maskGatheredCouplingRibbon_exec (hA : 4 ≤ A) (flags : List Bool) (xs : List GaussianInt)
    (w : ℕ) (hlen : xs.length = flags.length) (tail : List (Fin (A+4)))
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hs : (S.R 166).length = flags.length) (hw : (S.R 94).length = w)
    (hsrc : S.R 160 = cstream A w xs++tail)
    (hmask : S.R 158 = flags.map (fun flag => pairSym A flag flag))
    (h108 : S.R 108 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = [])
    (h135 : S.R 135 = []) (h107 : S.R 167 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ maskCouplingSourceCost flags.length w ∧
      Exec body maskGatheredCouplingRibbon (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 158 [])
          141 (cstream A w (maskedLine flags xs)++S.R 141))}) := by
  obtain ⟨v₁,m,hu₁,hm,he⟩ := maskCouplingSource_exec
    (body := fun p : Empty => nomatch p) hA flags xs w hlen tail
    (embDn ribbonMaskReg v) (embStk ribbonMaskReg S) hs hw hsrc hmask
    h108 h104 h105 h135 h107 h143
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    ribbonMaskReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let T := embStk ribbonMaskReg S
  let T₁ : Stacks 144 A := {T with R := Function.update T.R 109 []}
  change embOvr ribbonMaskReg
    ({T₁ with R := (Function.update T₁.R 141 (cstream A w (maskedLine flags xs)++T.R 141))} : Stacks 144 A).get S = _
  rw [embOvr_updR ribbonMaskReg_injective T₁ S 141,
    embOvr_updR ribbonMaskReg_injective T S 109,embOvr_stk]
  rfl

theorem maskGatheredCouplingRibbon_interval_exec {s : ℕ} [NeZero s] (hA : 4 ≤ A) (boundary : Bool)
    (t band a b origin N : ℕ) (C : ZMod s → GaussianInt)
    (flags : List Bool) (hflags : flags = couplingRibbonFlags (s := s) boundary t band a b origin N)
    (w : ℕ) (hlen : (rawCouplingRibbon band origin N C).length = flags.length) (tail : List (Fin (A+4)))
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hs : (S.R 166).length = flags.length) (hw : (S.R 94).length = w)
    (hsrc : S.R 160 = cstream A w (rawCouplingRibbon band origin N C)++tail)
    (hmask : S.R 158 = flags.map (fun flag => pairSym A flag flag))
    (h108 : S.R 108 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = [])
    (h135 : S.R 135 = []) (h107 : S.R 167 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ maskCouplingSourceCost flags.length w ∧
      Exec body maskGatheredCouplingRibbon (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 158 [])
          141 (cstream A w (couplingSourceInterval boundary t band a b origin N C)++S.R 141))}) := by
  have he := maskGatheredCouplingRibbon_exec (body := body) hA flags
    (rawCouplingRibbon band origin N C) w hlen tail v S hs hw hsrc hmask
    h108 h104 h105 h135 h107 h143
  simpa only [hflags,maskedLine_couplingRibbon] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
