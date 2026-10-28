module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateRecoveryCouplingMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingPacket

/-! Prepare one owned row-guard symbol per ambient coordinate, above a borrowed suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def couplingSkipAt (boundary : Bool) (s t band a b i : ℕ) : Bool :=
  recoveryGuardMaskAt true s t (2*band) a b i

def couplingGuardSymbols (boundary : Bool) (A s t band a b : ℕ) : List (Fin (A+4)) :=
  (List.range s).map (fun i => pairSym A (couplingSkipAt boundary s t band a b i) (couplingSkipAt boundary s t band a b i))

@[simp] theorem couplingGuardSymbols_length (boundary : Bool) (A s t band a b : ℕ) :
    (couplingGuardSymbols boundary A s t band a b).length = s := by simp [couplingGuardSymbols]

theorem couplingSkipAt_sound {s t : ℕ} [NeZero s] (hst : s < t) (boundary : Bool)
    (band a b i : ℕ) (hb : b ≤ s) (hi : i < s) (h : couplingSkipAt boundary s t band a b i = true) :
    (i : ZMod s) ∈ couplingZeroRows true s t band a b := by
  exact (recoveryGuardMaskAt_spec hst true band a b i hb hi).mp h

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def prepareCouplingGuard (boundary : Bool) : Pr P₀ 144 Q A U :=
  embProg (couplingViewReg 109 136) Empty.elim (generateRecoveryCouplingMask (P₀ := Empty) true)

def prepareCouplingGuardCost (s t band a b : ℕ) : ℕ :=
  generateRecoveryCouplingMaskCost s t band a b

theorem prepareCouplingGuard_exec {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hA : 4 ≤ A)
    (raw : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCouplingGuardCost s t band a b ∧
      Exec body (prepareCouplingGuard boundary) (mk v S) m
        (mk v' {S with R := (Function.update S.R 136
          (couplingGuardSymbols boundary A s t band a b++S.R 136))}) := by
  let e := couplingViewReg 109 136
  obtain ⟨v₁,m,hu₁,hm,he₁⟩ := generateRecoveryCouplingMask_exec
    (body := fun p : Empty => nomatch p) true hst ha hb hA (embDn e v) (embStk e S)
    hready.axis hready.period hready.bandwidth hready.lower hready.upper
    (hready.fresh 96 (by simp)) (hready.fresh 104 (by simp))
    (hready.fresh 115 (by simp)) (hready.fresh 106 (by simp)) (hready.fresh 108 (by simp))
    (by intro r hr; have hn : r ≠ 109 := by intro h; subst r; norm_num at hr
        simpa [e,couplingViewReg,embStk,hn] using hready.low r (by omega))
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    (couplingViewReg_injective 109 136 (by decide)) (fun p => nomatch p) he₁ v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,by dsimp [prepareCouplingGuardCost]; omega,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [embOvr_updR (couplingViewReg_injective 109 136 (by decide)),embOvr_stk]
  rfl


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
