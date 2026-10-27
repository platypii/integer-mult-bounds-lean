module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateDeepCouplingMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingPacket

/-! Prepare one owned row-guard symbol per ambient coordinate, above a borrowed suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def couplingSkipAt (boundary : Bool) (s t band a b i : ℕ) : Bool :=
  boundary && haloMaskAt false s t (2*band) a b i

def couplingGuardSymbols (boundary : Bool) (A s t band a b : ℕ) : List (Fin (A+4)) :=
  (List.range s).map (fun i => pairSym A (couplingSkipAt boundary s t band a b i) (couplingSkipAt boundary s t band a b i))

@[simp] theorem couplingGuardSymbols_length (boundary : Bool) (A s t band a b : ℕ) :
    (couplingGuardSymbols boundary A s t band a b).length = s := by simp [couplingGuardSymbols]

theorem couplingSkipAt_sound {s t : ℕ} [NeZero s] (hst : s < t) (boundary : Bool)
    (band a b i : ℕ) (hb : b ≤ s) (hi : i < s) (h : couplingSkipAt boundary s t band a b i = true) :
    boundary = true ∧ (i : ZMod s) ∈ haloInterior s t (2*band) a b := by
  have hh : boundary = true ∧ haloMaskAt false s t (2*band) a b i = true := by
    simpa only [couplingSkipAt,Bool.and_eq_true] using h
  obtain ⟨hboundary,hmask⟩ := hh
  exact ⟨hboundary,(haloMaskAt_spec false hst (2*band) a b i hb hi).mp hmask⟩

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def prepareCouplingGuard (boundary : Bool) : Pr P₀ 144 Q A U :=
  if boundary then embProg (couplingViewReg 109 136) Empty.elim (generateDeepCouplingMask (P₀ := Empty))
  else umulSym 1 (pairSym A false false) 97 136 104

def prepareCouplingGuardCost (s t band a b : ℕ) : ℕ :=
  generateDeepCouplingMaskCost s t band a b+4*s+4

theorem prepareCouplingGuard_exec {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hst : s < t) (ha : a ≤ s) (hb : b ≤ s)
    (raw : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCouplingGuardCost s t band a b ∧
      Exec body (prepareCouplingGuard boundary) (mk v S) m
        (mk v' {S with R := (Function.update S.R 136
          (couplingGuardSymbols boundary A s t band a b++S.R 136))}) := by
  have hs : (S.R 97).length = s := hready.axis
  cases boundary with
  | false =>
    obtain ⟨v',hu,he⟩ := umulSym_exec (body := body) 1 (pairSym A false false)
      (a := 97) (b := 136) (t := 104) (by decide) (by decide) (by decide) v S (hready.fresh 104 (by simp))
    refine ⟨v',4*s+4,hu,by dsimp [prepareCouplingGuardCost]; omega,?_⟩
    simpa [prepareCouplingGuard,couplingGuardSymbols,couplingSkipAt,hs,List.map_const'] using he
  | true =>
    let e := couplingViewReg 109 136
    obtain ⟨v₁,m,hu₁,hm,he₁⟩ := generateDeepCouplingMask_exec
      (body := fun p : Empty => nomatch p) hst ha hb (embDn e v) (embStk e S)
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
