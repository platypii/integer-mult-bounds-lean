module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedResidualControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireAmbientSource
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeInteriorOutput

/-! Initialize the output from the actual RHS and execute a standalone interior pass. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 256 Q A U}

noncomputable def placedInitializedInterior (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 256 Q A U :=
  embProg couplingSourceReg Empty.elim (initializedInterior (P₀ := Empty) hR hQ)

def placedAmbientSourceRetire : Pr P₀ 256 Q A U :=
  embProg couplingSourceReg Empty.elim (retireAmbientSource (P₀ := Empty))

theorem placedInitializedInterior_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 256 Q A U) (S : Stacks 256 A) (borrowed : List (Fin (A+4)))
    (h127 : (embStk couplingSourceReg S).R 127 = []) (h138 : (embStk couplingSourceReg S).R 138 = [])
    (haMaster : ((embStk couplingSourceReg S).R 141).length = a) (hbMaster : ((embStk couplingSourceReg S).R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) (embStk couplingSourceReg S)) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' n, ∃ D : ZMod s → GaussianInt, v'.user = v.user ∧
      n ≤ initializedInteriorCost p l s t u target rhsExp a b ∧ (cstream A w (chirpLine s D)).length = s*w ∧
      Exec body (placedInitializedInterior hR hQ) (mk v S) n
        (mk v' { S with R := Function.update S.R 132 (cstream A w (chirpLine s D)++S.R 132) }) ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (fun k => (value q (D k)).re) x (1/(2 : ℝ)^target) := by
  dsimp only
  obtain ⟨vi,n,D,hu',hn,hlen,he,hDnorm,hDerror⟩ := initializedInterior_spec
    (body := fun p : Empty => nomatch p) hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad
    C hC x hx (embDn couplingSourceReg v) (embStk couplingSourceReg S) borrowed
    h127 h138 haMaster hbMaster hready
  obtain ⟨v',hv',hu'',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingSourceReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',n,D,hu''.trans hu',hn,hlen,he'.cast rfl ?_,hDnorm,hDerror⟩
  apply congrArg (mk v')
  rw [embOvr_updR couplingSourceReg_injective,embOvr_stk]
  rfl

theorem placedAmbientSourceRetire_exec (q s : ℕ) (raw tail : List (Fin (A+4)))
    (v : HS 256 Q A U) (S : Stacks 256 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsrc : S.R 110 = raw++tail) (hlen : raw.length = s*(2*q+8))
    (h94 : S.R 94 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retireAmbientSourceCost q s ∧
      Exec body placedAmbientSourceRetire (mk v S) m
        (mk v' {S with R := Function.update S.R 110 tail}) := by
  obtain ⟨vi,m,hu,hm,he⟩ := retireAmbientSource_exec (body := fun p : Empty => nomatch p)
    q s raw tail (embDn couplingSourceReg v) (embStk couplingSourceReg S) hq hs hsrc hlen h94 h131 h134 h135
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingSourceReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  rw [embOvr_updR couplingSourceReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
