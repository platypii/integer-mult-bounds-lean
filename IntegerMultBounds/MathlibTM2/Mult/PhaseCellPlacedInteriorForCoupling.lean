module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInteriorForCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingSource
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallCouplingHeaders

/-! Execute the interior solve and reconstruct the next coupling runtime bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 256 Q A U}

noncomputable def placedInteriorForCoupling (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 256 Q A U :=
  embProg couplingSourceReg Empty.elim (interiorForCoupling (P₀ := Empty) hR hQ)

theorem placedInteriorForCoupling_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 256 Q A U) (S : Stacks 256 A) (borrowed outputTail : List (Fin (A+4)))
    (E₀ : ZMod s → GaussianInt)
    (hE₀ : ∀ k, ‖value (executionPrecision p l target rhsExp) (E₀ k)‖ ≤
      (2 : ℝ)^interiorOutputExponent p l target rhsExp)
    (hdst : (embStk couplingSourceReg S).R 132 = cstream A (executionWidth p l target rhsExp) (chirpLine s E₀)++outputTail)
    (h127 : (embStk couplingSourceReg S).R 127 = []) (h138 : (embStk couplingSourceReg S).R 138 = [])
    (haMaster : ((embStk couplingSourceReg S).R 141).length = a) (hbMaster : ((embStk couplingSourceReg S).R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) (embStk couplingSourceReg S)) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let band := PhaseCellBand.width p u
    ∃ v' n, ∃ D : ZMod s → GaussianInt,
      let T := embStk couplingSourceReg S
      let T' : Stacks 144 A := {T with R := (couplingHeadersR (2^15*p) q s t u band a b
        (Function.update T.R 132 (cstream A w (chirpLine s D)++outputTail)))}
      let S' := embOvr couplingSourceReg T'.get S
      v'.user = v.user ∧ n ≤ interiorForCouplingCost p l s t u target rhsExp a b ∧
      Exec body (placedInteriorForCoupling hR hQ) (mk v S) n (mk v' S') ∧
      CouplingReady (2^15*p) q w s t u band a b (cstream A w (chirpLine s C)++borrowed)
        (embStk groupReg (embStk couplingSourceReg S')) ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (fun k => (value q (D k)).re) x (1/(2 : ℝ)^target) := by
  dsimp only
  obtain ⟨vi,n,D,hu',hn,he,hcoupling,hDnorm,hDerror⟩ := interiorForCoupling_spec
    (body := fun p : Empty => nomatch p) hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hpad
    C hC x hx (embDn couplingSourceReg v) (embStk couplingSourceReg S) borrowed outputTail E₀ hE₀
    hdst h127 h138 haMaster hbMaster hready
  obtain ⟨v',hv',hu'',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingSourceReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',n,D,hu''.trans hu',hn,he',?_,hDnorm,hDerror⟩
  rw [embStk_ovr couplingSourceReg_injective]
  exact hcoupling

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
