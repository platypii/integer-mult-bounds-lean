module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloInput

/-! Run the concrete solver from its shared input contract. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U}

theorem PackedHaloInput.run (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    {p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    {C : ZMod s → GaussianInt} {tail E outputTail : List (Fin (A+4))} {S : Stacks 242 A}
    (hinput : PackedHaloInput (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C tail E outputTail S)
    (v : HS 248 Q A U) (x : ZMod s → ℝ)
    (hx : let B := haloBoundary s t (PhaseCellBand.width p u) a b
      let j := boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp B.card
      SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x
        (fun i => (value (executionPrecision p l j rhsExp) (C i)).re)) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∃ v' F n, ∃ D : ZMod s → GaussianInt,
      v'.user = v.user ∧ n ≤ packedHaloSolveCost p u l target rhsExp s t a b V ∧
      Exec body' (packedHaloSolve hR hQ) (IntegerMultBounds.MathlibTM2.Host.mk v (extendStacks (by decide) S)) n (IntegerMultBounds.MathlibTM2.Host.mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      (F.R 130).length = w ∧ F.R 104 = [] ∧ F.R 105 = [] ∧ F.R 109 = [] ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧
      (∀ i, Fits w (D i)) ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => (packedIntervalRead q w a (F.R 132) i).re) x (1/(2 : ℝ)^target) ∧
      ∃ residual : List (Fin (A+4)), residual.length = (b-a)*w ∧
        F.R 110 = residual++(cstream A w (packedInterval a (b-a) C)++tail) := by
  dsimp only
  obtain ⟨v₁,F₁,m,D,hu₁,hm,he,hin,hout,h93,h238,h138,h139,h140,h220,hfactor,hwidth,h104,h105,h109,
    hsource,hfits,herror,hbuffers⟩ := packedHaloSolve_spec (body := body) (body' := body')
    (p := p) (l := l) (s := s) (t := t) (u := u) (target := target) (rhsExp := rhsExp)
    (a := a) (b := b) (V := V) (α := α) (d := d) hR hQ hA hbody
    hinput.hp hinput.hwidth hinput.hα hinput.hst hinput.hu hinput.hαu hinput.hθ hinput.hgap hinput.hbudget
    hinput.hband hinput.has hinput.hbs hinput.hpad C tail E outputTail v S
    hinput.h109 hinput.h115 hinput.h116 hinput.hleft hinput.hready hinput.haMaster hinput.hbMaster
    hinput.h0 hinput.h139 hinput.h127 hinput.h138 hinput.h143 hinput.h147 hinput.h151 hinput.h153
    hinput.h152 hinput.hnew hinput.h132left hinput.hV hinput.h155 hinput.h165 hinput.hfitV
    hinput.hgeometryBlank hinput.h239 hinput.hab hinput.haLt hinput.hsep hinput.hwide hinput.hVeq
    hinput.hwV hinput.hcoords hinput.hunits hinput.hC hinput.h157 hinput.h158 hinput.h167
    hinput.houtput hinput.hE hinput.hfresh hinput.hrange hinput.hdom x hx
  exact ⟨v₁,F₁,m,D,hu₁,hm,he,hin,hout,hwidth,h104,h105,h109,hsource,hfits,herror,hbuffers⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
