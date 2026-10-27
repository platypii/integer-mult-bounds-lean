module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedInverseHeadersReady

/-! Construct, reuse and fully release one boundary page around the complete complex-input inverse. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 280 Q A U}

noncomputable def sharedInverseCoreCall (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 280 Q A U :=
  embProg sharedInverseCoreReg Empty.elim (sharedPageClosedComplex (P := Empty) hR hQ)

theorem sharedInverseCoreCall_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let band := PhaseCellBand.width p u
    let solveTarget := boundaryRecoveryTarget p (target+1)
    let bits := boundaryTableBits p solveTarget 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∀ (F : ZMod s → GaussianInt), (∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS 280 Q A U) (S : Stacks 280 A) (tail : List (Fin (A+4))),
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (chirpLine s F)++tail)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg (embStk sharedInverseCoreReg S)))))) →
    (∀ i, S.L (sharedInverseCoreReg i) = []) → (S.R (sharedInverseCoreReg 141)).length = a → (S.R (sharedInverseCoreReg 142)).length = b →
    (∀ i ∈ ([109,115,116,0,106,139,127,138,143,147,151,153,152,94,131,134,135,136,140] : List (Fin 240)), S.R (sharedInverseCoreReg i) = []) →
    (∀ i : Fin 240, 154 ≤ i.val → S.R (sharedInverseCoreReg i) = []) →
    S.R (sharedInverseCoreReg 137) = [] →
    ∀ (x y : ZMod s → ℝ),
    Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
    Solves (realMatrix s t p u) (haloVertices s a b) y (fun i => (value q (F i)).im) →
    ∃ v' n, ∃ Z : ZMod s → GaussianInt,
      let S' : Stacks 280 A := {S with R := Function.update S.R 132 (cstream A w (chirpLine s Z)++S.R 132)}
      v'.user = v.user ∧ n ≤ sharedPageClosedComplexCost p u l s t a b target ∧
      Exec body (sharedInverseCoreCall hR hQ) (mk v S) n (mk v' S') ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b) (pairedCellRead q w (S'.R 132))
        (fun i => (⟨x i,y i⟩ : ℂ)) (1/(2 : ℝ)^target) := by
  dsimp only
  intro F hF v S tail hready hleft ha hb hclean hnew h137 x y hx hy
  obtain ⟨v₁,n,Z,hu₁,hn,he,herror⟩ := sharedPageClosedComplex_spec
    (body := fun p : Empty => nomatch p) hR hQ hA hp hwidth hα hst hu hαu
    hθ hgap hbudget hband has hbs hpad F hF (embDn sharedInverseCoreReg v)
    (embStk sharedInverseCoreReg S) tail hready hleft ha hb hclean hnew h137 x y hx hy
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    sharedInverseCoreReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,Z,hu₂.trans hu₁,hn,he₂.cast rfl ?_,?_⟩
  · apply congrArg (mk v₂)
    exact sharedInverseOutput_frame S _
  · exact herror

theorem sharedInverseCoreCall_full_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) :
    let B := haloBoundary s t (PhaseCellBand.width p u) 0 s
    let band := PhaseCellBand.width p u
    let solveTarget := boundaryRecoveryTarget p (target+1)
    let bits := boundaryTableBits p solveTarget 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∀ (F : ZMod s → GaussianInt), (∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS 280 Q A U) (S : Stacks 280 A) (tail : List (Fin (A+4))),
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (chirpLine s F)++tail)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg (embStk sharedInverseCoreReg S)))))) →
    (∀ i, S.L (sharedInverseCoreReg i) = []) → (S.R (sharedInverseCoreReg 141)).length = 0 → (S.R (sharedInverseCoreReg 142)).length = s →
    (∀ i ∈ ([109,115,116,0,106,139,127,138,143,147,151,153,152,94,131,134,135,136,140] : List (Fin 240)), S.R (sharedInverseCoreReg i) = []) →
    (∀ i : Fin 240, 154 ≤ i.val → S.R (sharedInverseCoreReg i) = []) →
    S.R (sharedInverseCoreReg 137) = [] →
    ∀ z : ZMod s → ℂ,
    Matrix.mulVec (fun i j => (realMatrix s t p u i j : ℂ)) z = (fun i => value q (F i)) →
    ∃ v' n, ∃ Z : ZMod s → GaussianInt,
      let S' : Stacks 280 A := {S with R := Function.update S.R 132 (cstream A w (chirpLine s Z)++S.R 132)}
      v'.user = v.user ∧ n ≤ sharedPageClosedComplexCost p u l s t 0 s target ∧
      Exec body (sharedInverseCoreCall hR hQ) (mk v S) n (mk v' S') ∧
      ∀ i, ‖pairedCellRead q w (S'.R 132) i-z i‖ ≤ 1/(2 : ℝ)^target := by
  dsimp only
  intro F hF v S tail hready hleft ha hb hclean hnew h137 z hz
  have hfull : haloVertices s 0 s = Finset.univ := by
    ext i
    simp only [mem_haloVertices,Finset.mem_univ,iff_true]
    exact ⟨Nat.zero_le _,i.val_lt⟩
  have hx : Solves (realMatrix s t p u) (haloVertices s 0 s)
      (fun i => (z i).re) (fun i => (value
        (executionPrecision p l (initialSchurTarget p u
          (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
            (haloBoundary s t (PhaseCellBand.width p u) 0 s).card) 2) 2) (F i)).re) := by
    rw [hfull]
    intro i _
    have hh := congrArg Complex.re (congrFun hz i)
    simpa [Matrix.mulVec,dotProduct,Complex.mul_re] using hh
  have hy : Solves (realMatrix s t p u) (haloVertices s 0 s)
      (fun i => (z i).im) (fun i => (value
        (executionPrecision p l (initialSchurTarget p u
          (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
            (haloBoundary s t (PhaseCellBand.width p u) 0 s).card) 2) 2) (F i)).im) := by
    rw [hfull]
    intro i _
    have hh := congrArg Complex.im (congrFun hz i)
    simpa [Matrix.mulVec,dotProduct,Complex.mul_im] using hh
  obtain ⟨v',n,Z,hu',hn,he,herror⟩ := sharedInverseCoreCall_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband (Nat.zero_le s) (le_refl s)
    hpad F hF v S tail hready hleft ha hb hclean hnew h137
    (fun i => (z i).re) (fun i => (z i).im) hx hy
  refine ⟨v',n,Z,hu',hn,he,?_⟩
  intro i
  have hh := herror i (by rw [hfull]; exact Finset.mem_univ i)
  simpa only [Complex.eta] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
