module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyBatchCoreReady
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! One raw-bank placement of a shared setup around a counted complex batch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

noncomputable def familyInverseBatchCoreCall (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 303 Q A U :=
  embProg familyInverseCoreReg Empty.elim (generatedClosedFamilyComplexBatch (P := Empty) recovery hR hQ)

theorem familyInverseBatchCoreCall_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (ha : a ≤ s) (hb : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∀ (Fs : List (ZMod s → GaussianInt)), (∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS 303 Q A U) (S : Stacks 303 A) (tail : List (Fin (A+4))),
    FamilyBatchCoreReady recovery p u l target s t a b Fs.length
      (cstream A w (Fs.map (chirpLine s)).flatten++tail) S →
    ∀ (x y : (ZMod s → GaussianInt) → ZMod s → ℝ),
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (x F) (fun i => (value q (F i)).re)) →
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (y F) (fun i => (value q (F i)).im)) →
    ∃ v' n, ∃ Zs : List (ZMod s → GaussianInt),
      v'.user = v.user ∧ n ≤ generatedClosedFamilyComplexBatchCost A p u l s t a b target Fs.length ∧
      Exec body (familyInverseBatchCoreCall recovery hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R 132 (cstream A w (Zs.map (chirpLine s)).flatten++S.R 132))}) ∧
      List.Forall₂ (fun F Z => PhaseCellInterface.ErrorOn (haloVertices s a b)
        (pairedCellRead q w (cstream A w (chirpLine s Z)++S.R 132))
          (fun i => (⟨x F i,y F i⟩ : ℂ)) (1/(2 : ℝ)^target)) Fs Zs ∧
      ∀ C, mnProgPush (familyInverseBatchCoreCall (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*generatedClosedFamilyComplexBatchStockCost A p u l s t a b target Fs.length)
          depth (familyInverseBatchCoreCall recovery hR hQ) (mk v S) n
          (mk v' {S with R := (Function.update S.R 132 (cstream A w (Zs.map (chirpLine s)).flatten++S.R 132))}) := by
  dsimp only
  intro Fs hF v S tail hr x y hx hy
  obtain ⟨vi,n,Zs,hui,hcost,he,herror,htrace⟩ := generatedClosedFamilyComplexBatch_spec
    (body := fun f : Empty => nomatch f) recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
    hband ha hb hpad Fs hF (embDn familyInverseCoreReg v) (embStk familyInverseCoreReg S) tail
    (by simpa only [executionPrecision,executionStagePrecision,← inverseExecutionExponent_eq] using hr.native) hr.couplingGuard hr.couplingWords hr.couplingRows hr.familyFresh hr.left hr.aLength hr.bLength
    hr.lowerBlank hr.upperBlank hr.count hr.fresh hr.extraBlank x y hx hy
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    familyInverseCoreReg_injective (fun f => nomatch f) he v rfl S rfl
  let output := cstream A (executionWidth p l (initialSchurTarget p u
    (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (Zs.map (chirpLine s)).flatten
  have hfinal : embOvr familyInverseCoreReg
      ({embStk familyInverseCoreReg S with R := Function.update (embStk familyInverseCoreReg S).R 132 (output++S.R 132)}).get S =
      {S with R := Function.update S.R 132 (output++S.R 132)} := by
    rw [embOvr_updR familyInverseCoreReg_injective,embOvr_stk]
    rfl
  have heOut := he'.cast rfl (congrArg (mk v') hfinal)
  refine ⟨v',n,Zs,hu'.trans hui,hcost,heOut,herror,?_⟩
  intro C hpC hbC depth
  have hpSmall : mnProgPush (generatedClosedFamilyComplexBatch (P := Empty) (U := U) (A := A) recovery hR hQ) ≤ C := by
    simpa only [familyInverseBatchCoreCall,embProg_push] using hpC
  have hs := htrace C hpSmall (fun f => nomatch f) depth
  obtain ⟨vf,hvf,huf,ht⟩ := exec_emb_ovr_within_stock familyInverseCoreReg
    familyInverseCoreReg_injective (ι := Empty.elim) (body' := body) (fun f => nomatch f) hs v rfl S rfl
  have hsame := (ht.toExec.unique heOut).2
  rw [hsame] at ht
  exact ht

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
