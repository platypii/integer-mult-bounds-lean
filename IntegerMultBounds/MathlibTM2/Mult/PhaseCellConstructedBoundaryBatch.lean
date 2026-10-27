module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryBatch

/-! Execute one generated factor setup followed by a whole batch on the same computed page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def constructedBoundaryBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 234 Q A U :=
  .seq (embProg preparedBoundaryBatchCoreReg id (preparedBoundaryFactory hR hQ)) (preparedBoundaryBatch hQ)

theorem constructedBoundaryBatch_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 234 Q A U) (S : Stacks 234 A) (tail : List (Fin (A+4)))
    (h109 : S.R 109 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (hleft : ∀ i : Fin 224, S.L (preparedBoundaryBatchCoreReg (preparedBoundaryCoreReg i)) = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u
      (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
      l s t u (PhaseCellBand.width p u) 0 0 tail
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg (embStk preparedBoundaryBatchCoreReg S)))))))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (h0 : S.R 0 = []) (h139 : S.R 139 = []) (h127 : S.R 127 = []) (h138 : S.R 138 = [])
    (h143 : S.R 143 = []) (h147 : S.R 147 = []) (h151 : S.R 151 = []) (h153 : S.R 153 = [])
    (h152 : S.R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R (preparedBoundaryBatchCoreReg (preparedBoundaryCoreReg i)) = [])
    (bs : List (List GaussianInt)) (hrows : ∀ x ∈ bs, x.length = (haloBoundary s t (PhaseCellBand.width p u) a b).card)
    (hbound : ∀ xs ∈ bs, ∀ x ∈ xs,
      |gv (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) x.re| ≤ 1/2 ∧
      |gv (executionPrecision p l (initialSchurTarget p u
        (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) x.im| ≤ 1/2)
    (rhsTail : List (Fin (A+4)))
    (h225 : S.R 225 = []) (h227 : S.R 227 = []) (h228 : S.R 228 = []) (h230 : S.R 230 = [])
    (h231 : S.R 231 = []) (h232 : S.R 232 = []) (h233 : S.R 233 = [])
    (hcount : (S.R 229).length = bs.length)
    (hsource : S.R 226 = cstream A (executionWidth p l (initialSchurTarget p u
      (boundaryTableBits p target rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) bs.flatten++rhsTail) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p target rhsExp B.card
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    ∃ v' page n, ∃ columns : List (ZMod s → GaussianInt),
      let σ := boundaryFactorState (embStk preparedBoundaryCoreReg (embStk preparedBoundaryBatchCoreReg page))
      let AZ := factorRankIntegerMatrix B W columns
      let solve := bandSolveVec q W (naturalLineLc q K W B.card AZ)
        (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ)
      v'.user = v.user ∧ n ≤ constructedBoundaryFactorCost p u l s t a b target rhsExp+
        preparedBoundaryBatchCost w B.card W bs.length ∧
      Exec (embTab preparedBoundaryBatchCoreReg (embTab preparedBoundaryCoreReg
        (embTab boundaryFactorLegacyReg (embTab tableReg
          (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))))
        (constructedBoundaryBatch hR hQ) (mk v S) n
        (mk v' {page with R := Function.update page.R 224 (cstream A w (bs.map solve).flatten++S.R 224)}) ∧
      columns.length = B.card ∧ ColumnFamilyFormat w columns ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b) (haloInterior s t band a b).toList).1
        (1/(2 : ℝ)^bits) columns ∧
      BoundarySolveReady σ q w W B.card ∧
      σ .bo = cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten ∧
      σ .hf = cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten ∧
      σ .df = cstream A w ((naturalLineRcs q K W B.card AZ).map fun x => (⟨x,0⟩ : GaussianInt)) ∧
      page.R 206 = [] ∧ page.R 225 = [] ∧
      (∀ i : Fin 224, page.L (preparedBoundaryBatchCoreReg (preparedBoundaryCoreReg i)) = []) ∧
      (∀ i : Fin 64, page.R (preparedBoundaryBatchCoreReg (preparedBoundaryCoreReg (boundaryFactorMulReg i))) = []) ∧
      (∀ k : Fin 234, 226 ≤ k.val → page.R k = S.R k) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p target rhsExp B.card
  let W := 12*PhaseCellBand.width p u+1
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let T := embStk preparedBoundaryBatchCoreReg S
  let coreBody := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
    (embTab componentReg (embTab groupReg body))))
  let nativeBody := embTab preparedBoundaryCoreReg coreBody
  let outerBody := embTab preparedBoundaryBatchCoreReg nativeBody
  obtain ⟨v₁,T₁,n₁,columns,hu₁,hn₁,he₁,hlen,hformat,hcolumns,hstage,hsolve,hbo,hhf,hdf,h206,h224,h225',hleft',hmul⟩ :=
    preparedBoundaryFactory_spec (body := body) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
      (embDn preparedBoundaryBatchCoreReg v) T tail h109 h115 h116 hleft hready haMaster hbMaster
      h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
  obtain ⟨v₁',hv₁',hu₁',he₁'⟩ := exec_emb_ovr (ι := id) (body' := outerBody) preparedBoundaryBatchCoreReg_injective
    (fun _ => rfl) he₁ v rfl S rfl
  let page := embOvr preparedBoundaryBatchCoreReg T₁.get S
  have hproj : embStk preparedBoundaryBatchCoreReg page = T₁ := embStk_ovr preparedBoundaryBatchCoreReg_injective T₁ S
  have hprivate (k : Fin 234) (hk : 226 ≤ k.val) : page.R k = S.R k :=
    (embOvr_off (e := preparedBoundaryBatchCoreReg) T₁.get S (fun i => preparedBoundaryBatchCoreReg_off i k hk)).2
  have h206' : page.R 206 = [] := (congrArg (fun R : Stacks 226 A => R.R 206) hproj).trans h206
  have h224' : page.R 224 = S.R 224 := (congrArg (fun R : Stacks 226 A => R.R 224) hproj).trans h224
  have h225'' : page.R 225 = [] := (congrArg (fun R : Stacks 226 A => R.R 225) hproj).trans (h225'.trans h225)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := preparedBoundaryBatch_exec (body := coreBody) hQ hA p u l target rhsExp B W columns hp hlen
    hformat hstage bs hrows hbound v₁' page rhsTail
    (by rw [hproj]; exact hleft') (by rw [hproj]; exact hmul) (by rw [hproj]; exact hsolve)
    (by rw [hproj]; exact hbo) (by rw [hproj]; exact hhf) (by rw [hproj]; exact hdf) h206' h225''
    ((hprivate 227 (by decide)).trans h227) ((hprivate 228 (by decide)).trans h228)
    ((hprivate 230 (by decide)).trans h230) ((hprivate 231 (by decide)).trans h231)
    ((hprivate 232 (by decide)).trans h232) ((hprivate 233 (by decide)).trans h233)
    (by rw [hprivate 229 (by decide)]; exact hcount) ((hprivate 226 (by decide)).trans hsource)
  refine ⟨v₂,page,n₁+n₂,columns,hu₂.trans (hu₁'.trans hu₁),Nat.add_le_add hn₁ hn₂,?_,hlen,hformat,hcolumns,?_,?_,?_,?_,h206',h225'',?_,?_,hprivate⟩
  · simpa only [constructedBoundaryBatch,outerBody,nativeBody,coreBody,B,W,h224'] using Exec.seq he₁' he₂
  · rw [hproj]; exact hsolve
  · rw [hproj]; exact hbo
  · rw [hproj]; exact hhf
  · rw [hproj]; exact hdf
  · intro i
    have hh := congrArg (fun T : Stacks 226 A => T.L (preparedBoundaryCoreReg i)) hproj
    exact hh.trans (hleft' i)
  · intro i
    have hh := congrArg (fun T : Stacks 226 A => T.R (preparedBoundaryCoreReg (boundaryFactorMulReg i))) hproj
    exact hh.trans (hmul i)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
