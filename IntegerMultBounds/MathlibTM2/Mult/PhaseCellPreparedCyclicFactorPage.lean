module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCyclicColumns
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScaledFactorPageReady

/-! Execute the joint cyclic Schur table and its complete physical factor input page. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def preparedCyclicFactorPage (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 154 Q A U :=
  .seq (preparedCyclicColumns hR hQ) (scaledGeneratedFactorPage 24)

theorem preparedCyclicFactorPage_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (has : a < s) (hbs : n ≤ s)
    (v : HS 154 Q A U) (S : Stacks 154 A) (tail : List (Fin (A+4)))
    (pageTail : List (Fin (A+4)))
    (hrows : (S.R 116).length = (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card)
    (hpageWidth : (S.R 115).length = publicationGeometryWidth t (PhaseCellBand.width p u))
    (hpage : S.R 109 = cstream A (publicationGeometryWidth t (PhaseCellBand.width p u))
      ((bFoldOrder s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)).map
        (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u target 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S))))
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (h141 : S.R 141 = []) (h142 : S.R 142 = [])
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = [])
    (h151 : S.R 151 = []) (h152 : S.R 152 = []) (h153 : S.R 153 = []) :
    let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
    let W := 24*PhaseCellBand.width p u+1
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let w := executionWidth p l (initialSchurTarget p u target 2) 2
    ∃ v' m, ∃ columns : List (ZMod s → GaussianInt),
      let output := bandTableWords A w B W columns 0++S.R 132
      let inputPage := cstream A w ((factorWindowValues B W columns).flatten++
        (factorInputValues B W B.card columns).flatten)
      let S' : Stacks 154 A := {S with R := (Function.update (Function.update S.R 132 output)
        140 (inputPage++S.R 140))}
      v'.user = v.user ∧ m ≤ ((4*B.card+4)+(cyclicTableColumnsLoopCost p u l s t a n target+(4*B.card+5)))+
        scaledGeneratedFactorPageCost 24 q (PhaseCellBand.width p u) B.card ∧
      Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
        (preparedCyclicFactorPage hR hQ) (mk v S) m (mk v' S') ∧ columns.length = B.card ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
          (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1 (1/(2 : ℝ)^target) columns ∧ ColumnFamilyFormat w columns ∧
      PreparedBoundaryColumns A p target q w W B columns ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
        q l s t u (PhaseCellBand.width p u) 0 0 tail
        (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg {S' with R := Function.update S'.R 140 []}))) := by
  dsimp only
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let W := 24*PhaseCellBand.width p u+1
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  obtain ⟨v₁,m₁,columns,hv₁,hm₁,he₁,hlen,hacc,hformat,hprepared,hready₁⟩ := preparedCyclicColumns_spec (body := body)
    hR hQ hA axis has hbs v S tail pageTail hrows hpageWidth hpage hready haSrc hleftEnd hrightEnd
    h141 h142 h0 h139 h127 h138 h143 h147 h151 h152 h153
  let output := bandTableWords A w B W columns 0++S.R 132
  let F : Stacks 154 A := {S with R := Function.update S.R 132 output}
  have hreadyF : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      q l s t u (PhaseCellBand.width p u) 0 0 tail
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg F))) := hready₁
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := scaledGeneratedFactorPage_ready_exec
    (body := embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))) B
    24 (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1) q l t u
    (PhaseCellBand.width p u) 0 0 tail (S.R 132) columns hlen (by simpa only [← hw] using hformat)
    (by omega) v₁ F hreadyF (by simpa [F,B] using hrows) (by simp [F,output,W,hw])
    (by simpa [F] using h138) (by simpa [F] using h151) (by simpa [F] using h152) (by simpa [F] using h153)
  let inputPage := cstream A w ((factorWindowValues B W columns).flatten++(factorInputValues B W B.card columns).flatten)
  let G : Stacks 154 A := {F with R := Function.update F.R 140 (inputPage++S.R 140)}
  have he₂' : Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
      (scaledGeneratedFactorPage 24) (mk v₁ F) m₂ (mk v₂ G) := by
    simpa [G,F,inputPage,← hw,W] using he₂
  have h140 : S.R 140 = [] := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 140 (by simp)
  have hreset : {G with R := Function.update G.R 140 []} = F := by
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hk : k = 140 <;> simp [G,F,hk,h140,Function.update_apply]
  refine ⟨v₂,m₁+m₂,columns,hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂,
    Exec.seq he₁ he₂',hlen,hacc,hformat,hprepared,?_⟩
  change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _ (embStk componentReg (embStk boundaryArithmeticReg
    (embStk tableReg {G with R := Function.update G.R 140 []})))
  rw [hreset]
  exact hreadyF

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
