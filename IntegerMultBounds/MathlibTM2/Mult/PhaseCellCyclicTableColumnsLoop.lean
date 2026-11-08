module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicTableLoopStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScanInvariant

/-! Compute all boundary columns under the packed-page invariant. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def cyclicTableColumnsLoop (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 154 Q A U :=
  scanP 152 153 (cyclicTableLoopStep hR hQ)

noncomputable def cyclicTableColumnsLoopCost (p u l s t a n target : ℕ) [NeZero s] : ℕ :=
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  (∑ k ∈ Finset.range B.card, (cyclicTableColumnCost p u l s t a n target k (bFoldAt s B k).val+1+3))+2*B.card+4

theorem cyclicTableColumnsLoop_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a < s) (hbs : n ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
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
    (h151 : S.R 151 = []) (h153 : S.R 153 = [])
    (hcount : (S.R 152).length = (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) :
    let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
    let W := 24*PhaseCellBand.width p u+1
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let w := executionWidth p l (initialSchurTarget p u target 2) 2
    ∃ v' m, ∃ columns : List (ZMod s → GaussianInt),
      let output := bandTableWords A w B W columns 0++S.R 132
      let S' : Stacks 154 A := {S with R := (Function.update (Function.update S.R 132 output)
        151 (List.replicate B.card tick))}
      v'.user = v.user ∧ m ≤ cyclicTableColumnsLoopCost p u l s t a n target ∧
      Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
        (cyclicTableColumnsLoop hR hQ) (mk v S) m (mk v' S') ∧ columns.length = B.card ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
          (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1 (1/(2 : ℝ)^target) columns ∧ ColumnFamilyFormat w columns ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
        q l s t u (PhaseCellBand.width p u) 0 0 tail
        (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S'))) := by
  dsimp only
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let W := 24*PhaseCellBand.width p u+1
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  let Sh := (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
    (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1
  let Inv := TableLoopInvariant q w B W Sh (1/(2 : ℝ)^target) S.R
  let c := fun k => cyclicTableColumnCost p u l s t a n target k (bFoldAt s B k).val+1
  have hframe : ∀ k R R', (∀ k : Fin 154, k ≠ 152 → k ≠ 153 → R' k = R k) → Inv k R → Inv k R' := by
    intro k R R' hr hInv
    exact hInv.of_frame hr
  have hstep : ∀ k < B.card, ∀ (vi : HS 154 Q A U) (Si : Stacks 154 A), Si.L = S.L → Inv k Si.R →
      ∃ v' R' m, v'.user = vi.user ∧ m ≤ c k ∧
        Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
          (cyclicTableLoopStep hR hQ) (mk vi Si) m (mk v' {Si with R := R'}) ∧
        R' 152 = Si.R 152 ∧ R' 153 = Si.R 153 ∧ Inv (k+1) R' := by
    intro k hn vi Si hL hInv
    exact cyclicTableLoopStep_spec (body := body) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
      k hn vi S tail pageTail hrows hpageWidth hpage hready haSrc hleftEnd hrightEnd h141 h142 h0 h139 h127 h138 h143 h147 Si hL hInv
  have hInv : Inv 0 S.R := by
    refine ⟨[],rfl,?_,by simp [ColumnFamilyFormat],?_⟩
    · intro k hn
      simp at hn
    · intro k _ _
      by_cases hk132 : k = 132 <;> by_cases hk151 : k = 151 <;>
        simp [tableLoopRegs,bandTableWords,hk132,hk151,h151]
  obtain ⟨v',R',m,hu',hm,he,h152,h153',hInv'⟩ := scanInvariant_exec
    (body := embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
    (show (152 : Fin 154) ≠ 153 by decide) hframe hstep 0 v S (by simp [hcount,B]) rfl hInv
  have hInvN : Inv B.card R' := by simpa [hcount] using hInv'
  obtain ⟨columns,hlen,hcolumns,hformat,hr⟩ := hInvN
  let S' : Stacks 154 A := {S with R := (Function.update (Function.update S.R 132
    (bandTableWords A w B W columns 0++S.R 132)) 151 (List.replicate B.card tick))}
  have hR : R' = S'.R := by
    funext k
    by_cases hk152 : k = 152
    · subst k; simpa [S',h153] using h152
    by_cases hk153 : k = 153
    · subst k; simpa [S',h153] using h153'
    simpa [S',tableLoopRegs,hlen] using hr k hk152 hk153
  rw [hR] at he
  refine ⟨v',m,columns,hu',?_,he,hlen,hcolumns,hformat,?_⟩
  · simpa [cyclicTableColumnsLoopCost,hcount,h153,c,B] using hm
  · apply tableLoopReady_of_frame (S' := S') hready rfl
    intro k hk hk132
    have hk151 : k ≠ 151 := by omega
    simp [S',hk132,hk151]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
