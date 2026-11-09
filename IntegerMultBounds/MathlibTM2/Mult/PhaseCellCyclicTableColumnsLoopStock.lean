module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicTableColumnsLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicTableLoopStepStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScanInvariantStock

/-! The complete table scan shares one arithmetic reserve above retained output. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem cyclicTableColumnsLoop_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a < s) (hbs : n ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (J ringPush batchPush : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ J)
    (hpushR : mnProgPush (rpProg (P := P₀) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ ringPush)
    (hpushK : mnProgPush (cmulBlock cr
      (rmulOne (P := P₀) (Q := Q) (A := A) (U := U) mul mul_injective (by decide) hQ cr)) ≤ batchPush)
    (rowPush : ℕ) (hrowPush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ rowPush)
    (cap reserve : ℕ)
    (hcollectionCost : ∀ k < (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card,
      let q := executionPrecision p l (initialSchurTarget p u target 2) 2
      let band := PhaseCellBand.width p u
      let B := cyclicPrincipalBoundary s t band a n
      ∀ i < min B.card (k+(24*band+1)+1)-(k-(24*band+1)),
        cyclicColumnEntryStepCost q (publicationGeometryWidth t band) s a (a+min n (s-a))
          (k-(24*band+1)+i) (bFoldAt s B (k-(24*band+1)+i)).val ≤ cap)
    (hworkspace : ∀ k < (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card,
      cyclicTableColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J ringPush batchPush rowPush cap p l s t u target a n k+1 ≤ reserve)
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
      ExecWithin (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+
          B.card*((2*W+1)*w+1)+0+reserve)
        0 (cyclicTableColumnsLoop hR hQ) (mk v S) m (mk v' S') ∧ columns.length = B.card ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
          (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1 (1/(2 : ℝ)^target) columns ∧ ColumnFamilyFormat w columns ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
        q l s t u (PhaseCellBand.width p u) 0 0 tail
        (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S'))) := by
  dsimp only
  obtain ⟨v',m,columns,hu',hm,he,hlen,hcolumns,hformat,hready'⟩ := cyclicTableColumnsLoop_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
    v S tail pageTail hrows hpageWidth hpage hready haSrc hleftEnd hrightEnd
    h141 h142 h0 h139 h127 h138 h143 h147 h151 h153 hcount
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

  let growth := (2*W+1)*w+1
  let boundary := fun k => mnSize (mk v S)+k*growth
  let bound := boundary B.card
  have hboundary : ∀ k ≤ B.card, boundary k ≤ bound := by
    intro k hk
    exact Nat.add_le_add_left (Nat.mul_le_mul_right growth hk) _
  have hstep : InvariantBoundedStockSpec
      (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
      (cyclicTableLoopStep hR hQ) 152 153 Inv S.L c boundary B.card bound reserve 0 := by
    intro k hk vi Si hL hInv hsize
    obtain ⟨vf,Rf,mf,huf,hmf,hef,hgrowth,h152,h153,hnext⟩ := cyclicTableLoopStep_spec_within (body := body)
      hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad k hk
      J ringPush batchPush hpushJ hpushR hpushK rowPush hrowPush cap (hcollectionCost k hk)
      vi S tail pageTail hrows hpageWidth hpage hready haSrc hleftEnd hrightEnd
      h141 h142 h0 h139 h127 h138 h143 h147 Si hL hInv
    have hcap := hworkspace k hk
    have hsize' : mnSize (mk vi Si) ≤ bound := hsize.trans (hboundary k hk.le)
    have hw := hef.mono (J := fun d z => mnSize z+d ≤ bound+0+reserve) (by
      intro d z hz
      omega)
    refine ⟨vf,Rf,mf,huf,hmf,hw,h152,h153,hnext,?_⟩
    change mnSize (mk vf {Si with R := Rf}) ≤ mnSize (mk v S)+(k+1)*growth
    change mnSize (mk vf {Si with R := Rf}) ≤ mnSize (mk vi Si)+growth at hgrowth
    change mnSize (mk vi Si) ≤ mnSize (mk v S)+k*growth at hsize
    rw [Nat.add_mul,Nat.one_mul]
    omega
  have hInv : Inv 0 S.R := by
    refine ⟨[],rfl,?_,by simp [ColumnFamilyFormat],?_⟩
    · intro k hn
      simp at hn
    · intro k _ _
      by_cases hk132 : k = 132 <;> by_cases hk151 : k = 151 <;>
        simp [tableLoopRegs,bandTableWords,hk132,hk151,h151]

  have hw := scanInvariant_within_bounded_stock
    (show (152 : Fin 154) ≠ 153 by decide) hframe hboundary hstep 0 v S
    (by simp [hcount,B]) rfl hInv
    (by simp [boundary]) he
  exact ⟨v',m,columns,hu',hm,hw,hlen,hcolumns,hformat,hready'⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
