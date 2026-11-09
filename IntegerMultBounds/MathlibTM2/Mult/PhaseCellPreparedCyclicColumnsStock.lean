module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCyclicColumns
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicTableUniformStock
public import IntegerMultBounds.MathlibTM2.Host.ClearBankExcept

/-! Execute and retire table-scan controls while preserving the derived shared reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

@[irreducible] def preparedCyclicColumnsWorkspace
    (J ringPush batchPush rowPush p l s t u target a n : ℕ) [NeZero s] : ℕ :=
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let W := 24*PhaseCellBand.width p u+1
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  2*(4*B.card+4)+(B.card*((2*W+1)*w+1)+
    (cyclicTableUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      J ringPush batchPush rowPush (cyclicTableEntryCostBound p l s t u target a n)
      p l s t u target a n+1))

theorem preparedCyclicColumns_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (has : a < s) (hbs : n ≤ s)
    (J ringPush batchPush : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ J)
    (hpushR : mnProgPush (rpProg (P := P₀) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ ringPush)
    (hpushK : mnProgPush (cmulBlock cr
      (rmulOne (P := P₀) (Q := Q) (A := A) (U := U) mul mul_injective (by decide) hQ cr)) ≤ batchPush)
    (rowPush : ℕ) (hrowPush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ rowPush)
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
      let S' : Stacks 154 A := {S with R := Function.update S.R 132 output}
      v'.user = v.user ∧ m ≤ (4*B.card+4)+(cyclicTableColumnsLoopCost p u l s t a n target+(4*B.card+5)) ∧
      ExecWithin (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
          preparedCyclicColumnsWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
            J ringPush batchPush rowPush p l s t u target a n)
        0 (preparedCyclicColumns hR hQ) (mk v S) m (mk v' S') ∧ columns.length = B.card ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
          (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1 (1/(2 : ℝ)^target) columns ∧ ColumnFamilyFormat w columns ∧
      PreparedBoundaryColumns A p target q w W B columns ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
        q l s t u (PhaseCellBand.width p u) 0 0 tail
        (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S'))) := by
  dsimp only
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let W := 24*PhaseCellBand.width p u+1
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  have h135 : S.R 135 = [] := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 135 (by simp)
  obtain ⟨v₁,hv₁,he₁⟩ := ucopy_exec
    (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
    (a := 116) (b := 152) (t := 135) (by decide) (by decide) (by decide) v S h135
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 152 (List.replicate B.card tick)}
  have he₁' : Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
      (ucopy 116 152 135) (mk v S) (4*B.card+4) (mk v₁ S₁) := by simpa [S₁,hrows,h152,B] using he₁
  have hproject : embStk tableReg S₁ = embStk tableReg S :=
    tableProject_updateR_outer S 152 (List.replicate B.card tick) (by decide)
  obtain ⟨v₂,m₂,columns,hv₂,hm₂,he₂,hlen,hacc,hformat,_⟩ := cyclicTableColumnsLoop_spec_uniform_workspace (body := body)
    hR hQ hA axis.hp axis.hpacket axis.hα axis.hst axis.hu axis.hαu axis.hθ axis.hgap axis.hbudget axis.hband has hbs axis.hpad J ringPush batchPush hpushJ hpushR hpushK rowPush hrowPush
    v₁ S₁ tail pageTail (by simpa [S₁] using hrows) (by simpa [S₁] using hpageWidth)
    (by simpa [S₁] using hpage) (by rw [hproject]; exact hready)
    (by simpa [S₁] using haSrc) (by simpa [S₁] using hleftEnd) (by simpa [S₁] using hrightEnd)
    (by simpa [S₁] using h141) (by simpa [S₁] using h142) (by simpa [S₁] using h0)
    (by simpa [S₁] using h139) (by simpa [S₁] using h127) (by simpa [S₁] using h138)
    (by simpa [S₁] using h143) (by simpa [S₁] using h147) (by simpa [S₁] using h151)
    (by simpa [S₁] using h153) (by simp [S₁,B])
  have hprepared := cyclicPreparedBoundaryColumns_of_accurate axis a n has hbs A target q w columns hlen hformat hacc
  let output := bandTableWords A w B W columns 0++S.R 132
  let F : Stacks 154 A := {S₁ with R := (Function.update (Function.update S₁.R 132 output) 151 (List.replicate B.card tick))}
  have he₂' : ExecWithin (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
      (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+0+
        (B.card*((2*W+1)*w+1)+
          (cyclicTableUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
            J ringPush batchPush rowPush (cyclicTableEntryCostBound p l s t u target a n)
            p l s t u target a n+1)))
      0 (cyclicTableColumnsLoop hR hQ) (mk v₁ S₁) m₂ (mk v₂ F)  := by
    have h := he₂.mono (J := fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+0+
      (B.card*((2*W+1)*w+1)+
        (cyclicTableUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
          J ringPush batchPush rowPush (cyclicTableEntryCostBound p l s t u target a n)
          p l s t u target a n+1))) (by
      intro d z hz
      dsimp only [B,W,w]
      omega)
    simpa [F,S₁,output,B,W,w] using h
  obtain ⟨v₃,hv₃,he₃⟩ := clearWords_exec
    (body := embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
    [(151 : Fin 154),152] (by decide) v₂ F
  have hsum : ([(151 : Fin 154),152].map (fun k => (F.R k).length)).sum = B.card+B.card := by simp [F,S₁]
  have hfinal : {F with R := fun k => if k ∈ [(151 : Fin 154),152] then [] else F.R k} =
      {S with R := Function.update S.R 132 output} := by
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hk151 : k = 151
      · subst k; simp [h151]
      by_cases hk152 : k = 152
      · subst k; simp [h152]
      simp [F,S₁,hk151,hk152,Function.update_apply]
  have hcopy : mnNativePushBound 2 (ucopy (P := P₀) (Q := Q) (A := A) (U := U) (116 : Fin 154) 152 135) := by
    simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have ht₁ := mn_native_exec_within he₁' 2 hcopy 0 _ (Nat.le_refl _)
  have ht₃ := mn_native_exec_within he₃ 0 (clearWords_native_zero _) 0
    (mnSize (mk v₁ S₁)+0+(B.card*((2*W+1)*w+1)+
      (cyclicTableUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J ringPush batchPush rowPush (cyclicTableEntryCostBound p l s t u target a n)
        p l s t u target a n+1)))
    (by simpa only [Nat.zero_mul,Nat.add_zero] using he₂'.final)
  have htail := ExecWithin.seq he₂' ht₃
  have ht := (mn_seq_within_add ht₁ htail).mono
    (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
      preparedCyclicColumnsWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J ringPush batchPush rowPush p l s t u target a n) (by
      intro d z hz
      unfold preparedCyclicColumnsWorkspace
      exact hz)
  refine ⟨v₃,(4*B.card+4)+(m₂+(4*B.card+5)),columns,hv₃.trans (hv₂.trans hv₁),
    Nat.add_le_add_left (Nat.add_le_add_right hm₂ _) _,
    ht.cast (by rw [hsum]; simp only [List.length_cons,List.length_nil]; omega) (congrArg (mk v₃) hfinal),
    hlen,hacc,hformat,hprepared,?_⟩
  apply tableLoopReady_of_frame (S' := {S with R := Function.update S.R 132 output}) hready rfl
  intro k _ hk132
  exact Function.update_of_ne hk132 _ _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
