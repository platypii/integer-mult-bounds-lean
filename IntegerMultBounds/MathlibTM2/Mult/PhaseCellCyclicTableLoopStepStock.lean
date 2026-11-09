module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicTableLoopStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicTableColumnStock

/-! Extend the canonical packed-table invariant with a bounded actual column step. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem cyclicTableLoopStep_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a < s) (hbs : n ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (k : ℕ) (hn : k < (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card)
    (J ringPush batchPush : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ J)
    (hpushR : mnProgPush (rpProg (P := P₀) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ ringPush)
    (hpushK : mnProgPush (cmulBlock cr
      (rmulOne (P := P₀) (Q := Q) (A := A) (U := U) mul mul_injective (by decide) hQ cr)) ≤ batchPush)
    (rowPush : ℕ) (hrowPush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ rowPush)
    (cap : ℕ)
    (hcollectionCost :
      let q := executionPrecision p l (initialSchurTarget p u target 2) 2
      let band := PhaseCellBand.width p u
      let B := cyclicPrincipalBoundary s t band a n
      ∀ i < min B.card (k+(24*band+1)+1)-(k-(24*band+1)),
        cyclicColumnEntryStepCost q (publicationGeometryWidth t band) s a (a+min n (s-a))
          (k-(24*band+1)+i) (bFoldAt s B (k-(24*band+1)+i)).val ≤ cap)
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
    (Si : Stacks 154 A) (hL : Si.L = S.L)
    (hInv : TableLoopInvariant (executionPrecision p l (initialSchurTarget p u target 2) 2)
      (executionWidth p l (initialSchurTarget p u target 2) 2)
      (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n) (24*PhaseCellBand.width p u+1)
      (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
        (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1 (1/(2 : ℝ)^target) S.R k Si.R) :
    ∃ v' R' m, v'.user = v.user ∧
      m ≤ cyclicTableColumnCost p u l s t a n target k
        (bFoldAt s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n) k).val+1 ∧
      ExecWithin (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
        (fun d z => mnSize z+d ≤ mnSize (mk v Si)+0+
          (cyclicTableColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
            J ringPush batchPush rowPush cap p l s t u target a n k+1))
        0 (cyclicTableLoopStep hR hQ) (mk v Si) m (mk v' {Si with R := R'}) ∧
      mnSize (mk v' {Si with R := R'}) ≤ mnSize (mk v Si)+
        ((2*(24*PhaseCellBand.width p u+1)+1)*
          executionWidth p l (initialSchurTarget p u target 2) 2+1) ∧
      R' 152 = Si.R 152 ∧ R' 153 = Si.R 153 ∧
      TableLoopInvariant (executionPrecision p l (initialSchurTarget p u target 2) 2)
      (executionWidth p l (initialSchurTarget p u target 2) 2)
      (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n) (24*PhaseCellBand.width p u+1)
      (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
        (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1 (1/(2 : ℝ)^target) S.R (k+1) R' := by
  let boundary := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let band := PhaseCellBand.width p u
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  let j := bFoldAt s boundary k
  obtain ⟨columns,hlen,hcolumns,hformat,hr⟩ := hInv
  have hoff (k : Fin 154) (hk132 : k ≠ 132) (hk151 : k ≠ 151) (hk152 : k ≠ 152) (hk153 : k ≠ 153) :
      Si.R k = S.R k := by rw [hr k hk152 hk153]; simp [tableLoopRegs,hk132,hk151]
  have hcursor : (Si.R 151).length = k := by rw [hr 151 (by decide) (by decide)]; simp [tableLoopRegs,hlen]
  have hreadyi := TableLoopInvariant.ready hready hL ⟨columns,hlen,hcolumns,hformat,hr⟩
  obtain ⟨v₁,m₁,E,hu₁,hm₁,he₁,hreal,hnorm,herror,_⟩ := cyclicTableColumn_spec_within (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad k hn J ringPush batchPush hpushJ hpushR hpushK rowPush hrowPush cap hcollectionCost v Si tail pageTail hcursor
    (by rw [hoff 0 (by decide) (by decide) (by decide) (by decide)]; exact h0)
    (by rw [hoff 139 (by decide) (by decide) (by decide) (by decide)]; exact h139)
    (by rw [hoff 115 (by decide) (by decide) (by decide) (by decide)]; exact hpageWidth)
    (by rw [hoff 116 (by decide) (by decide) (by decide) (by decide)]; exact hrows)
    (by rw [hoff 109 (by decide) (by decide) (by decide) (by decide)]; exact hpage)
    (by rw [hoff 144 (by decide) (by decide) (by decide) (by decide)]; exact haSrc)
    (by rw [hoff 145 (by decide) (by decide) (by decide) (by decide)]; exact hleftEnd)
    (by rw [hoff 146 (by decide) (by decide) (by decide) (by decide)]; exact hrightEnd)
    (by intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hoff 127 (by decide) (by decide) (by decide) (by decide)]; exact h127
        · rw [hoff 138 (by decide) (by decide) (by decide) (by decide)]; exact h138
        · rw [hoff 141 (by decide) (by decide) (by decide) (by decide)]; exact h141
        · rw [hoff 142 (by decide) (by decide) (by decide) (by decide)]; exact h142
        · rw [hoff 143 (by decide) (by decide) (by decide) (by decide)]; exact h143
        · rw [hoff 147 (by decide) (by decide) (by decide) (by decide)]; exact h147) hreadyi
  let output := bandColumnWords A w boundary (24*band+1) k E++Si.R 132
  let S₁ : Stacks 154 A := {Si with R := Function.update Si.R 132 output}
  have he₂ := Exec.act (body := embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
    (.push (.rt 151) (fun _ => tick) .done) (mk v₁ S₁)
  let R' : Regs 154 A := Function.update S₁.R 151 (tick::Si.R 151)
  have he₂' : Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
      (.act (.push (.rt 151) (fun _ => tick) .done)) (mk v₁ S₁) 1 (mk v₁ {Si with R := R'}) := by
    simpa [S₁,R',Action.run,update_rt] using he₂
  have hpush : mnNativePushBound 1
      (.act (.push (.rt (151 : Fin 154)) (fun _ => tick) .done) : Pr P₀ 154 Q A U) := by
    simp [mnNativePushBound,mnActPush]
  have ht₂ := mn_native_exec_within he₂' 1 hpush 0 _ (Nat.le_refl _)
  have ht := mn_seq_within_add he₁ ht₂
  have hstock₁ : mnSize (mk v₁ S₁)+(Si.R 132).length = mnSize (mk v Si)+output.length := by
    simpa only [S₁,mk,update_rt,get_rt] using mn_size_update (mk v Si) v₁ (.rt 132) output
  have hstock₂ : mnSize (mk v₁ {Si with R := R'})+(S₁.R 151).length =
      mnSize (mk v₁ S₁)+(tick::Si.R 151).length := by
    simpa only [R',S₁,mk,update_rt,get_rt] using
      mn_size_update (mk v₁ S₁) v₁ (.rt 151) (tick::Si.R 151)
  have hwords : (bandColumnWords A w boundary (24*band+1) k E).length ≤ (2*(24*band+1)+1)*w := by
    simpa [bandColumnWords] using
      Nat.mul_le_mul_right w (foldedBandRows_length_le boundary (24*band+1) k)
  have hgrowth : mnSize (mk v₁ {Si with R := R'}) ≤ mnSize (mk v Si)+((2*(24*band+1)+1)*w+1) := by
    have h151 : S₁.R 151 = Si.R 151 := by simp [S₁]
    rw [h151,List.length_cons] at hstock₂
    dsimp only [output] at hstock₁
    rw [List.length_append] at hstock₁
    omega
  refine ⟨v₁,R',m₁+1,hu₁,Nat.add_le_add_right hm₁ 1,ht,hgrowth,by simp [R',S₁],by simp [R',S₁],?_⟩
  refine ⟨columns++[E],by simp [hlen],?_,?_,?_⟩
  · apply ColumnFamilyAccurate.append _ _ _ _ _ _ _ _ hcolumns
    intro i hi
    simpa [columnWordRead,hlen,q,w,band,boundary,j] using herror i hi
  · apply ColumnFamilyFormat.append w columns E hformat hreal
    intro i
    exact fits_of_value_power
      (stableInteriorResidual_width p u l (initialSchurTarget p u target 2) 2) (E i) (hnorm i)
  · intro k hk152 hk153
    by_cases hk132 : k = 132
    · subst k
      rw [show R' 132 = output by simp [R',S₁]]
      dsimp only [output]
      rw [hr 132 (by decide) (by decide)]
      simp [tableLoopRegs,bandTableWords_append,hlen,List.append_assoc,w,band,boundary]
    by_cases hk151 : k = 151
    · subst k
      rw [show R' 151 = tick::Si.R 151 by simp [R'],hr 151 (by decide) (by decide)]
      simp [tableLoopRegs,List.replicate_succ]
    rw [show R' k = Si.R k by simp [R',S₁,hk132,hk151],hr k hk152 hk153]
    simp [tableLoopRegs,hk132,hk151]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
