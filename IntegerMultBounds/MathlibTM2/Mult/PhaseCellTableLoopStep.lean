module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableLoopInvariant

/-! Extend the packed-page invariant by one actually computed column. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def tableLoopStep (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 154 Q A U :=
  .seq (tableColumn hR hQ) (.act (.push (.rt 151) (fun _ => tick) .done))

theorem tableLoopStep_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (n : ℕ) (hn : n < (haloBoundary s t (PhaseCellBand.width p u) a b).card)
    (v : HS 154 Q A U) (S : Stacks 154 A) (tail : List (Fin (A+4)))
    (pageTail : List (Fin (A+4)))
    (hrows : (S.R 116).length = (haloBoundary s t (PhaseCellBand.width p u) a b).card)
    (hpageWidth : (S.R 115).length = publicationGeometryWidth t (PhaseCellBand.width p u))
    (hpage : S.R 109 = cstream A (publicationGeometryWidth t (PhaseCellBand.width p u))
      ((bFoldOrder s (haloBoundary s t (PhaseCellBand.width p u) a b)).map
        (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u target 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S))))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = []) 
    (Si : Stacks 154 A) (hL : Si.L = S.L)
    (hInv : TableLoopInvariant (executionPrecision p l (initialSchurTarget p u target 2) 2)
      (executionWidth p l (initialSchurTarget p u target 2) 2)
      (haloBoundary s t (PhaseCellBand.width p u) a b) (12*PhaseCellBand.width p u+1)
      (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
        (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 (1/(2 : ℝ)^target) S.R n Si.R) :
    ∃ v' R' m, v'.user = v.user ∧
      m ≤ tableColumnCost p u l s t a b target n
        (bFoldAt s (haloBoundary s t (PhaseCellBand.width p u) a b) n).val+1 ∧
      Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
        (tableLoopStep hR hQ) (mk v Si) m (mk v' {Si with R := R'}) ∧
      R' 152 = Si.R 152 ∧ R' 153 = Si.R 153 ∧
      TableLoopInvariant (executionPrecision p l (initialSchurTarget p u target 2) 2)
      (executionWidth p l (initialSchurTarget p u target 2) 2)
      (haloBoundary s t (PhaseCellBand.width p u) a b) (12*PhaseCellBand.width p u+1)
      (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
        (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 (1/(2 : ℝ)^target) S.R (n+1) R' := by
  let boundary := haloBoundary s t (PhaseCellBand.width p u) a b
  let band := PhaseCellBand.width p u
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  let j := bFoldAt s boundary n
  obtain ⟨columns,hlen,hcolumns,hr⟩ := hInv
  have hoff (k : Fin 154) (hk132 : k ≠ 132) (hk151 : k ≠ 151) (hk152 : k ≠ 152) (hk153 : k ≠ 153) :
      Si.R k = S.R k := by rw [hr k hk152 hk153]; simp [tableLoopRegs,hk132,hk151]
  have hcursor : (Si.R 151).length = n := by rw [hr 151 (by decide) (by decide)]; simp [tableLoopRegs,hlen]
  have hreadyi := TableLoopInvariant.ready hready hL ⟨columns,hlen,hcolumns,hr⟩
  obtain ⟨v₁,m₁,D,hu₁,hm₁,he₁,hreal,hnorm,herror,hready₁⟩ := tableColumn_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad n hn v Si tail pageTail
    (by rw [hoff 116 (by decide) (by decide) (by decide) (by decide)]; exact hrows)
    hcursor
    (by rw [hoff 115 (by decide) (by decide) (by decide) (by decide)]; exact hpageWidth)
    (by rw [hoff 109 (by decide) (by decide) (by decide) (by decide)]; exact hpage) hreadyi
    (by rw [hoff 141 (by decide) (by decide) (by decide) (by decide)]; exact haMaster)
    (by rw [hoff 142 (by decide) (by decide) (by decide) (by decide)]; exact hbMaster)
    (by rw [hoff 0 (by decide) (by decide) (by decide) (by decide)]; exact h0)
    (by rw [hoff 139 (by decide) (by decide) (by decide) (by decide)]; exact h139)
    (by rw [hoff 127 (by decide) (by decide) (by decide) (by decide)]; exact h127)
    (by rw [hoff 138 (by decide) (by decide) (by decide) (by decide)]; exact h138)
    (by rw [hoff 143 (by decide) (by decide) (by decide) (by decide)]; exact h143)
    (by rw [hoff 147 (by decide) (by decide) (by decide) (by decide)]; exact h147)
  let B := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
  let C := couplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
  let output := bandColumnWords A w boundary (12*band+1) n C++Si.R 132
  let S₁ : Stacks 154 A := {Si with R := Function.update Si.R 132 output}
  have he₂ := Exec.act (body := embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
    (.push (.rt 151) (fun _ => tick) .done) (mk v₁ S₁)
  let R' : Regs 154 A := Function.update S₁.R 151 (tick::Si.R 151)
  have he₂' : Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
      (.act (.push (.rt 151) (fun _ => tick) .done)) (mk v₁ S₁) 1 (mk v₁ {Si with R := R'}) := by
    simpa [S₁,R',Action.run,update_rt] using he₂
  refine ⟨v₁,R',m₁+1,hu₁,Nat.add_le_add_right hm₁ 1,Exec.seq he₁ he₂',by simp [R',S₁],by simp [R',S₁],?_⟩
  refine ⟨columns++[C],by simp [hlen],?_,?_⟩
  · apply ColumnFamilyAccurate.append _ _ _ _ _ _ _ _ hcolumns
    intro i hi
    simpa [columnWordRead,hlen,C,B,q,w,band,boundary,j] using herror i hi
  · intro k hk152 hk153
    by_cases hk132 : k = 132
    · subst k
      rw [show R' 132 = output by simp [R',S₁]]
      dsimp only [output]
      rw [hr 132 (by decide) (by decide)]
      simp [tableLoopRegs,bandTableWords_append,output,hlen,List.append_assoc,w,band,boundary]
    by_cases hk151 : k = 151
    · subst k
      rw [show R' 151 = tick::Si.R 151 by simp [R'],hr 151 (by decide) (by decide)]
      simp [tableLoopRegs,List.replicate_succ]
    rw [show R' k = Si.R k by simp [R',S₁,hk132,hk151],hr k hk152 hk153]
    simp [tableLoopRegs,hk132,hk151]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
