module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableColumnsLoop

/-! Generate the boundary-table loop controls, execute every column and restore all scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def buildBoundaryTable (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 154 Q A U :=
  .seq (ucopy 116 152 135) (.seq (tableColumnsLoop hR hQ) (clearWords [151,152]))

noncomputable def buildBoundaryTableCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  (4*N+4)+(tableColumnsLoopCost p u l s t a b target+(4*N+5))

theorem buildBoundaryTable_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
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
    (h151 : S.R 151 = []) (h153 : S.R 153 = [])
    (h152 : S.R 152 = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let W := 12*PhaseCellBand.width p u+1
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let w := executionWidth p l (initialSchurTarget p u target 2) 2
    ∃ v' m, ∃ columns : List (ZMod s → GaussianInt),
      let output := bandTableWords A w B W columns 0++S.R 132
      let S' : Stacks 154 A := {S with R := Function.update S.R 132 output}
      v'.user = v.user ∧ m ≤ buildBoundaryTableCost p u l s t a b target ∧
      Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
        (buildBoundaryTable hR hQ) (mk v S) m (mk v' S') ∧ columns.length = B.card ∧
      ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
          (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 (1/(2 : ℝ)^target) columns ∧ ColumnFamilyFormat w columns ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
        q l s t u (PhaseCellBand.width p u) 0 0 tail
        (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S'))) ∧
      (bandTableWords A w B W columns 0).length ≤ B.card*(2*W+1)*w ∧
      (∀ i ∈ B, ∀ j ∈ B,
        |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 i j| ≤ 1/(2 : ℝ)^target) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let W := 12*PhaseCellBand.width p u+1
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  have h135 : S.R 135 = [] := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 135 (by simp)
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec
    (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
    (a := 116) (b := 152) (t := 135) (by decide) (by decide) (by decide) v S h135
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 152 (List.replicate B.card tick)}
  have he₁' : Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
      (ucopy 116 152 135) (mk v S) (4*B.card+4) (mk v₁ S₁) := by
    simpa [S₁,hrows,h152,B] using he₁
  have hready₁ : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      q l s t u (PhaseCellBand.width p u) 0 0 tail
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S₁))) := by
    dsimp only [S₁]
    rw [tableProject_updateR_outer S 152 _ (by decide)]
    exact hready
  obtain ⟨v₂,m₂,columns,hu₂,hm₂,he₂,hlen,hcolumns,hformat,hready₂⟩ := tableColumnsLoop_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad v₁ S₁ tail pageTail
    (by simpa [S₁] using hrows) (by simpa [S₁] using hpageWidth) (by simpa [S₁] using hpage) hready₁
    (by simpa [S₁] using haMaster) (by simpa [S₁] using hbMaster) (by simpa [S₁] using h0)
    (by simpa [S₁] using h139) (by simpa [S₁] using h127) (by simpa [S₁] using h138)
    (by simpa [S₁] using h143) (by simpa [S₁] using h147) (by simpa [S₁] using h151)
    (by simpa [S₁] using h153) (by simp [S₁,B])
  let output := bandTableWords A w B W columns 0++S.R 132
  let S₂ : Stacks 154 A := {S₁ with R := (Function.update (Function.update S₁.R 132 output)
    151 (List.replicate B.card tick))}
  have he₂' : Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
      (tableColumnsLoop hR hQ) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,output,w,B,W] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec
    (body := embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
    [(151 : Fin 154),152] (by decide) v₂ S₂
  have hsum : ([(151 : Fin 154),152].map (fun k => (S₂.R k).length)).sum = 2*B.card := by simp [S₂,S₁]; omega
  let Sfinal : Stacks 154 A := {S with R := Function.update S.R 132 output}
  have he₃' : Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
      (clearWords [151,152]) (mk v₂ S₂) (4*B.card+5) (mk v₃ Sfinal) := by
    convert he₃ using 1
    · rw [hsum]; simp only [List.length_cons,List.length_nil]; omega
    · apply congrArg (mk v₃)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hk132 : k = 132 <;> by_cases hk151 : k = 151 <;> by_cases hk152 : k = 152 <;>
        simp [Sfinal,S₂,S₁,hk132,hk151,hk152,h151,h152]
  refine ⟨v₃,(4*B.card+4)+(m₂+(4*B.card+5)),columns,hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add_left (Nat.add_le_add_right hm₂ _) _,Exec.seq he₁' (Exec.seq he₂' he₃'),hlen,hcolumns,hformat,?_,?_,?_⟩
  · apply tableLoopReady_of_frame (S' := Sfinal) hready rfl
    intro k hk hk132
    simp [Sfinal,hk132]
  · simpa [hlen,w,B,W] using bandTableWords_storage A w B W columns 0
  · apply computedBoundaryTable_band_error A q w B W columns hlen _ _ (by positivity)
    · intro i hi j hj hne
      exact halo_schur_foldBRel hst p u a b hi hj hne
    · exact hcolumns

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
