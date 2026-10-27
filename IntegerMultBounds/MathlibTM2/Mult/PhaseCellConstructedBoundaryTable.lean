module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBuildBoundaryTable
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareBoundaryPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryPageFrame

/-! Generate the folded coordinate page and its complete accurate Schur table from retained masters. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def constructedBoundaryTable (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 154 Q A U :=
  .seq prepareBoundaryPage (buildBoundaryTable hR hQ)

noncomputable def constructedBoundaryTableCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  prepareBoundaryPageCost s t (PhaseCellBand.width p u) a b+buildBoundaryTableCost p u l s t a b target

theorem constructedBoundaryTable_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 154 Q A U) (S : Stacks 154 A) (tail : List (Fin (A+4)))
    (h109 : S.R 109 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (hleft : ∀ r : Fin 148, S.L (tableFoldReg r) = [])
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
    let V := publicationGeometryWidth t (PhaseCellBand.width p u)
    let page := cstream A V ((bFoldOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
    ∃ v' m, ∃ columns : List (ZMod s → GaussianInt),
      let output := bandTableWords A w B W columns 0++S.R 132
      let S' : Stacks 154 A := {S with R := (Function.update (Function.update (Function.update (Function.update S.R
        115 (List.replicate V tick)) 116 (List.replicate B.card tick)) 109 page) 132 output)}
      v'.user = v.user ∧ m ≤ constructedBoundaryTableCost p u l s t a b target ∧
      Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
        (constructedBoundaryTable hR hQ) (mk v S) m (mk v' S') ∧ columns.length = B.card ∧
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
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let V := publicationGeometryWidth t band
  let page := cstream A V ((bFoldOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
  have hs : (S.R 121).length = s := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,groupHeaderValue] using
      hready.masters (121,97) (by simp [groupHeaderCopies])
  have ht : (S.R 122).length = t := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,groupHeaderValue] using
      hready.masters (122,98) (by simp [groupHeaderCopies])
  have hb : (S.R 124).length = band := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,groupHeaderValue,band] using
      hready.masters (124,100) (by simp [groupHeaderCopies])
  have h135 : S.R 135 = [] := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 135 (by simp)
  have h106 : S.R 106 = [] := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 106 (by decide) (by decide) (by decide)
  have h108 : S.R 108 = [] := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 108 (by decide) (by decide) (by decide)
  have hblank : ∀ k ∈ boundarySetupHeaders, S.R k = [] := by
    intro k hk
    simp only [boundarySetupHeaders,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 97 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 98 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 100 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 101 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 103 (by decide) (by decide) (by decide)
  have hlow : ∀ r : Fin 154, r.val < 77 → S.R r = [] := by
    intro r hr
    let i : Fin 144 := ⟨r.val,by omega⟩
    have hi93 : i ≠ 93 := by
      intro h
      have hh := congrArg Fin.val h
      change r.val = 93 at hh
      omega
    have hi110 : i ≠ 110 := by
      intro h
      have hh := congrArg Fin.val h
      change r.val = 110 at hh
      omega
    have hh := hready.blank i (by dsimp [i]; omega) hi93 hi110
    have he : tableReg (boundaryArithmeticReg (componentReg i)) = r := by
      have h109' : componentReg i ≠ 109 := by
        intro h; have hh := congrArg Fin.val h; change r.val = 109 at hh; omega
      have h115' : componentReg i ≠ 115 := by
        intro h; have hh := congrArg Fin.val h; change r.val = 115 at hh; omega
      have h116' : componentReg i ≠ 116 := by
        intro h; have hh := congrArg Fin.val h; change r.val = 116 at hh; omega
      apply Fin.ext
      change (boundaryArithmeticReg (componentReg i)).val = r.val
      simp only [boundaryArithmeticReg,h109',h115',h116',ite_false]
      rfl
    change S.R (tableReg (boundaryArithmeticReg (componentReg i))) = [] at hh
    rw [he] at hh
    exact hh
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := prepareBoundaryPage_exec
    (body := embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
    hst has hbs hband v S hs ht hb haMaster hbMaster h135 h115 h116 h109 h106 h108 hblank hlow hleft
  let S₁ : Stacks 154 A := {S with R := (Function.update (Function.update (Function.update S.R
    115 (List.replicate V tick)) 116 (List.replicate B.card tick)) 109 page)}
  have hready₁ : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u target 2) 2) l s t u band 0 0 tail
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S₁))) := by
    dsimp only [S₁]
    rw [tableArithmeticProject_page]
    exact hready
  obtain ⟨v₂,m₂,columns,hu₂,hm₂,he₂,hlen,hcolumns,hformat,hready₂,hstorage,herror⟩ := buildBoundaryTable_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad v₁ S₁ tail []
    (by simp [S₁,B,band]) (by simp [S₁,V,band]) (by simp [S₁,page,V,B,band]) hready₁
    (by simpa [S₁] using haMaster) (by simpa [S₁] using hbMaster) (by simpa [S₁] using h0)
    (by simpa [S₁] using h139) (by simpa [S₁] using h127) (by simpa [S₁] using h138)
    (by simpa [S₁] using h143) (by simpa [S₁] using h147) (by simpa [S₁] using h151)
    (by simpa [S₁] using h153) (by simpa [S₁] using h152)
  refine ⟨v₂,m₁+m₂,columns,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,?_,hlen,hcolumns,hformat,?_,hstorage,herror⟩
  · simpa [constructedBoundaryTable,S₁,page,V,B,band] using Exec.seq he₁ he₂
  · simpa [S₁,page,V,B,band] using hready₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
