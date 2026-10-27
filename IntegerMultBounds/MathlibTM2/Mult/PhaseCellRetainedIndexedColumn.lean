module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIndexedSchurColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidentCoordinate
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoordinateReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryWorkspace

/-! Generate a Schur column while the prepared folded page remains resident. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def retainedIndexedColumn (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 154 Q A U :=
  .seq (ucopy 151 0 135) (embProg tableReg id (indexedSchurColumn hR hQ))

def retainedIndexedColumnCost (p u l s t a b target n x : ℕ) : ℕ :=
  (4*n+4)+indexedSchurColumnCost p u l s t a b target n x

theorem retainedIndexedColumn_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (n : ℕ) (hn : n < (haloBoundary s t (PhaseCellBand.width p u) a b).card)
    (v : HS 154 Q A U) (S : Stacks 154 A) (tail : List (Fin (A+4)))
    (pageTail : List (Fin (A+4)))
    (hindex : (S.R 151).length = n)
    (hpageWidth : (S.R 115).length = publicationGeometryWidth t (PhaseCellBand.width p u))
    (hpage : S.R 109 = cstream A (publicationGeometryWidth t (PhaseCellBand.width p u))
      ((bFoldOrder s (haloBoundary s t (PhaseCellBand.width p u) a b)).map
        (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u target 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S))))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = []) :
    let j := bFoldAt s (haloBoundary s t (PhaseCellBand.width p u) a b) n
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let w := executionWidth p l (initialSchurTarget p u target 2) 2
    let band := PhaseCellBand.width p u
    let B := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
    ∃ v' m, ∃ D : ZMod s → GaussianInt,
      let C := guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
      let output := cstream A w (chirpLine s C)++tail
      let S' : Stacks 154 A := {S with R := Function.update S.R 110 output}
      v'.user = v.user ∧ m ≤ retainedIndexedColumnCost p u l s t a b target n j.val ∧
      Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))) (retainedIndexedColumn hR hQ) (mk v S) m (mk v' S') ∧
      (∀ i, (C i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2)
        (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ haloBoundary s t band a b,
        |publishedCellRead q w (0 : ZMod s) (S'.R 110) i-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^target) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
        q l s t u band 0 0 output (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S'))) := by
  dsimp only
  have h135 : S.R 135 = [] := by
    have hh := hready.fresh 135 (by simp)
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hh
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec
    (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
    (a := 151) (b := 0) (t := 135) (by decide) (by decide) (by decide) v S h135
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 0 (List.replicate n tick)}
  have he₁' : Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
      (ucopy 151 0 135) (mk v S) (4*n+4) (mk v₁ S₁) := by simpa [S₁,hindex,h0] using he₁
  have hreset : {(embStk tableReg S₁) with R := Function.update (embStk tableReg S₁).R 0 []} =
      embStk tableReg S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = 0 <;> simp [embStk,Function.comp_def,tableReg,S₁,hk,h0]
  obtain ⟨v₂,m₂,D,hu₂,hm₂,he₂,hreal,hnorm,herror,hready₂⟩ := indexedSchurColumn_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad n hn
    (embDn tableReg v₁) (embStk tableReg S₁) tail pageTail
    (by simp [embStk,tableReg,S₁])
    (by simpa [embStk,tableReg,S₁] using hpageWidth)
    (by simpa [embStk,tableReg,S₁] using hpage)
    (by rw [hreset]; exact hready)
    (by simpa [embStk,tableReg,S₁] using haMaster)
    (by simpa [embStk,tableReg,S₁] using hbMaster)
    (by simpa [embStk,tableReg,S₁] using h139)
    (by simpa [embStk,tableReg,S₁] using h127)
    (by simpa [embStk,tableReg,S₁] using h138)
    (by simpa [embStk,tableReg,S₁] using h143)
    (by simpa [embStk,tableReg,S₁] using h147)
  obtain ⟨v₃,hu₃,he₃⟩ := tableExec_twoPorts (indexedSchurColumn hR hQ) v₁ S₁ v₂ m₂ 0 110 _ _ hu₂ he₂
  let j := bFoldAt s (haloBoundary s t (PhaseCellBand.width p u) a b) n
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  let band := PhaseCellBand.width p u
  let B := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
  let C := guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
  let output := cstream A w (chirpLine s C)++tail
  let Sfinal : Stacks 154 A := {S with R := Function.update S.R 110 output}
  have he₃' : Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
      (embProg tableReg id (indexedSchurColumn hR hQ)) (mk v₁ S₁) m₂ (mk v₃ Sfinal) := by
    convert he₃ using 1
    apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk0 : k = 0 <;> by_cases hk110 : k = 110 <;>
      simp [Sfinal,S₁,tableReg,hk0,hk110,h0,output,C,B,q,w,band,j]
  refine ⟨v₃,(4*n+4)+m₂,D,hu₃.trans hu₁,Nat.add_le_add_left hm₂ _,Exec.seq he₁' he₃',hreal,hnorm,?_,?_⟩
  · simpa [embStk,tableReg,S₁,Sfinal,output,C,B,q,w,band,j] using herror
  · have hproj : embStk tableReg Sfinal =
        {(embStk tableReg S₁) with R := (Function.update (Function.update (embStk tableReg S₁).R 0 []) 110 output)} := by
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hk0 : k = 0
      · subst k; simp [embStk,tableReg,Sfinal,S₁,h0]
      by_cases hk110 : k = 110
      · subst k; simp [embStk,tableReg,Sfinal,S₁]
      have hne : tableReg k ≠ 110 := by
        change tableReg k ≠ tableReg 110
        exact fun h => hk110 (tableReg_injective h)
      simp [embStk,Function.comp_def,Sfinal,S₁,hk0,hk110,h0,hne,tableReg]
      change Function.update S.R 110 output (tableReg k) = S.R (tableReg k)
      rw [Function.update_of_ne hne]
    rw [hproj]
    exact hready₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
