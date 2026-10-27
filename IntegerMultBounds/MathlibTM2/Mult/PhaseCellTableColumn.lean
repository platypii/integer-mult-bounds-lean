module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedIndexedColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedColumnCollection
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

noncomputable def tableColumn (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 154 Q A U :=
  .seq (retainedIndexedColumn hR hQ) retainedColumnCollection

noncomputable def tableColumnCost (p u l s t a b target n x : ℕ) [NeZero s] : ℕ :=
  let band := PhaseCellBand.width p u
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  retainedIndexedColumnCost p u l s t a b target n x+
    retainedColumnCollectionCost (haloBoundary s t band a b) q (publicationGeometryWidth t band) band n

theorem tableColumn_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (n : ℕ) (hn : n < (haloBoundary s t (PhaseCellBand.width p u) a b).card)
    (v : HS 154 Q A U) (S : Stacks 154 A) (tail : List (Fin (A+4)))
    (pageTail : List (Fin (A+4)))
    (hrows : (S.R 116).length = (haloBoundary s t (PhaseCellBand.width p u) a b).card)
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
      let output := cstream A w ((foldedBandRows (haloBoundary s t band a b) (12*band+1) n).reverse.map C)++S.R 132
      let S' : Stacks 154 A := {S with R := Function.update S.R 132 output}
      v'.user = v.user ∧ m ≤ tableColumnCost p u l s t a b target n j.val ∧
      Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))) (tableColumn hR hQ) (mk v S) m (mk v' S') ∧
      (∀ i, (C i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2)
        (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ haloBoundary s t band a b,
        |(value q (decodeWord (csyms A w (C i)))).re-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^target) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
        q l s t u band 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S'))) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  let V := publicationGeometryWidth t band
  let boundary := haloBoundary s t band a b
  let j := bFoldAt s boundary n
  have hwq : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  obtain ⟨v₁,m₁,D,hu₁,hm₁,he₁,hreal,hnorm,herror,hready₁⟩ := retainedIndexedColumn_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad n hn v S tail pageTail
    hindex hpageWidth hpage hready haMaster hbMaster h0 h139 h127 h138 h143 h147
  let B := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
  let C := guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 110 (cstream A w (chirpLine s C)++tail)}
  have hq : (S₁.R 119).length = q := by
    simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,groupHeaderValue,q] using
      hready₁.masters (119,112) (by simp [groupHeaderCopies])
  have hsMaster : (S₁.R 121).length = s := by
    simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,groupHeaderValue] using
      hready₁.masters (121,97) (by simp [groupHeaderCopies])
  have hbandMaster : (S₁.R 124).length = band := by
    simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,groupHeaderValue,band] using
      hready₁.masters (124,100) (by simp [groupHeaderCopies])
  have hfresh : ∀ k ∈ [(94 : Fin 154),106,131,134,135,136,137,138,139,140], S₁.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready₁.blank 94 (by decide) (by decide) (by decide)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready₁.blank 106 (by decide) (by decide) (by decide)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready₁.fresh 131 (by simp)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready₁.fresh 134 (by simp)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready₁.fresh 135 (by simp)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready₁.fresh 136 (by simp)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready₁.fresh 137 (by simp)
    · simpa [S₁] using h138
    · simpa [S₁] using h139
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready₁.fresh 140 (by simp)
  have hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S₁.R r = [] := by
    intro r hr1 hr7
    have hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by omega
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready₁.blank 1 (by decide) (by decide) (by decide)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready₁.blank 2 (by decide) (by decide) (by decide)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready₁.blank 3 (by decide) (by decide) (by decide)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready₁.blank 4 (by decide) (by decide) (by decide)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready₁.blank 5 (by decide) (by decide) (by decide)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready₁.blank 6 (by decide) (by decide) (by decide)
  have hsfit : s ≤ 2^V := by
    have hh := publicationGeometryWidth_fits t band
    nlinarith only [hh,hst]
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := retainedColumnCollection_exec
    (body := embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))
    boundary q V band n (by omega) hsfit hn C pageTail tail v₁ S₁
    (by simpa [S₁] using hindex) (by simpa [S₁] using hpageWidth) hbandMaster
    (by simpa [S₁] using hrows) (by simpa [S₁] using hpage) hq hsMaster
    (by simp [S₁,hwq]) (by simpa [S₁] using h0) hfresh hblank
  let output := cstream A w ((foldedBandRows boundary (12*band+1) n).reverse.map C)++S.R 132
  let Sfinal : Stacks 154 A := {S with R := Function.update S.R 132 output}
  have hsrc : S.R 110 = tail := by
    simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.source
  have he₂' : Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
      retainedColumnCollection (mk v₁ S₁) m₂ (mk v₂ Sfinal) := by
    convert he₂ using 1
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk110 : k = 110 <;> by_cases hk132 : k = 132 <;>
      simp [Sfinal,S₁,output,hwq,hk110,hk132,hsrc]
  refine ⟨v₂,m₁+m₂,D,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂',hreal,hnorm,?_,?_⟩
  · intro i hi
    have hh := herror i hi
    change |publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s C)++tail) i-_| ≤ _ at hh
    simp only [publishedCellRead,ZMod.val_zero,Nat.sub_zero] at hh
    rw [cstream_word w (chirpLine s C) tail i.val (by simpa using i.val_lt)] at hh
    simpa [chirpLine,C,B,q,w,band,boundary,j] using hh
  · change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _ (embStk componentReg (embStk boundaryArithmeticReg
      (embStk tableReg {S with R := Function.update S.R (tableReg (boundaryArithmeticReg (componentReg 132))) output})))
    rw [tableProject_updateR_inner,boundaryArithmeticProject_updateR_inner]
    convert hready.update_output output using 1
    exact componentProject_updateR_inner (embStk boundaryArithmeticReg (embStk tableReg S)) (132 : Fin 144) output

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
