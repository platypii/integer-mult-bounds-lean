module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedBoundaryRealUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryPublish

/-! Execute the accurate retained boundary solve through ambient publication. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def retainedBoundaryPublished (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (retainedBoundaryRealUnfold hR hQ) preparedBoundaryPublish

theorem retainedBoundaryPublished_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (F : ZMod s → GaussianInt) (hF : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (F i)‖ ≤ (2 : ℝ)^2)
    (v : HS 224 Q A U) (S : Stacks 224 A) (tail : List (Fin (A+4)))
    (h109 : S.R 109 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (hleft : ∀ i : Fin 224, S.L i = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0 (cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p target 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (chirpLine s F)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = []) 
    (h151 : S.R 151 = []) (h153 : S.R 153 = [])
    (h152 : S.R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p target 2 B.card
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let V := publicationGeometryWidth t band
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∃ v₀ S₀ n₀ v₁ S₁ n₁ v' S' n, ∃ D : ZMod s → GaussianInt,
    ∃ columns : List (ZMod s → GaussianInt), ∃ solution : List GaussianInt,
      let C := couplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (F i))
      let G := boundarySolutionField B solution
      v'.user = v.user ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (retainedBoundarySolve hR hQ)
        (mk v S) n₀ (mk v₀ S₀) ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (retainedBoundaryRealUnfold hR hQ)
        (mk v S) n₁ (mk v₁ S₁) ∧
      n ≤ retainedBoundarySolveCost p u l s t a b target+
        (2*(([189,191,198,204] : List (Fin 224)).map fun i => (S₀.R i).length).sum+9)+
        generatedBoundaryUnfoldCost B.card w+(B.card*(12*w+9)+12)+
        (2*(([189,191,198,206] : List (Fin 224)).map fun i => (S₁.R i).length).sum+9)+
        generatedBoundaryUnfoldCost B.card V+(4*(B.card*V)+4)+
        generateBoundaryAdvancesCost B.card V w s+93*s*w+45 ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (retainedBoundaryPublished hR hQ)
        (mk v S) n (mk v' S') ∧
      solution.length = B.card ∧
      S'.R 132 = cstream A w (chirpLine s G)++
        (bandTableWords A w B W columns 0++cstream A w (chirpLine s D)++S.R 132) ∧
      S'.R 110 = cstream A w (chirpLine s C)++S.R 110 ∧
      S'.R 109 = [] ∧ S'.R 204 = [] ∧ S'.R 206 = [] ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ x : ZMod s → ℝ,
      SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
      (∀ i ∈ B, |publishedCellRead q w (0 : ZMod s) (S'.R 132) i-x i| ≤ 3/(2 : ℝ)^target) ∧
      (∀ i, (G i).im = 0) ∧
      (∀ i, ‖value q (G i)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let band := PhaseCellBand.width p u
  let V := publicationGeometryWidth t band
  let bits := boundaryTableBits p target 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  obtain ⟨v₀,S₀,n₀,v₁,S₁,n₁,D,columns,solution,hu₁,hn₀,he₀,hn₁,he₁,hlen,hsolLen,hsrc,h217,
    h110,h132,hinp,hout,hL,hpub,hcoords,hacc⟩ :=
    retainedBoundaryRealUnfold_spec (body := body) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
      hband has hbs hpad F hF v S tail h109 h115 h116 hleft hready haMaster hbMaster
      h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
  let G := boundarySolutionField B solution
  have hw : 1 ≤ w := by dsimp [w,executionWidth]; omega
  have hsV : s ≤ 2^V := by
    have hh := publicationGeometryWidth_fits t band
    change 8*(t+1)^2+2*band+8 < 2^V at hh
    nlinarith only [hh,hst]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := preparedBoundaryPublish_exec
    (body := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
      (embTab componentReg (embTab groupReg body))))) (by omega) s B V w hw hsV G
    (fun i hi => boundarySolutionField_off B solution i hi) [] v₁ S₁
    hpub.left hpub.mul hpub.ambient hpub.width hpub.geometry hpub.count hcoords
    (by simpa only [List.append_nil] using hsrc) hpub.scratch
  let S₂base : Stacks 224 A := {S₁ with R := fun i => if i ∈ ([189,191,198] : List (Fin 224)) then [] else S₁.R i}
  let S₂ : Stacks 224 A := {S₂base with R := (Function.update (Function.update (Function.update (Function.update S₂base.R
    109 []) 206 []) 204 []) 132 (cstream A w (chirpLine s G)++S₁.R 132))}
  have hn : n₁+n₂ ≤ _ := Nat.add_le_add hn₁ hn₂
  refine ⟨v₀,S₀,n₀,v₁,S₁,n₁,v₂,S₂,n₁+n₂,D,columns,solution,hu₂.trans hu₁,he₀,he₁,?_,
    Exec.seq he₁ he₂,hsolLen,?_,?_,?_,?_,?_,hinp,hout,hL,?_⟩
  · simpa only [Nat.add_assoc] using hn
  · simp [S₂,S₂base,h132,List.append_assoc,w,bits,B,G]
  · simpa [S₂,S₂base] using h110
  · simp [S₂]
  · simp [S₂]
  · simp [S₂]
  · intro x hx
    obtain ⟨herror,hmag,hfit⟩ := hacc x hx
    refine ⟨?_,fun i => boundarySolutionField_im B solution i,hmag⟩
    intro i hi
    have hread := publishedCellRead_encodedField (q := q) (w := w) (by omega : 4 ≤ A) hw
      G (S₁.R 132) hfit i
    change |publishedCellRead q w (0 : ZMod s) (S₂.R 132) i-x i| ≤ _
    rw [show S₂.R 132 = cstream A w (chirpLine s G)++S₁.R 132 by simp [S₂]]
    rw [hread]
    exact herror i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
