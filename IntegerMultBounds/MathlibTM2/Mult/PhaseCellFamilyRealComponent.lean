module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyComputedBoundarySolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyBoundaryRecovered
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryReady

/-! A complete prepared real-component inverse: compute, solve, recover and retire owned lines while preserving the shared page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 263 Q A U}

noncomputable def familyRealComponent (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 263 Q A U :=
  .seq (familyComputedBoundarySolve recovery hR hQ)
    (.seq (retireCountedLine 121 160 132 231 232 233)
      (.seq (familyBoundaryRecovered recovery hR hQ) (retireCountedLine 192 160 224 231 232 233)))

noncomputable def familyRealComponentCost (A p u l s t a b target V : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  familyRealInteriorResidualCost A p l s t u (initialSchurTarget p u bits 2) 2 a b+
    familyGeneratedBoundaryRhsCost (2^15*p) q s t u (PhaseCellBand.width p u) a b+preparedResidualSolveCost q w N (12*PhaseCellBand.width p u+1)+
    retireCountedLineCost s w+sharedPageBoundaryAmbientCost N w s+
    familyRecoveryToleranceCost A p l s t u bits 2 a b+sharedPageRetireResidualCost s w+retireCountedLineCost N w

private theorem component_restore {A : ℕ} (S : Stacks 263 A)
    (input interior folded output : List (Fin (A+4))) :
    let S₁ : Stacks 263 A := {S with R := (Function.update (Function.update (Function.update S.R
      110 input) 132 (interior++S.R 132)) 224 (folded++S.R 224))}
    let S₂ : Stacks 263 A := {S₁ with R := Function.update S₁.R 132 (S.R 132)}
    let S₃ : Stacks 263 A := {S₂ with R := (Function.update (Function.update S₂.R 110 (S.R 110))
      132 (output++S₂.R 132))}
    {S₃ with R := Function.update S₃.R 224 (S.R 224)} =
      {S with R := Function.update S.R 132 (output++S.R 132)} := by
  dsimp only
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi110 : i = 110 <;> by_cases hi132 : i = 132 <;> by_cases hi224 : i = 224 <;>
    simp [hi110,hi132,hi224]

theorem familyRealComponent_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let bits := boundaryTableBits p (boundaryRecoveryTarget p target) 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    ∀ (columns : List (ZMod s → GaussianInt)),
    let AZ := factorRankIntegerMatrix B W columns
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    columns.length = B.card → ColumnFamilyFormat w columns →
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits)) (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
      (SchurDominance.run (realMatrix s t p u) (haloVertices s a b) (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    ∀ (F : ZMod s → GaussianInt), (∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS 263 Q A U) (S : Stacks 263 A) (tail coordinateTail pageTail familyTail : List (Fin (A+4))) (V : ℕ),
    let σ := boundaryFactorState (embStk sharedPageRecoveryReg (embStk familyBoundaryReg S))
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (chirpLine s F)++tail)
      (embStk familyCouplingSourceReg S) →
    CouplingPageCacheReady recovery (2^15*p) q w s t u band a b pageTail (embStk familyInverseLegacyReg S) →
    S.R 260 = weightKeyFamily (haloWeightKeyPages A w q (2^15*p) s t u band a b (haloLengthKeys s t band a b))++familyTail →
    (∀ i ∈ ([(256 : Fin 263),257,258,259,261,262] : List (Fin 263)), S.R i = []) →
    (S.R 141).length = a → (S.R 142).length = b →
    (∀ i : Fin 240, (embStk familyBoundaryReg S).L i = []) → (∀ i : Fin 64, S.R ⟨i.val,by omega⟩ = []) →
    BoundarySolveReady σ q w W B.card →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    s ≤ 2^V → (S.R 116).length = B.card → (S.R 115).length = V → (S.R 160).length = w →
    S.R 109 = cstream A V ((bFoldOrder s B).map (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++coordinateTail →
    (S.R 119).length = q →
    (∀ i ∈ ([127,138,143,106,139,206,223,184,220,221,225,217,201,208,211,215,231,232,233,234,235,236,237] : List (Fin 263)), S.R i = []) →
    S.R 116 = List.replicate B.card tick → (S.R 192).length = B.card → (S.R 121).length = s →
    ∀ (borrowed : List (Fin (A+4))),
    S.R 239 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])++borrowed →
    ∀ x : ZMod s → ℝ, Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
    ∃ v' n, ∃ Y : ZMod s → GaussianInt,
      let S' : Stacks 263 A := {S with R := Function.update S.R 132 (cstream A w (chirpLine s Y)++S.R 132)}
      v'.user = v.user ∧ n ≤ familyRealComponentCost A p u l s t a b target V ∧
      Exec body (familyRealComponent recovery hR hQ) (mk v S) n (mk v' S') ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => publishedCellRead q w (0 : ZMod s) (S'.R 132) i) x (1/(2 : ℝ)^target) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let band := PhaseCellBand.width p u
  let W := 12*band+1
  let solveTarget := boundaryRecoveryTarget p target
  let bits := boundaryTableBits p solveTarget 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  intro columns hlen hformat hstage htable F hF v S tail coordinateTail pageTail familyTail V hready hcache hfamily hfamilyFresh ha hb hleft hmul
    hsolve hbo hhf hdf hsV hN hV hw hcoordinates hmaster hclean hc hrows hs borrowed hadv x hx
  have hz : ∀ i ∈ ([127,138,143,106,139,206,223,184,220,221,225] : List (Fin 263)), S.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hclean _ (by simp)
  obtain ⟨v₁,n₁,D,C,solution,hu₁,hn₁,he₁,hsolLen,hfit,hready₁,hacc⟩ := familyComputedBoundarySolve_spec
    (body := body) (target := solveTarget) recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
    columns hlen hformat hstage htable F hF v S tail coordinateTail pageTail familyTail V hready hcache hfamily hfamilyFresh ha hb hleft hmul
    hsolve hbo hhf hdf hsV hN hV hw hcoordinates hmaster hz
  let input := cstream A w (chirpLine s C)++S.R 110
  let interior := cstream A w (chirpLine s D)
  let folded := cstream A w solution
  let S₁ : Stacks 263 A := {S with R := (Function.update (Function.update (Function.update S.R
    110 input) 132 (interior++S.R 132)) 224 (folded++S.R 224))}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := retireCountedLine_exec (body := body) 121 160 132 231 232 233
    (by decide) s w interior (S.R 132) (by simp [interior,chirpLine]) v₁ S₁
    (by simpa [S₁] using hs) (by simpa [S₁] using hw) (by rfl)
    (by simpa [S₁] using hclean 231 (by simp)) (by simpa [S₁] using hclean 232 (by simp))
    (by simpa [S₁] using hclean 233 (by simp))
  let S₂ : Stacks 263 A := {S₁ with R := Function.update S₁.R 132 (S.R 132)}
  have hproj₂ : embStk familyCouplingSourceReg S₂ = {embStk familyCouplingSourceReg S₁ with R :=
      (Function.update (embStk familyCouplingSourceReg S₁).R 132 (S.R 132))} :=
    embStk_updateR_inner familyCouplingSourceReg familyCouplingSourceReg_injective S₁ 132 _
  have hready₂ : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 input (embStk familyCouplingSourceReg S₂) := by
    rw [hproj₂]; exact hready₁.update_output _
  have hsource : S.R 110 = cstream A w (chirpLine s F)++tail := hready.source
  have hready₂' : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (chirpLine s C)++(cstream A w (chirpLine s F)++tail))
      (embStk familyCouplingSourceReg S₂) := by
    change LengthKeyReady _ _ _ _ _ _ _ _ _ _ (S₂.R 110) _ at hready₂
    simpa only [S₂,S₁,Function.update_of_ne (by decide : (110 : Fin 263) ≠ 132),
      Function.update_of_ne (by decide : (110 : Fin 263) ≠ 224),Function.update_self,input,hsource] using hready₂
  have hm₂ : ∀ i : Fin 64, S₂.R ⟨i.val,by omega⟩ = [] := by
    intro i
    have hn (k : Fin 263) (hk : 64 ≤ k.val) : (⟨i.val,by omega⟩ : Fin 263) ≠ k := by
      intro he
      have hh := congrArg (fun j : Fin 263 => j.val) he
      have hi := i.isLt
      change i.val = k.val at hh
      omega
    simpa only [S₂,S₁,Function.update_of_ne (hn 132 (by decide)),
      Function.update_of_ne (hn 224 (by decide)),Function.update_of_ne (hn 110 (by decide))] using hmul i
  have hz₂ : ∀ i ∈ ([184,217,223,201,208,211,215,220,231,232,233,234,235,236,237,127,138,143] : List (Fin 263)), S₂.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [S₂,S₁] using hclean _ (by simp)
  have hcache₂ : CouplingPageCacheReady recovery (2^15*p) q w s t u band a b pageTail (embStk familyInverseLegacyReg S₂) := by
    apply hcache.of_frame
    intro i
    have hi := couplingCachePort_ge recovery i
    have hne (k : Fin 263) (hk : k.val < 248) : familyInverseLegacyReg (couplingCachePort recovery i) ≠ k := by
      intro h; have hv := congrArg Fin.val h; dsimp [familyInverseLegacyReg] at hv; omega
    simp [S₂,S₁,embStk,hne 110 (by decide),hne 132 (by decide),hne 224 (by decide)]
  obtain ⟨v₃,n₃,E,hu₃,hn₃,he₃,herror⟩ := familyBoundaryRecovered_spec (body := body) (target := target)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
    F solution x hsolLen hfit (fun i hi => (hacc x hx i hi).1) hF hx v₂ S₂
    (cstream A w (chirpLine s C)) tail (S.R 224) borrowed pageTail familyTail
    (by change (cstream A w (chirpLine s C)).length = s*w; simp [chirpLine]) hready₂' hcache₂
    (by simpa [S₂,S₁] using hfamily) (by
      intro i hi
      have hi110 : i ≠ 110 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hi132 : i ≠ 132 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hi224 : i ≠ 224 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [S₂,S₁,hi110,hi132,hi224] using hfamilyFresh i hi)
    (by simpa [S₂,S₁] using ha) (by simpa [S₂,S₁] using hb) hleft hm₂
    (by simpa [S₂,S₁] using hc) (by simpa [S₂,S₁] using hrows)
    (by simpa [S₂,S₁] using hw) (by simpa [S₂,S₁] using hs)
    (by simpa [S₂,S₁] using hadv) (by change S₂.R 224 = cstream A w solution++S.R 224; simp [S₂,S₁,folded]) hz₂
  let G := boundarySolutionField B solution
  let Y := fun i => realPartWord (publicationField t band a b E G i)
  let output := cstream A w (chirpLine s Y)
  let S₃ : Stacks 263 A := {S₂ with R := (Function.update (Function.update S₂.R 110 (S.R 110))
    132 (output++S₂.R 132))}
  have he₃' : Exec body (familyBoundaryRecovered recovery hR hQ) (mk v₂ S₂) n₃ (mk v₃ S₃) := by
    simpa only [S₃,hsource] using he₃
  have hsolLen' : solution.length = B.card := hsolLen
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := retireCountedLine_exec (body := body) 192 160 224 231 232 233
    (by decide) B.card w folded (S.R 224) (by simp [folded,hsolLen']) v₃ S₃
    (by simpa [S₃,S₂,S₁] using hrows) (by simpa [S₃,S₂,S₁] using hw) (by simp [S₃,S₂,S₁])
    (by simpa [S₃,S₂,S₁] using hclean 231 (by simp))
    (by simpa [S₃,S₂,S₁] using hclean 232 (by simp)) (by simpa [S₃,S₂,S₁] using hclean 233 (by simp))
  refine ⟨v₄,n₁+(n₂+(n₃+n₄)),Y,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃' he₄))).cast rfl ?_,?_⟩
  · have h₁ : n₁ ≤ familyRealInteriorResidualCost A p l s t u (initialSchurTarget p u bits 2) 2 a b+
      familyGeneratedBoundaryRhsCost (2^15*p) q s t u (PhaseCellBand.width p u) a b+preparedResidualSolveCost q w B.card W := hn₁
    have h₂ : n₂ ≤ retireCountedLineCost s w := hn₂
    have h₃ : n₃ ≤ sharedPageBoundaryAmbientCost B.card w s+familyRecoveryToleranceCost A p l s t u bits 2 a b+
      sharedPageRetireResidualCost s w := hn₃
    have h₄ : n₄ ≤ retireCountedLineCost B.card w := hn₄
    dsimp only [familyRealComponentCost]
    change n₁+(n₂+(n₃+n₄)) ≤ familyRealInteriorResidualCost A p l s t u (initialSchurTarget p u bits 2) 2 a b+
      familyGeneratedBoundaryRhsCost (2^15*p) q s t u (PhaseCellBand.width p u) a b+preparedResidualSolveCost q w B.card W+retireCountedLineCost s w+
      sharedPageBoundaryAmbientCost B.card w s+familyRecoveryToleranceCost A p l s t u bits 2 a b+
      sharedPageRetireResidualCost s w+retireCountedLineCost B.card w
    omega
  · apply congrArg (mk v₄)
    exact component_restore S input interior folded output
  · exact herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
