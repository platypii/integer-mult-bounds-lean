module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedComplexBatchStep

/-! Execute a complex input through both real solves on one retained factor page, restoring every borrowed tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 256 Q A U}

theorem cachedComplexBatchStep_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
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
    ∀ (v : HS 256 Q A U) (S : Stacks 256 A) (tail coordinateTail pageTail : List (Fin (A+4))) (V : ℕ),
    let σ := boundaryFactorState (embStk sharedPageRecoveryReg (embStk couplingBoundaryReg S))
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (chirpLine s F)++tail)
      (embStk couplingSourceReg S) →
    CouplingPageCacheReady recovery (2^15*p) q w s t u band a b pageTail S →
    (S.R 141).length = a → (S.R 142).length = b →
    (∀ i : Fin 240, (embStk couplingBoundaryReg S).L i = []) → (∀ i : Fin 64, S.R ⟨i.val,by omega⟩ = []) →
    BoundarySolveReady σ q w W B.card →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    s ≤ 2^V → (S.R 116).length = B.card → (S.R 115).length = V → (S.R 160).length = w →
    S.R 109 = cstream A V ((bFoldOrder s B).map (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++coordinateTail →
    (S.R 119).length = q →
    (∀ i ∈ ([127,138,143,106,139,206,223,184,220,221,225,217,201,208,211,215,231,232,233,234,235,236,237,94,131,134,135,136,140,147] : List (Fin 256)), S.R i = []) →
    S.R 116 = List.replicate B.card tick → (S.R 192).length = B.card → (S.R 121).length = s →
    ∀ (borrowed : List (Fin (A+4))),
    S.R 239 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])++borrowed →
    (S.R 243).length = s*w → S.R 244 = [] →
    ∀ (x y : ZMod s → ℝ),
    Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
    Solves (realMatrix s t p u) (haloVertices s a b) y (fun i => (value q (F i)).im) →
    ∃ v' n, ∃ Z : ZMod s → GaussianInt,
      let input := cstream A w (chirpLine s F)
      let output := cstream A w (chirpLine s Z)
      let S' : Stacks 256 A := {S with R := (Function.update (Function.update (Function.update S.R
        110 tail) 241 (input.reverse++S.R 241)) 242 (output.reverse++S.R 242))}
      v'.user = v.user ∧ n ≤ originalComponentInputsCost q s+placedCachedBoundaryPairCost p u l s t a b target V+(8*(s*w)+8) ∧
      Exec body (cachedComplexBatchStep recovery hR hQ) (mk v S) n (mk v' S') ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b) (pairedCellRead q w (output++S.R 132))
        (fun i => (⟨x i,y i⟩ : ℂ)) (1/(2 : ℝ)^target) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  intro columns hlen hformat hstage htable F hF v S tail coordinateTail pageTail V hready hcache ha hb hleft hmul
    hsolve hbo hhf hdf hsV hN hV hw hcoordinates hmaster hclean hc hrows hs borrowed hadv
    hclock htmp x y hx hy
  obtain ⟨v₁,n,Z,hu₁,hn,he,herror⟩ := placedCachedComplexComponent_spec
    (body := body) recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
    hband has hbs hpad columns hlen hformat hstage htable F hF v
    S tail coordinateTail pageTail V hready hcache ha hb hleft hmul
    hsolve hbo hhf hdf hsV hN hV hw hcoordinates hmaster hclean hc hrows hs borrowed hadv x y hx hy
  let input := cstream A w (chirpLine s F)
  let output := cstream A w (chirpLine s Z)
  have hinputLen : input.length = s*w := by simp [input,chirpLine]
  have houtputLen : output.length = input.length := by simp [output,input,chirpLine]
  obtain ⟨v₂,hu₂,he₂⟩ := cachedComplexBatchStep_of_exec (body := body) recovery hR hQ v S v₁ n
    input output tail hready.source (hclock.trans hinputLen.symm) houtputLen htmp hu₁ he
  refine ⟨v₂,n+(8*(s*w)+8),Z,hu₂, Nat.add_le_add_right hn _,?_,herror⟩
  simpa only [hinputLen] using he₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
